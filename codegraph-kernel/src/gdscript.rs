//! GDScript extraction — Godot 4.x GDScript walker.
//!
//! Mirrors the TS-side GDScript paths: class_name/extends inheritance,
//! function/static_function definitions, var/const declarations, signal
//! definitions, enum definitions, lambda nodes, call expressions, and
//! cross-file references. Files with parse errors defer to wasm.
//!
//! GDScript node types (tree-sitter-gdscript 6.1.0):
//!   - source (root)
//!   - class_name_statement  (class_name Foo)
//!   - class_definition      (class Foo extends Bar)
//!   - function_definition   (func foo():)
//!   - static_function_definition
//!   - variable_statement    (var x = 1, with optional export/onready)
//!   - const_statement       (const FOO = 1)
//!   - signal_statement      (signal my_signal)
//!   - enum_definition       (enum Foo { A, B })
//!   - lambda
//!   - call                  (foo())
//!   - extends_statement     (extends Bar / extends "path")
//!   - comment               (# line comment / ## doc comment)

use crate::buffers::{
    build_meta, edge_kind_index, node_kind_index, Arena, BoolFlags, EdgeRow, EmitOut, NodeRow,
    RefRow, StrRef, Tables, FLAG_IS_EXPORTED, FUNCTION_REF_CODE, NONE, NONE_STR,
};
use crate::docstring::preceding_docstring;
use crate::ids;
use crate::textutil as util;
use std::collections::{HashMap, HashSet};
use tree_sitter::{Node, Parser};

const MAX_VALUE_REF_NODES: usize = 20_000;

struct Scope {
    row: u32,
    kind: &'static str,
    name: String,
}

#[derive(Default)]
struct Extra {
    docstring: Option<String>,
    signature: Option<String>,
    is_exported: Option<bool>,
    return_type: Option<String>,
    qualified_name: Option<String>,
}

struct ValueScope<'t> {
    row: u32,
    node: Node<'t>,
    name: String,
}

struct Cand {
    from: u32,
    name: String,
    line: u32,
    column_byte: usize,
    row: usize,
}

struct NodeMeta {
    kind: &'static str,
    name: String,
}

pub struct Walker<'t> {
    src: &'t str,
    file_path: &'t str,
    line_starts: Vec<usize>,
    arena: Arena,
    tables: Tables,
    stack: Vec<Scope>,
    nodes_meta: Vec<NodeMeta>,
    node_ids: Vec<String>,
    defined_fn_names: HashSet<String>,
    imported_names: HashSet<String>,
    fn_ref_cands: Vec<Cand>,
    fs_values: HashMap<String, u32>,
    fs_value_counts: HashMap<String, u32>,
    value_scopes: Vec<ValueScope<'t>>,
}

pub fn extract(file_path: &str, source: &str) -> Result<EmitOut, String> {
    let grammar = crate::langs::grammar_for("gdscript").ok_or("no gdscript grammar")?;
    let t0 = std::time::Instant::now();
    let mut parser = Parser::new();
    parser
        .set_language(&grammar)
        .map_err(|e| format!("set_language(gdscript) failed: {e}"))?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| "parser returned null tree".to_string())?;
    if tree.root_node().has_error() {
        return Err("defer: parse tree contains errors — wasm recovery is canonical".to_string());
    }

    let mut w = Walker {
        src: source,
        file_path,
        line_starts: util::line_starts(source),
        arena: Arena::default(),
        tables: Tables::default(),
        stack: Vec::new(),
        nodes_meta: Vec::new(),
        node_ids: Vec::new(),
        defined_fn_names: HashSet::new(),
        imported_names: HashSet::new(),
        fn_ref_cands: Vec::new(),
        fs_values: HashMap::new(),
        fs_value_counts: HashMap::new(),
        value_scopes: Vec::new(),
    };

    let line_count = source.bytes().filter(|b| *b == b'\n').count() as u32 + 1;
    let base_name = file_path.rsplit(['/', '\\']).next().unwrap_or(file_path);
    let file_id = w.arena.put(&ids::file_node_id(file_path));
    let name_ref = w.arena.put(base_name);
    let qn_ref = w.arena.put(file_path);
    w.tables.push_node(&NodeRow {
        kind: node_kind_index("file").unwrap(),
        visibility: 0,
        flags: BoolFlags::default(),
        start_line: 1,
        end_line: line_count,
        start_column: 0,
        end_column: 0,
        name: name_ref,
        qualified_name: qn_ref,
        id: file_id,
        docstring: NONE_STR,
        signature: NONE_STR,
        decorators: NONE_STR,
        type_parameters: NONE_STR,
        return_type: NONE_STR,
        extra_json: NONE_STR,
    });
    w.nodes_meta.push(NodeMeta { kind: "file", name: base_name.to_string() });
    w.node_ids.push(ids::file_node_id(file_path));
    w.stack.push(Scope { row: 0, kind: "file", name: base_name.to_string() });

    w.visit_node(tree.root_node());
    w.flush_fn_ref_candidates();
    w.flush_value_refs(tree.root_node());
    w.stack.pop();

    let duration_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let meta = build_meta(&w.tables, w.arena.len(), NONE_STR, duration_ms);
    Ok(EmitOut {
        meta,
        nodes: w.tables.nodes,
        edges: w.tables.edges,
        refs: w.tables.refs,
        arena: w.arena.into_vec(),
    })
}

impl<'t> Walker<'t> {
    fn text(&self, node: Node) -> &'t str {
        &self.src[node.byte_range()]
    }
    fn line_of(&self, node: Node) -> u32 {
        node.start_position().row as u32 + 1
    }
    fn col_of(&self, node: Node) -> u32 {
        util::col16(self.src, &self.line_starts, node.start_position().row, node.start_byte())
    }
    fn end_col_of(&self, node: Node) -> u32 {
        util::col16(self.src, &self.line_starts, node.end_position().row, node.end_byte())
    }
    fn top_row(&self) -> u32 {
        self.stack.last().map(|s| s.row).unwrap_or(0)
    }
    fn inside_class_like(&self) -> bool {
        self.stack
            .last()
            .map(|s| matches!(s.kind, "class" | "struct" | "interface" | "trait" | "enum" | "module"))
            .unwrap_or(false)
    }

    fn push_ref_at(&mut self, from_row: u32, name: &str, kind_code: u8, node: Node) {
        let name_ref = self.arena.put(name);
        self.tables.push_ref(&RefRow {
            from_idx: from_row,
            kind: kind_code,
            line: self.line_of(node),
            column: self.col_of(node),
            reference_name: name_ref,
            candidates: NONE_STR,
            from_id_str: NONE_STR,
        });
        if kind_code == edge_kind_index("imports").unwrap() {
            if util::simple_name().is_match(name) {
                self.imported_names.insert(name.to_string());
            }
        }
    }

    fn create_node(&mut self, kind: &'static str, name: &str, node: Node<'t>, extra: Extra) -> Option<u32> {
        if name.is_empty() {
            return None;
        }
        let start_line = self.line_of(node);
        let id = ids::node_id(self.file_path, kind, name, start_line);
        let end_line = node.end_position().row as u32 + 1;

        let qualified = extra.qualified_name.unwrap_or_else(|| {
            let mut parts: Vec<&str> = Vec::new();
            for s in &self.stack {
                if s.kind != "file" {
                    parts.push(&s.name);
                }
            }
            let mut qn = parts.join("::");
            if !qn.is_empty() {
                qn.push_str("::");
            }
            qn.push_str(name);
            qn
        });

        let mut flags = BoolFlags::default();
        if let Some(v) = extra.is_exported {
            flags.set(FLAG_IS_EXPORTED, v);
        }
        let name_ref = self.arena.put(name);
        let qn_ref = self.arena.put(&qualified);
        let id_ref = self.arena.put(&id);
        let doc_ref = opt_str(&mut self.arena, extra.docstring.as_deref());
        let sig_ref = opt_str(&mut self.arena, extra.signature.as_deref());
        let ret_ref = opt_str(&mut self.arena, extra.return_type.as_deref());
        let row = self.tables.push_node(&NodeRow {
            kind: node_kind_index(kind).unwrap(),
            visibility: 0,
            flags,
            start_line,
            end_line,
            start_column: self.col_of(node),
            end_column: self.end_col_of(node),
            name: name_ref,
            qualified_name: qn_ref,
            id: id_ref,
            docstring: doc_ref,
            signature: sig_ref,
            decorators: NONE_STR,
            type_parameters: NONE_STR,
            return_type: ret_ref,
            extra_json: NONE_STR,
        });
        self.nodes_meta.push(NodeMeta { kind, name: name.to_string() });
        self.node_ids.push(id);

        let parent_row = self.top_row();
        self.tables.push_edge(&EdgeRow {
            source_idx: parent_row,
            target_idx: row,
            kind: edge_kind_index("contains").unwrap(),
            provenance: 0,
            line: NONE,
            column: NONE,
            metadata_json: NONE_STR,
            source_id_str: NONE_STR,
            target_id_str: NONE_STR,
        });

        if kind == "function" || kind == "method" {
            self.defined_fn_names.insert(name.to_string());
        }
        let target_kind_ok = kind == "constant" || kind == "variable";
        if target_kind_ok
            && util::utf16_len(name) >= 3
            && util::has_upper_or_underscore().is_match(name)
        {
            let parent_ok = self
                .stack
                .last()
                .map(|s| matches!(s.kind, "file" | "class" | "module" | "struct" | "enum"))
                .unwrap_or(false);
            if parent_ok {
                self.fs_values.insert(name.to_string(), row);
                *self.fs_value_counts.entry(name.to_string()).or_insert(0) += 1;
            }
        }
        if matches!(kind, "function" | "method" | "constant" | "variable") {
            self.value_scopes.push(ValueScope { row, node, name: name.to_string() });
        }
        Some(row)
    }

    fn extract_name(&self, node: Node) -> String {
        // GDScript uses "name" field for class/function/variable names
        if let Some(name_node) = node.child_by_field_name("name") {
            return self.text(name_node).to_string();
        }
        // Fallback: find first identifier child
        for i in 0..node.named_child_count() {
            if let Some(c) = node.named_child(i) {
                if c.kind() == "identifier" {
                    return self.text(c).to_string();
                }
            }
        }
        String::new()
    }

    fn signature_of(&self, node: Node) -> Option<String> {
        let params = node.child_by_field_name("parameters")?;
        let ret = node.child_by_field_name("return_type");
        let mut sig = self.text(params).to_string();
        if let Some(r) = ret {
            sig.push_str(" -> ");
            sig.push_str(self.text(r));
        }
        Some(sig)
    }

    fn is_exported(&self, _node: Node) -> bool {
        // GDScript: @export is an annotation, but for now treat all as exported
        // since GDScript has no true visibility modifiers
        true
    }

    fn return_type_of(&self, node: Node) -> Option<String> {
        node.child_by_field_name("return_type").map(|n| self.text(n).to_string())
    }

    // --- visit dispatch ---------------------------------------------------------

    fn visit_node(&mut self, node: Node<'t>) {
        let kind = node.kind();
        let mut skip_children = false;

        self.maybe_capture_fn_refs(node);

        match kind {
            "class_name_statement" => {
                self.extract_class_name(node);
            }
            "class_definition" => {
                self.extract_class(node);
                skip_children = true;
            }
            "function_definition" => {
                self.extract_function(node, false);
                skip_children = true;
            }
            "static_function_definition" => {
                self.extract_function(node, true);
                skip_children = true;
            }
            "variable_statement" => {
                self.extract_variable(node);
            }
            "const_statement" => {
                self.extract_constant(node);
            }
            "signal_statement" => {
                self.extract_signal(node);
            }
            "enum_definition" => {
                self.extract_enum(node);
                skip_children = true;
            }
            "lambda" => {
                self.extract_lambda(node);
                skip_children = true;
            }
            "call" => {
                self.extract_call(node);
            }
            "extends_statement" => {
                self.extract_extends_statement(node);
            }
            _ => {}
        }

        if !skip_children {
            for i in 0..node.named_child_count() {
                if let Some(c) = node.named_child(i) {
                    self.visit_node(c);
                }
            }
        }
    }

    // --- extractors -------------------------------------------------------------

    /// class_name_statement: `class_name Foo` — global class registration
    fn extract_class_name(&mut self, node: Node<'t>) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        let extra = Extra {
            docstring: preceding_docstring(node, self.src),
            is_exported: Some(true),
            ..Extra::default()
        };
        self.create_node("class", &name, node, extra);
    }

    /// class_definition: `class Foo extends Bar` — inner/nested class
    fn extract_class(&mut self, node: Node<'t>) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        let extra = Extra {
            docstring: preceding_docstring(node, self.src),
            is_exported: Some(self.is_exported(node)),
            ..Extra::default()
        };
        let Some(row) = self.create_node("class", &name, node, extra) else { return };

        // Extract inheritance from extends_clause
        self.extract_inheritance(node, row);

        // Visit class body
        if let Some(body) = node.child_by_field_name("body") {
            self.stack.push(Scope { row, kind: "class", name: name.clone() });
            for i in 0..body.named_child_count() {
                if let Some(c) = body.named_child(i) {
                    self.visit_node(c);
                }
            }
            self.stack.pop();
        }
    }

    /// function_definition / static_function_definition
    fn extract_function(&mut self, node: Node<'t>, is_static: bool) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        let kind = if self.inside_class_like() {
            if is_static { "method" } else { "method" }
        } else {
            "function"
        };
        let extra = Extra {
            docstring: preceding_docstring(node, self.src),
            signature: self.signature_of(node),
            is_exported: Some(self.is_exported(node)),
            return_type: self.return_type_of(node),
            ..Extra::default()
        };
        let Some(row) = self.create_node(kind, &name, node, extra) else { return };

        // Visit function body for calls and nested functions
        if let Some(body) = node.child_by_field_name("body") {
            self.stack.push(Scope { row, kind: "function", name: name.clone() });
            self.visit_function_body(body);
            self.stack.pop();
        }
    }

    fn visit_function_body(&mut self, node: Node<'t>) {
        let kind = node.kind();
        self.maybe_capture_fn_refs(node);

        if kind == "call" {
            self.extract_call(node);
        } else if kind == "function_definition" || kind == "static_function_definition" {
            self.extract_function(node, kind == "static_function_definition");
            return;
        }

        for i in 0..node.named_child_count() {
            if let Some(c) = node.named_child(i) {
                self.visit_function_body(c);
            }
        }
    }

    /// variable_statement: `var x = value` (with optional @export/@onready)
    fn extract_variable(&mut self, node: Node<'t>) {
        let docstring = preceding_docstring(node, self.src);
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        // Check for @export or @onready annotation
        let has_export = self.has_annotation(node, "export");
        let signature = node
            .child_by_field_name("value")
            .map(|v| util::init_signature(self.text(v)));

        let var_row = self.create_node(
            "variable",
            &name,
            node,
            Extra {
                docstring,
                signature,
                is_exported: Some(has_export || self.is_exported(node)),
                ..Extra::default()
            },
        );

        // Walk initializer for calls
        if let Some(value) = node.child_by_field_name("value") {
            if let Some(row) = var_row {
                let var_name = self.nodes_meta[row as usize].name.clone();
                self.stack.push(Scope { row, kind: "variable", name: var_name });
                self.visit_function_body(value);
                self.stack.pop();
            } else {
                self.visit_function_body(value);
            }
        }
    }

    /// const_statement: `const FOO = value`
    fn extract_constant(&mut self, node: Node<'t>) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        let signature = node
            .child_by_field_name("value")
            .map(|v| util::init_signature(self.text(v)));
        self.create_node(
            "constant",
            &name,
            node,
            Extra {
                docstring: preceding_docstring(node, self.src),
                signature,
                is_exported: Some(self.is_exported(node)),
                ..Extra::default()
            },
        );
    }

    /// signal_statement: `signal my_signal`
    fn extract_signal(&mut self, node: Node<'t>) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        self.create_node(
            "variable", // signals map to variable-like symbols
            &name,
            node,
            Extra {
                docstring: preceding_docstring(node, self.src),
                is_exported: Some(true),
                ..Extra::default()
            },
        );
    }

    /// enum_definition: `enum Foo { A, B, C }`
    fn extract_enum(&mut self, node: Node<'t>) {
        let name = self.extract_name(node);
        if name.is_empty() {
            return;
        }
        let extra = Extra {
            docstring: preceding_docstring(node, self.src),
            is_exported: Some(self.is_exported(node)),
            ..Extra::default()
        };
        let Some(row) = self.create_node("enum", &name, node, extra) else { return };

        // Extract enumerators as constants
        if let Some(body) = node.child_by_field_name("body") {
            self.stack.push(Scope { row, kind: "enum", name: name.clone() });
            for i in 0..body.named_child_count() {
                if let Some(child) = body.named_child(i) {
                    if child.kind() == "enumerator" {
                        let enum_name = self.extract_name(child);
                        if !enum_name.is_empty() {
                            self.create_node(
                                "constant",
                                &enum_name,
                                child,
                                Extra { is_exported: Some(true), ..Extra::default() },
                            );
                        }
                    }
                }
            }
            self.stack.pop();
        }
    }

    /// lambda: `func(): ...` anonymous function
    fn extract_lambda(&mut self, node: Node<'t>) {
        let name = format!("lambda@{}", self.line_of(node));
        let extra = Extra {
            signature: self.signature_of(node),
            return_type: self.return_type_of(node),
            ..Extra::default()
        };
        let Some(row) = self.create_node("function", &name, node, extra) else { return };
        if let Some(body) = node.child_by_field_name("body") {
            self.stack.push(Scope { row, kind: "function", name });
            self.visit_function_body(body);
            self.stack.pop();
        }
    }

    /// call: `foo()` — function call reference
    fn extract_call(&mut self, node: Node<'t>) {
        if self.stack.is_empty() {
            return;
        }
        let callee = node.child_by_field_name("function");
        let callee_name = callee.map(|c| self.text(c).to_string()).unwrap_or_default();
        if callee_name.is_empty() {
            return;
        }
        let from_row = self.top_row();
        self.push_ref_at(
            from_row,
            &callee_name,
            FUNCTION_REF_CODE,
            callee.unwrap_or(node),
        );
    }

    /// extends_statement: `extends Bar` or `extends "res://path.gd"`
    fn extract_extends_statement(&mut self, node: Node<'t>) {
        // extends_statement is a top-level statement, find the parent class
        let parent_class_row = self.stack.iter().rev().find(|s| s.kind == "class").map(|s| s.row);
        if let Some(class_row) = parent_class_row {
            // Find the extended class name
            for i in 0..node.named_child_count() {
                if let Some(child) = node.named_child(i) {
                    if child.kind() == "identifier" {
                        let parent_name = self.text(child).to_string();
                        self.tables.push_edge(&EdgeRow {
                            source_idx: class_row,
                            target_idx: 0, // unresolved — will be resolved later
                            kind: edge_kind_index("extends").unwrap(),
                            provenance: 0,
                            line: self.line_of(child),
                            column: self.col_of(child),
                            metadata_json: NONE_STR,
                            source_id_str: NONE_STR,
                            target_id_str: NONE_STR,
                        });
                        self.push_ref_at(class_row, &parent_name, edge_kind_index("extends").unwrap(), child);
                        break;
                    }
                }
            }
        }
    }

    /// extract_inheritance: find extends_clause inside class_definition
    fn extract_inheritance(&mut self, class_node: Node<'t>, class_row: u32) {
        for i in 0..class_node.named_child_count() {
            if let Some(child) = class_node.named_child(i) {
                if child.kind() == "extends_clause" {
                    // extends_clause contains the parent class identifier
                    for j in 0..child.named_child_count() {
                        if let Some(ident) = child.named_child(j) {
                            if ident.kind() == "identifier" {
                                let parent_name = self.text(ident).to_string();
                                self.push_ref_at(
                                    class_row,
                                    &parent_name,
                                    edge_kind_index("extends").unwrap(),
                                    ident,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    // --- helpers ----------------------------------------------------------------

    fn has_annotation(&self, node: Node<'t>, annotation_name: &str) -> bool {
        let mut current = node.prev_named_sibling();
        while let Some(sibling) = current {
            if sibling.kind() == "annotation" || sibling.kind() == "annotations" {
                let text = self.text(sibling);
                if text.contains(annotation_name) {
                    return true;
                }
                current = sibling.prev_named_sibling();
            } else if sibling.kind() == "comment" {
                current = sibling.prev_named_sibling();
            } else {
                break;
            }
        }
        false
    }

    // --- fn-refs & value-refs (simplified) --------------------------------------

    fn maybe_capture_fn_refs(&mut self, node: Node<'t>) {
        // Simplified: capture function references from call arguments
        if node.kind() == "call" {
            if let Some(args) = node.child_by_field_name("arguments") {
                for i in 0..args.named_child_count() {
                    if let Some(arg) = args.named_child(i) {
                        if arg.kind() == "identifier" {
                            let name = self.text(arg).to_string();
                            if !name.is_empty() {
                                self.fn_ref_cands.push(Cand {
                                    from: self.top_row(),
                                    name,
                                    line: self.line_of(arg),
                                    column_byte: arg.start_byte(),
                                    row: 0,
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    fn flush_fn_ref_candidates(&mut self) {
        for cand in &self.fn_ref_cands {
            if self.defined_fn_names.contains(&cand.name) || self.imported_names.contains(&cand.name) {
                let name_ref = self.arena.put(&cand.name);
                self.tables.push_ref(&RefRow {
                    from_idx: cand.from,
                    kind: FUNCTION_REF_CODE,
                    line: cand.line,
                    column: 0,
                    reference_name: name_ref,
                    candidates: NONE_STR,
                    from_id_str: NONE_STR,
                });
            }
        }
    }

    fn flush_value_refs(&mut self, root: Node<'t>) {
        // Simplified value-ref resolution — collect first to avoid borrow conflict
        let scopes: Vec<(u32, String)> = self
            .value_scopes
            .iter()
            .map(|vs| (vs.row, vs.name.clone()))
            .collect();
        for (row, name) in &scopes {
            self.scan_value_refs_in_node(root, *row, name);
        }
    }

    fn scan_value_refs_in_node(&mut self, node: Node<'t>, reader_row: u32, target_name: &str) {
        if node.kind() == "identifier" {
            let name = self.text(node).to_string();
            if name == target_name {
                if self.fs_values.contains_key(target_name) {
                    let name_ref = self.arena.put(target_name);
                    self.tables.push_ref(&RefRow {
                        from_idx: reader_row,
                        kind: FUNCTION_REF_CODE,
                        line: self.line_of(node),
                        column: self.col_of(node),
                        reference_name: name_ref,
                        candidates: NONE_STR,
                        from_id_str: NONE_STR,
                    });
                }
            }
        }
        for i in 0..node.named_child_count() {
            if let Some(c) = node.named_child(i) {
                self.scan_value_refs_in_node(c, reader_row, target_name);
            }
        }
    }
}

fn opt_str(arena: &mut Arena, s: Option<&str>) -> StrRef {
    match s {
        Some(s) if !s.is_empty() => arena.put(s),
        _ => NONE_STR,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Check if the arena contains a given substring.
    fn arena_contains(out: &EmitOut, needle: &str) -> bool {
        let arena_str = std::str::from_utf8(&out.arena).unwrap_or("");
        arena_str.contains(needle)
    }

    fn extract_test(source: &str) -> EmitOut {
        extract("test.gd", source).expect("extract should succeed")
    }

    #[test]
    fn test_class_name() {
        let out = extract_test("class_name MyPlayer\n");
        assert!(arena_contains(&out, "MyPlayer"), "should extract class_name MyPlayer");
    }

    #[test]
    fn test_function_extraction() {
        let source = "func _ready() -> void:\n    pass\n";
        let out = extract_test(source);
        assert!(arena_contains(&out, "_ready"), "should extract _ready function");
    }

    #[test]
    fn test_variable_extraction() {
        let source = "var health: int = 100\n";
        let out = extract_test(source);
        assert!(arena_contains(&out, "health"), "should extract health variable");
    }

    #[test]
    fn test_const_extraction() {
        let source = "const MAX_SPEED = 300.0\n";
        let out = extract_test(source);
        assert!(arena_contains(&out, "MAX_SPEED"), "should extract MAX_SPEED constant");
    }

    #[test]
    fn test_signal_extraction() {
        let source = "signal player_died\n";
        let out = extract_test(source);
        assert!(arena_contains(&out, "player_died"), "should extract player_died signal");
    }

    #[test]
    fn test_enum_extraction() {
        let source = "enum Direction {\n    UP,\n    DOWN,\n}\n";
        let out = extract_test(source);
        assert!(arena_contains(&out, "Direction"), "should extract Direction enum");
    }

    #[test]
    fn test_full_script() {
        let source = r##"class_name MyPlayer
extends CharacterBody2D

const MAX_SPEED = 300.0
var health: int = 100
@export var speed: float = 200.0
signal player_died

enum Direction { UP, DOWN }

func _ready() -> void:
    _initialize()

func _process(delta: float) -> void:
    pass

static func create() -> MyPlayer:
    return MyPlayer.new()

func _initialize() -> void:
    pass
"##;
        let out = extract_test(source);

        assert!(arena_contains(&out, "MyPlayer"), "should have MyPlayer");
        assert!(arena_contains(&out, "MAX_SPEED"), "should have MAX_SPEED");
        assert!(arena_contains(&out, "health"), "should have health");
        assert!(arena_contains(&out, "_ready"), "should have _ready");
        assert!(arena_contains(&out, "Direction"), "should have Direction");
    }
}
