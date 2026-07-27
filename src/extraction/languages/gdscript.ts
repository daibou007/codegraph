import { getNodeText, getChildByField } from '../tree-sitter-helpers';
import type { LanguageExtractor } from '../tree-sitter-types';

/**
 * GDScript language extractor config for the wasm fallback path.
 * The Rust kernel handles GDScript natively; this config is used when
 * the kernel is unavailable and the wasm path is the fallback.
 */
export const gdscriptExtractor: LanguageExtractor = {
  functionTypes: ['function_definition', 'static_function_definition'],
  classTypes: ['class_definition'],
  methodTypes: ['function_definition', 'static_function_definition'],
  interfaceTypes: [],
  structTypes: [],
  enumTypes: ['enum_definition'],
  typeAliasTypes: [],
  importTypes: [], // GDScript uses preload/load, not import statements
  callTypes: ['call'],
  variableTypes: ['variable_statement'],
  nameField: 'name',
  bodyField: 'body',
  paramsField: 'parameters',
  returnField: 'return_type',
  getSignature: (node, source) => {
    const params = getChildByField(node, 'parameters');
    const returnType = getChildByField(node, 'return_type');
    if (!params) return undefined;
    let sig = getNodeText(params, source);
    if (returnType) {
      sig += ' -> ' + getNodeText(returnType, source);
    }
    return sig;
  },
  isAsync: (_node) => {
    // GDScript uses await expressions, not async keyword
    return false;
  },
  isStatic: (node) => {
    return node.type === 'static_function_definition';
  },
  extractImport: (_node, _source) => {
    // GDScript preload/load are call expressions, not import statements
    return null;
  },
};
