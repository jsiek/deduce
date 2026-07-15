const prims = ['(?:[0-9])+', 'true', 'false', '∅', '\\.0\\.', 'emp', '0']

const whitespaces = ['(?:[ \t\x0c\r\n])+']

const types = ['fn', 'bool', 'type']

const keywords = ['[ℕ](?:[0-9])+', '[\\-\\+∸*%=≠<>≤≥&∘∪∩⊆∈⨄⊝\\^≲≈]', 'and', 'or', 'in', 'case', 'not', 'fun', 'generic', 'switch', 'all', 'some', 'define', 'if', 'then', 'else', 'suppose', 'assume', 'by', 'proof', 'end', 'conclude', 'apply', 'to', 'contradict', 'conjunct', 'of', 'cases', 'induction', 'rule', 'inversion', 'expand', 'replace', 'evaluate', 'simplify', 'for', 'equations', 'recall', 'reflexive', 'symmetric', 'transitive', 'help', 'sorry', 'with', 'arbitrary', 'choose', 'show', 'extensionality', 'have', 'injective', 'obtain', 'where', 'from', 'stop', 'suffices', 'theorem', 'lemma', 'postulate', 'public', 'private', 'opaque', 'union', 'predicate', 'relation', 'recursive', 'recfun', 'view', 'source', 'target', 'into', 'out', 'roundtrip', 'measure', 'terminates', 'import', 'using', 'hiding', 'export', 'assert', 'print', 'associative', 'auto', 'module', 'trace', 'inductive', 'object', 'proc', 'observer', 'resource', 'ghost', 'var', 'requires', 'ensures', 'reads', 'modifies', 'footprint', 'invariant', 'decreases', 'established', 'preserved', 'while', 'call', 'as', 'return', 'new', 'inverse']

const identifiers = ["(?:[A-Z]|[a-z]|_)(?:(?:[₀₁₂₃₄₅₆₇₈₉!?']|[A-Z]|[a-z]|[0-9]|_))*"]

const operators = ['\\-&gt;', 'iff', '&lt;&equals;&gt;', '⇔', ':', '&equals;', '≠', '&sol;&equals;', '&lt;', '&gt;', '≤', '&lt;&equals;', '≥', '&gt;&equals;', '⊆', '\\(&equals;', '∈', '≲', '≈', '\\+', '∪', '\\|', '∩', '\\&amp;', '⨄', '\\.\\+\\.', '\\+\\+', '\\-', '∸', '\\.\\-\\.', '⊝', '&sol;', '%', '\\*', '∘', '\\.o\\.', '\\^', '\\{', '\\}', 'operator', '@', 'array', '\\(', '\\)', '\\[', '\\]', 'λ', '\\.', '&semi;', '\\?', '─', '__', '\\#', ',', '\\.\\.\\.', '\\$', '!', '\\*\\*', '\\|\\-&gt;', ':&equals;']

const comments = ['&sol;&sol;[^\n]*', '\\&sol;\\*(\\*(?!\\&sol;)|[^*])*\\*\\&sol;']

const libs = ['UIntDefs', 'NatPowLog', 'UIntMult', 'UIntMonus', 'MultiSet', 'UIntToFrom', 'Set', 'NatAdd', 'UInt', 'NatDefs', 'Int', 'UIntPowLog', 'Base', 'Pair', 'NatDiv', 'NatMult', 'NatEvenOdd', 'NatSum', 'Maps', 'UIntEvenOdd', 'NatMonus', 'IntMult', 'IntAddSub', 'List', 'BigO', 'Option', 'NatLess', 'IntDefs', 'UIntLess', 'UIntDiv', 'Nat', 'UIntAdd']

export { prims, whitespaces, types, keywords, identifiers, operators, comments, libs }
