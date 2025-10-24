const idents = ["(?:[A-Z]|[a-z]|_)(?:(?:[₀₁₂₃₄₅₆₇₈₉!?']|[A-Z]|[a-z]|[0-9]|_))*"]

const types = ['fn', 'bool', 'type']

const prims = ['(?:[0-9])+', '∘', '\\.o\\.', 'true', 'false', '─', '\\.\\.\\.']

const operators = ['iff', '&lt;&equals;&gt;', '⇔', ':', '&equals;', '≠', '&sol;&equals;', '&lt;', '&gt;', '≤', '&lt;&equals;', '≥', '&gt;&equals;', '⊆', '\\(&equals;', '∈', '≲', '≈', '\\+', '∪', '\\|', '∩', '\\&amp;', '⨄', '\\.\\+\\.', '\\+\\+', '\\-', '∸', '&sol;', '%', '\\*', '\\^', '\\{', '\\}', 'operator', '∅', '\\.0\\.', '@', 'array', '\\(', '\\)', '\\[', '\\]', 'λ', '\\.', '&semi;', '\\?', '__', '\\#', ',', '\\$', '\\-&gt;', '0']

const keywords = ['[ℕ](?:[0-9])+', '[\\-\\+∸*%&equals;≠&lt;&gt;≤≥&amp;∘∪∩⊆∈⨄⊝\\^≲≈]', 'and', 'or', 'in', '⊝', 'case', 'not', 'fun', 'generic', 'switch', 'all', 'some', 'define', 'if', 'then', 'else', 'suppose', 'assume', 'by', 'proof', 'end', 'conclude', 'apply', 'to', 'contradict', 'conjunct', 'of', 'cases', 'induction', 'expand', 'replace', 'evaluate', 'for', 'equations', 'recall', 'reflexive', 'symmetric', 'transitive', 'help', 'sorry', 'arbitrary', 'choose', 'show', 'extensionality', 'have', 'injective', 'obtain', 'where', 'from', 'stop', 'suffices', 'theorem', 'lemma', 'postulate', 'public', 'private', 'opaque', 'union', 'recursive', 'recfun', 'measure', 'terminates', 'import', 'export', 'assert', 'print', 'associative', 'auto', 'module']

const whitespaces = ['(?:[ \t\x0c\r\n])+']

const comments = ['&sol;&sol;[^\n]*', '\\&sol;\\*(\\*(?!\\&sol;)|[^*])*\\*\\&sol;']

const libs = ['UInt', 'Pair', 'NatLess', 'NatMonus', 'UIntAdd', 'Option', 'IntDefs', 'NatMult', 'MultiSet', 'Set', 'List', 'Int', 'NatPowLog', 'Base', 'NatSum', 'UIntToFrom', 'NatDefs', 'UIntLess', 'IntMult', 'UIntDefs', 'IntAddSub', 'UIntDiv', 'UIntEvenOdd', 'Nat', 'NatAdd', 'UIntMult', 'UIntMonus', 'UIntPowLog', 'BigO', 'NatEvenOdd', 'Maps', 'NatDiv']

export { idents, types, prims, operators, keywords, whitespaces, comments, libs }