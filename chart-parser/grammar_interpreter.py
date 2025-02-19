from dataclasses import dataclass
from lark import Lark, Token, logger, exceptions, tree


@dataclass
class GrammarRule:
    lhs: str
    rhs: list[str]

    def add(self, new_rhs):
        self.rhs.append(new_rhs)

    def __str__(self):
        return self.lhs + " ::= " + "\n\t| ".join(self.rhs)

@dataclass
class Item:
    thing: GrammarRule
    start: int
    end: int

def new_grammar_rule(token_list, position) -> GrammarRule:
    rule_name = token_list[position]
    print("Found rule:", rule_name)
    return Item(GrammarRule, position, position + 2)

def join(list, items):
    for item in items:
        items[item.start].append(item)

def interpret_grammar_rules(tokens):
    rules = []
    tokens = [[token] for token in tokens]
    new = []
    for i in range(len(tokens) - 1):
        token = tokens[i]
        # print(repr(token))
        next = tokens[i + 1]
        if token.type == 'RULE' and next == ':':
            # print("Found grammar rule:", token)
            new.append(new_grammar_rule(tokens, i))
    
    exit(0)


def load_lark_grammar(lark_parser):
    with open("./lark.lark", encoding='utf-8') as lark_file:
        tokens = lark_parser.lex(lark_file.read())
        
    lark_rules = interpret_grammar_rules(tokens)
    


if __name__ == '__main__':
    print("Running grammar interpreter in like debug mode idk man")
    # Tokenize
    rule = GrammarRule("GrammarRule", ["RULE", ":"])

    with open("./lark.lark", encoding='utf-8') as lark_file:
        lark_parser = Lark(lark_file.read(),
                     start='start', parser='lalr',
                     debug=True, propagate_positions=True)
    
    load_lark_grammar(lark_parser)
    print("TODO: start interpreting!")
    exit(255)
        
    # file = "../Deduce.lark"
    file = "example.lark"
    with open(file, encoding='utf-8') as deduce_lark_file:
        deduce_lark_text = deduce_lark_file.read()
    
    tokens = lark_parser.lex(deduce_lark_text)
    for token in tokens:
        print(repr(token))

    # Parse (interpret grammar rules)


    # Interpret deduce file!!!
