from pprint import pprint
from collections import defaultdict

class Node:
    def __init__(self, type):
        self.type = type
        self.contents = []

    def append(self, x):
        self.contents.append(x)

    def to_str(self):
        contents = []
        for a in self.contents:
            if type(a) == Node:
                contents.append(a.to_str())
            else:
                contents.append(a)
        return (self.type, contents)
    
    def __str__(self):
        return self.to_str().__str__()
    
    def __repr__(self):
        return self.__str__()

class GrammarAnalyzer:
    EPSILON = 'EPSILON'
    COMMENT = '#'
    REWRITE = '='
    SPLITTER = '.'
    EOF = '$'

    def __init__(self):
        self.rules = []
        self.instance_counter = 0
        self.nonterminals = set()
        self.start_symbol = ""

        self.first_set = defaultdict(set)
        self.follow_set = defaultdict(set)
        self.director_set = defaultdict(set)

    def exec(self, text):
        text = self.reform_text(text)
        self.parse_text(text)
        self.convert_to_bnf()
        self.analyze_LL1()

    def reform_text(self, text):
        text = text.replace('->', self.REWRITE)
        text = text.replace('ε', self.EPSILON)
        text = text.replace('epsilon', self.EPSILON)
        # remove comment
        lines = []
        for line in text.split('\n'):
            line = line.strip()
            if len(line) > 0 and line[0] != self.COMMENT:
                lines.append(line)
        return '\n'.join(lines)

    def parse_text(self, text):
        tokens = text.split()

        rules = []
        rule = []
        for token in tokens:
            if token == self.SPLITTER:
                rules.append(rule)
                rule = []
            else:
                rule.append(token)

        for rule in rules:
            lhs = rule[0]
            assert rule[1] == self.REWRITE
            rhs = rule[2:]
            self.rules.append((lhs, self.parse_rhs(rhs)))

        self.start_symbol = rules[0][0]
        return rules

    def token2type(self, token):
        if token in '()':
            return 'grouping'
        elif token in '[]':
            return 'option'
        elif token in '{}':
            return 'repetition'
        else:
            assert False

    def parse_rhs(self, rhs):
        tree = Node('sequence')
        node_stack = [tree]

        for i, token in enumerate(rhs):
            if token in '([{':
                node = Node(self.token2type(token))
                node_stack[-1].append(node)
                node_stack.append(node)
            elif token in ')]}':
                assert node_stack[-1].type == self.token2type(token)
                self.split_by_alternatives(node_stack[-1])
                node_stack.pop()
            else:
                node_stack[-1].append(token)

        self.split_by_alternatives(node_stack[-1])
        return tree

    def split_by_alternatives(self, node):
        if '|' not in node.contents:
            return

        new_contents = [Node('sequence')]
        for x in node.contents:
            if x != '|':
                new_contents[-1].append(x)
            else:
                new_contents.append(Node('sequence'))
        
        if node.type == 'sequence':
            node.contents = new_contents
            node.type = 'alternative'
        else:
            new_node = Node('alternative')
            new_node.contents = new_contents
            node.contents.clear()
            node.contents.append(new_node)

    def convert_to_bnf(self):
        self.remove_repetitions()
        self.remove_options()
        self.remove_groupings()
        self.remove_alternatives()

    def remove_repetitions(self):
        self.instance_counter = 0
        for rule in self.rules:
            self.apply_nodes_recursively(self.substitute_repetition_node, rule[1])
    
    def substitute_repetition_node(self, parent, i):
        node = parent.contents[i]
        if node.type != 'repetition':
            return
        
        self.instance_counter += 1
        var = f"_R{self.instance_counter}"
        rhs = Node('alternative')
        rhs.contents.extend([Node('sequence'), Node('sequence')])
        rhs.contents[0].contents.append(self.EPSILON)
        rhs.contents[1].contents.append(var)
        rhs.contents[1].contents.extend(node.contents)
        self.rules.append((var, rhs))
        parent.contents[i] = var

    def remove_options(self):
        self.instance_counter = 0
        for rule in self.rules:
            self.apply_nodes_recursively(self.substitute_option_node, rule[1])

    def substitute_option_node(self, parent, i):
        node = parent.contents[i]
        if node.type != 'option':
            return
        
        self.instance_counter += 1
        var = f'_O{self.instance_counter}'
        rhs = Node('alternative')
        rhs.contents.extend([Node('sequence'), Node('sequence')])
        rhs.contents[0].contents.append(self.EPSILON)
        rhs.contents[1].contents = node.contents
        self.rules.append((var, rhs))
        parent.contents[i] = var

    def remove_groupings(self):
        self.instance_counter = 0
        for rule in self.rules:
            self.apply_nodes_recursively(self.substitute_grouping_node, rule[1])

    def substitute_grouping_node(self, parent, i):
        node = parent.contents[i]
        if node.type != 'grouping':
            return
        
        self.instance_counter += 1
        var = f'_G{self.instance_counter}'
        if len(node.contents) == 1 and node.contents[0].type == 'alternative':
            rhs = node.contents[0]
        else:
            rhs = Node('sequence')
            rhs.contents = node.contents
        self.rules.append((var, rhs))
        parent.contents[i] = var

    def remove_alternatives(self):
        new_rules = defaultdict(list)
        for rule in self.rules:
            node = rule[1]
            if type(node) == Node and node.type == 'alternative':
                for sequence_node in node.contents:
                    assert type(sequence_node) == Node
                    assert sequence_node.type == 'sequence'
                    new_rules[rule[0]].append(sequence_node.contents)
            else:
                assert node.type == 'sequence'
                new_rules[rule[0]].append(node.contents)
        self.rules = new_rules

    def apply_nodes_recursively(self, func, parent, i = None):
        if i is None:
            for i, _ in enumerate(parent.contents):
                self.apply_nodes_recursively(func, parent, i)
        else:
            node = parent.contents[i]
            if type(node) != Node:
                return
            
            for j, child in enumerate(node.contents):
                if type(child) == Node:
                    self.apply_nodes_recursively(func, node, j)
            func(parent, i)

    def analyze_LL1(self):
        for nt in self.rules.keys():
            self.nonterminals.add(nt)
        self.calculate_first_set()
        self.calculate_follow_set()
        self.calculate_director_set()

    def calculate_first_set(self):
        changed = True
        while changed:
            changed = False
            for nt in self.nonterminals:
                for production in self.rules[nt]:
                    first_subset = self.accumlate_first_set(production)
                    prev_num = len(self.first_set[nt])
                    self.first_set[nt] |= first_subset
                    if len(self.first_set[nt]) > prev_num:
                        changed = True

    def accumlate_first_set(self, symbols):
        first_set = set()
        for symbol in symbols:
            if symbol in self.nonterminals:
                first_set |= (self.first_set[symbol] - set([self.EPSILON]))
                if self.EPSILON not in self.first_set[symbol]:
                    break
            else:
                first_set.add(symbol)
                break
        else:
            if self.EPSILON not in first_set:
                first_set.add(self.EPSILON)
        return first_set

    def calculate_follow_set(self):
        self.follow_set[self.start_symbol].add(self.EOF)
        changed = True
        while changed:
            changed = False
            for nt in self.nonterminals:
                for production in self.rules[nt]:
                    for i, symbol in enumerate(production):
                        if symbol in self.nonterminals:
                            first_subset = self.accumlate_first_set(production[i+1:])
                            prev_num = len(self.follow_set[symbol])
                            self.follow_set[symbol] |= (first_subset - set([self.EPSILON]))
                            if self.EPSILON in first_subset or len(first_subset) == 0:
                                self.follow_set[symbol] |= self.follow_set[nt]
                            if len(self.follow_set[symbol]) > prev_num:
                                changed = True 

    def calculate_director_set(self):
        for nt in self.nonterminals:
            for production in self.rules[nt]:
                key = (nt, tuple(production))
                first_set = self.accumlate_first_set(production)
                self.director_set[key] |= (first_set - self.nonterminals)
                if self.EPSILON in first_set:
                    self.director_set[key] |= (self.follow_set[nt] - self.nonterminals)
                self.director_set[key].discard(self.EPSILON)


if __name__ == '__main__':
    with open('test0.grammar', 'r') as f:
        text = f.read()
    analyzer = GrammarAnalyzer()
    analyzer.exec(text)

    with open("output.txt", 'w') as f:
        pprint(analyzer.rules, stream=f)
        print('\n\n----- first set ------', file=f)
        pprint(analyzer.first_set, stream=f)
        print('\n\n----- follow set ------', file=f)
        pprint(analyzer.follow_set, stream=f)
        print('\n\n----- director set ------', file=f)
        pprint(analyzer.director_set, stream=f)


