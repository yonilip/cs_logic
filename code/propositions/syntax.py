""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """

NOT = '~'
AND = '&'
OR = '|'
NOR = '-|'
NAND = '-&'
IMPLIES = '->'
IFF = '<->'
MUX_GATE = '?'
MUX_SEP = ':'
MUX = MUX_GATE + MUX_SEP
T_str = 'T'
F_str = 'F'


def is_variable(s):  # DONT EDIT
    """ Is s an atomic proposition?  """
    return 'p' <= s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())  # simplified for py3


def is_unary(s):  # DONT EDIT
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s == '&' or s == '|' or s == '-|' or s == '-&' or s == '->' or s == '<->'


def is_ternary(s):
    """ Is a ternary operator? """
    return s == '?:'


def is_constant(s):  # DONT EDIT
    """ Is s a constant? """
    return s == 'T' or s == 'F'


def get_index_of_binary_operator(s):
    """
    :param s: formula
    :return: returns the index of the binary operator between the two sub-formulae
    """
    parenthesis_counter = 0  # add 1 for ( and subtract 1 for )
    for i in range(len(s)):
        if s[i] == "(":
            parenthesis_counter += 1
        if s[i] == ")":
            parenthesis_counter -= 1
        if not parenthesis_counter:
            if is_binary(s[i]):
                return i, i
            if is_binary(s[i:i + 2]):
                return i, i + 1
            if is_binary(s[i:i + 3]):
                return i, i + 2
            if is_binary(s[i:i + 4]):
                return i, i + 3


def get_index_of_ternary_operators(s):
    q_mark_idx = 0
    sep_mark_idx = 0
    parenthesis_counter = 0  # add 1 for ( and subtract 1 for )
    for i in range(len(s)):
        if s[i] == "(":
            parenthesis_counter += 1
        if s[i] == ")":
            parenthesis_counter -= 1
        if not parenthesis_counter:
            if s[i] == "?":
                q_mark_idx = i
            elif s[i] == ":":
                sep_mark_idx = i
            if q_mark_idx < sep_mark_idx:
                return q_mark_idx, sep_mark_idx


def extract_rhd_symbol(s):
    """
    splits the rhd most symbol from s
    :param s: formula as a string
    :return: tuple of rhd and remaining lhd from split
    """
    last_three_char = s[-3:]
    if is_binary(last_three_char):
        return s[:-3], last_three_char
    last_two_char = s[-2:]
    if is_binary(last_two_char) or is_ternary(last_two_char):
        return s[:-2], last_two_char
    last_char = s[-1]
    if is_constant(last_char) or is_unary(last_char) or is_binary(last_char):
        return s[:-1], last_char

    # var case
    for i in reversed(range(len(s))):
        rhd = s[i:]
        if is_variable(rhd):
            return s[:i], rhd


def is_binary_or_ternary_case(s):
    q_mark_idx = -1
    binary_mark_idx = -1
    parenthesis_counter = 0
    for i in range(len(s)):
        if s[i] == "(":
            parenthesis_counter += 1
        if s[i] == ")":
            parenthesis_counter -= 1
        if not parenthesis_counter:
            if s[i] == "?":
                q_mark_idx = i
            if s[i] in [AND, OR, '-']:
                binary_mark_idx = i
            if q_mark_idx > 0:
                return "TERNARY"
            if binary_mark_idx > 0:
                return "BINARY"



class Formula:
    """ A Propositional Formula """

    def __init__(self, root, first=None, second=None, third=None):
        """ Create a new formula from its root (a string) and, when needed, the
        first and second operands (each of them a Formula)."""
        self.vars = set()

        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
            self.vars.add(root) if is_variable(root) else None
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
            self.vars = self.vars.union(self.first.vars)
        elif is_binary(root):
            assert type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second
            self.vars = self.vars.union(first.vars)
            self.vars = self.vars.union(second.vars)
        elif is_ternary(root):
            assert type(first) is Formula and type(second) is Formula and type(third) is Formula
            self.root, self.first, self.second, self.third = root, first, second, third
            self.vars = self.vars.union(first.vars)
            self.vars = self.vars.union(second.vars)
            self.vars = self.vars.union(third.vars)
        else:
            raise ValueError("Given params to Formula invalid!")

    def __repr__(self):  # DONT EDIT
        return self.infix()

    def __eq__(self, other):  # DONT EDIT
        return self.infix() == other.infix()

    def __ne__(self, other):  # DONT EDIT
        return not self == other

    def infix(self):
        """ Return an infix representation of self """
        # Task 1.1
        if is_constant(self.root) or is_variable(self.root):
            return self.root

        if is_unary(self.root):
            return self.root + self.first.infix()

        if is_binary(self.root):
            return "(" + self.first.infix() + self.root + self.second.infix() + ")"

        if is_ternary(self.root):
            return "(" + self.first.infix() + MUX_GATE + \
                   self.second.infix() + MUX_SEP + self.third.infix() + ")"
        else:
            raise Exception("Invalid Formula")

    @staticmethod
    def from_infix(s):
        """ Return a propositional formula whose infix representation is s """
        # Task 1.2
        if is_constant(s) or is_variable(s):
            formula = Formula(s)
        elif is_unary(s[0]):
            formula = Formula(s[0], Formula.from_infix(s[1:]))

        # case binary in parenthesis
        elif s[0] is "(" and s[-1] is ")":
            s = s[1:-1]  # remove outer parenthesis

            case = is_binary_or_ternary_case(s)
            if case == "BINARY":
                l_op_idx, r_op_idx = get_index_of_binary_operator(s)
                if l_op_idx == r_op_idx:
                    formula = Formula(s[l_op_idx],
                                      Formula.from_infix(s[:l_op_idx]),
                                      Formula.from_infix(s[l_op_idx + 1:])
                                      )
                else:
                    formula = Formula(s[l_op_idx:r_op_idx + 1],
                                      Formula.from_infix(s[:l_op_idx]),
                                      Formula.from_infix(s[r_op_idx + 1:]))
            else:  # ternary case
                l_op_idx, r_op_idx = get_index_of_ternary_operators(s)
                formula = Formula('?:',
                                  Formula.from_infix(s[:l_op_idx]),
                                  Formula.from_infix(s[l_op_idx + 1: r_op_idx]),
                                  Formula.from_infix(s[r_op_idx + 1:]))
        else:
            raise ValueError("Invalid infix string given {s}".format(s=s))
        return formula

    def is_binary_formula(self):
        return hasattr(self, 'first') and hasattr(self, 'second') and not hasattr(self, 'third')

    def is_unary_formula(self):
        return hasattr(self, 'first') and not hasattr(self, 'second') and not hasattr(self, 'third')

    def is_ternary_formula(self):
        return hasattr(self, 'first') and hasattr(self, 'second') and hasattr(self, 'third')

    def is_constant_formula(self):
        return is_constant(self.root)

    def is_variable_formula(self):
        return is_variable(self.root)

    def prefix(self):
        """ Return a prefix representation of self """
        # Task 1.3
        final_repr = self.root
        if hasattr(self, 'first'):
            final_repr += self.first.prefix()
        if hasattr(self, 'second'):
            final_repr += self.second.prefix()
        if hasattr(self, 'third'):
            final_repr += self.third.prefix()
        return final_repr

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        # Task 1.4
        stack = []
        while s:
            s, rhd = extract_rhd_symbol(s)
            if is_constant(rhd) or is_variable(rhd):
                formula = Formula(rhd)
                stack.append(formula)
            elif is_unary(rhd):
                formula = Formula(rhd, stack.pop())
                stack.append(formula)
            elif is_binary(rhd):
                formula = Formula(rhd, stack.pop(), stack.pop())
                stack.append(formula)
            elif is_ternary(rhd):
                formula = Formula(rhd, stack.pop(), stack.pop(), stack.pop())
                stack.append(formula)
        return stack[0]

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        # Task 1.5
        return sorted(self.vars)
