""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """


def is_variable(s):
    """ Is s an atomic proposition?  """
    return 'p' <= s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())  # simplified for py3


def is_unary(s):
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s == '&' or s == '|'


def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'


def get_index_of_binary_operator(s):
    """
    :param s: formula
    :return: returns the index of the binary operator between the two sub-formulae
    """
    parenthesis_counter = 0  # add 1 for ( and subtract 1 for )
    for i in range(len(s)):
        if s[i] is "(":
            parenthesis_counter += 1
        if s[i] is ")":
            parenthesis_counter -= 1
        if is_binary(s[i]) and not parenthesis_counter:
            return i


def extract_rhd_symbol(s):
    """
    splits the rhd most symbol from s
    :param s: formula as a string
    :return: tuple of rhd and remaining lhd from split
    """
    last_char = s[-1]
    if is_constant(last_char) or is_unary(last_char) or is_binary(last_char):
        return s[:-1], last_char

    # var case
    for i in reversed(range(len(s))):
        rhd = s[i:]
        if is_variable(rhd):
            return s[:i], rhd


def add_vars_field(formula, s):
    """
    adds the vars field to the formula
    """
    formula.vars = set()
    formula.vars.add(s) if is_variable(s) else None
    return formula


def union_vars_sets(formula, binary_formula=False):
    """
    unions the vars set to contain the first and second vars sets
    second set will be added if formula is binary
    """
    formula.vars = set()
    formula.vars = formula.vars.union(formula.first.vars)
    if binary_formula:
        formula.vars = formula.vars.union(formula.second.vars)
    return formula


class Formula:
    """ A Propositional Formula """

    def __init__(self, root, first=None, second=None):
        """ Create a new formula from its root (a string) and, when needed, the
        first and second operands (each of them a Formula)."""
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __repr__(self):
        return self.infix()

    def __eq__(self, other):
        return self.infix() == other.infix()

    def __ne__(self, other):
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

        else:
            raise Exception("Invalid Formula")

    @staticmethod
    def from_infix(s):
        """ Return a propositional formula whose infix representation is s """
        # Task 1.2
        if is_constant(s) or is_variable(s):
            formula = Formula(s)
            formula = add_vars_field(formula, s)
            return formula

        if is_unary(s[0]):
            formula = Formula(s[0], Formula.from_infix(s[1:]))
            formula = union_vars_sets(formula)
            return formula

        # case binary in parenthesis
        if s[0] is "(" and s[-1] is ")":
            s = s[1:-1]  # remove outer parenthesis
            operator_idx = get_index_of_binary_operator(s)
            formula = Formula(s[operator_idx],
                           Formula.from_infix(s[:operator_idx]),
                           Formula.from_infix(s[operator_idx + 1:])
                           )
            binary_formula = True
            formula = union_vars_sets(formula, binary_formula)
            return formula

    def prefix(self):
        """ Return a prefix representation of self """
        # Task 1.3
        final_repr = self.root
        if hasattr(self, 'first'):
            final_repr += self.first.prefix()
        if hasattr(self, 'second'):
            final_repr += self.second.prefix()
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
                formula = add_vars_field(formula, rhd)
                stack.append(formula)
            elif is_unary(rhd):
                formula = Formula(rhd, stack.pop())
                formula = union_vars_sets(formula)
                stack.append(formula)
            elif is_binary(rhd):
                binary_formula = True
                formula = Formula(rhd, stack.pop(), stack.pop())
                formula = union_vars_sets(formula, binary_formula)
                stack.append(formula)
        return stack[0]

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self """
        # Task 1.5
        return self.vars
