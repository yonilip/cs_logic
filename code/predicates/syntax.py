""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *


def is_unary(s):  # DONT EDIT
    """ Is s a unary operator? """
    return s == '~'


def is_binary(s):  # DONT EDIT
    """ Is s a binary boolean operator? """
    return s == '&' or s == '|' or s == '->'


def is_equality(s):  # DONT EDIT
    """ Is s the equality relation? """
    return s == "="


def is_quantifier(s):  # DONT EDIT
    """ Is s a quantifier? """
    return s == "A" or s == "E"


def is_relation(s):  # DONT EDIT
    """ Is s a relation name? """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()


def is_constant(s):  # DONT EDIT
    """ Is s a constant name? """
    return ((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd')) and s.isalnum()


def is_function(s):  # DONT EDIT
    """ Is s a function name? """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()


def is_variable(s):  # DONT EDIT
    """ Is s a variable name? """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()


def get_idx_matching_r_par(s, left, right):
    counter = 0
    for i in range(len(s)):
        if s[i] == left:
            counter += 1
        if s[i] == right:
            counter -= 1
            if counter == 0:
                return i


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


class Term:
    """ A term in a first order logical formula, composed from constant names
        and variable names, and function names applied to them """

    def __init__(self, root, arguments=None):  # DONT EDIT
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            for x in arguments:
                assert type(x) is Term
            self.root = root
            self.arguments = arguments

    def __repr__(self):
        """ Return the usual (functional) representation of self """
        # Task 7.1
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        elif is_function(self.root):
            inner_terms = ','.join(str(x) for x in self.arguments)
            return self.root + "(" + inner_terms + ")"

    def __eq__(self, other):  # DONT EDIT
        return str(self) == str(other)

    def __ne__(self, other):  # DONT EDIT
        return not self == other

    def __hash__(self):  # DONT EDIT
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str):
        """ Parse a term from the prefix of a given string. Return a pair: the
            parsed term, and the unparsed remainder of the string """
        # Task 7.3.1
        if not s:  # base case for 0-nary functions / relations
            return [None, '']
        while s[0] == ',':
            s = s[1:]
        if len(s) == 1:
            return [Term(s), '']
        if is_function(s[0]):
            lpar = s.find('(')
            rpar = get_idx_matching_r_par(s, '(', ')')
            root = s[:lpar]
            inner = Term.parse_prefix(s[lpar + 1: rpar])
            args = [inner[0]] if inner[0] is not None else []
            residue = inner[1]
            while residue:
                left, right = Term.parse_prefix(residue)
                residue = right
                args.append(left)
            res = [Term(root, args), s[rpar + 1:]]
            return res

        if is_constant(s[0]):
            for i in range(1, len(s)):
                if not is_constant(s[:i + 1]):
                    return [Term(s[:i]), s[i:]]
            return [Term(s), '']

        if is_variable(s[0]):
            for i in range(1, len(s)):
                if not is_variable(s[:i + 1]):
                    return [Term(s[:i]), s[i:]]
            return [Term(s), '']

    @staticmethod
    def parse(s):
        """ Return a term parsed from its given string representation """
        # Task 7.3.2
        return Term.parse_prefix(s)[0]

    @staticmethod
    def variables_helper(term, variables: list):
        if is_constant(term.root):
            return []
        if is_variable(term.root):
            return [term.root]
        for arg in term.arguments:
            variables += Term.variables_helper(arg, variables)
        return variables

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5
        variables = Term.variables_helper(self, [])
        return set(variables)

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1

    def substitute_variables(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each variable v that appears in the dictionary substitution_map are
            replaced with the term substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
        # Task 9.1

    def substitute_constants(self, substitution_map):
        """ Return a term obtained from this formula where all the occurrences
            of each constant c that appears in the dictionary substitution_map
            are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
        # Ex12


class Formula:
    """ A Formula in first-order logic """

    def __init__(self, root, first=None, second=None):  # DONT EDIT
        if is_relation(root):  # Populate self.root and self.arguments
            assert second is None
            for x in first:
                assert type(x) is Term
            self.root, self.arguments = root, first
        elif is_equality(root):  # Populate self.first and self.second
            assert type(first) is Term and type(second) is Term
            self.root, self.first, self.second = root, first, second
        elif is_quantifier(root):  # Populate self.variable and self.predicate
            assert is_variable(first) and type(second) is Formula
            self.root, self.variable, self.predicate = root, first, second
        elif is_unary(root):  # Populate self.first
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:  # Populate self.first and self.second
            assert is_binary(root) and type(first) is Formula and type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __repr__(self):
        """ Return the usual (infix for operators and equality, functional for
            other relations) representation of self """
        # Task 7.2
        if is_relation(self.root):
            inner_terms = ','.join(str(x) for x in self.arguments)
            return self.root + '(' + inner_terms + ')'
        elif is_equality(self.root):
            return str(self.first) + '=' + str(self.second)
        elif is_quantifier(self.root):
            return self.root + self.variable + '[' + str(self.predicate) + ']'
        elif is_unary(self.root):
            return self.root + str(self.first)
        elif is_binary(self.root):
            return '(' + str(self.first) + self.root + str(self.second) + ')'

    def __eq__(self, other):  # DONT EDIT
        return str(self) == str(other)

    def __ne__(self, other):  # DONT EDIT
        return not self == other

    def __hash__(self):  # DONT EDIT
        return hash(str(self))

    @staticmethod
    def parse_prefix(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1
        if is_unary(s[0]):
            left, right = Formula.parse_prefix(s[1:])
            return [Formula(s[0], left), right]
        if s[0] == '(':  # binary cases
            right_par = get_idx_matching_r_par(s, '(', ')')
            residue = s[right_par + 1:]
            inner = s[1:right_par]
            l_op_idx, r_op_idx = get_index_of_binary_operator(inner)
            if l_op_idx == r_op_idx:  # cases &, |
                operator = inner[l_op_idx]
                left_formula = Formula.parse_prefix(inner[:l_op_idx])[0]
                right_formula = Formula.parse_prefix(inner[l_op_idx + 1:])[0]
            else:
                operator = inner[l_op_idx:r_op_idx + 1]
                left_formula = Formula.parse_prefix(inner[:l_op_idx])[0]
                right_formula = Formula.parse_prefix(inner[r_op_idx + 1:])[0]
            result = [Formula(operator, left_formula, right_formula), residue]
            return result

        if is_quantifier(s[0]):
            left_par = s.find('[')
            right_par = get_idx_matching_r_par(s, '[', ']')
            term = s[1:left_par]
            formula, residue = Formula.parse_prefix(s[left_par + 1:right_par])
            return [Formula(s[0], term, formula), s[right_par + 1:]]
        if is_variable(s[0]) or is_constant(s[0]) or is_function(s[0]):
            equal_idx = s.find('=')
            if equal_idx == -1:  # case not equality, just term
                return Term.parse_prefix(s)
            # case terms between equality
            left_term, left_residue = Term.parse_prefix(s[:equal_idx])
            right_term, right_residue = Term.parse_prefix(s[equal_idx + 1:])
            return [Formula('=', left_term, right_term), right_residue]

        if is_relation(s[0]):
            left_par = s.find('(')
            right_par = get_idx_matching_r_par(s, '(', ')')
            root = s[:left_par]
            inner = Term.parse_prefix(s[left_par + 1: right_par])
            args = [inner[0]] if inner[0] is not None else []
            residue = inner[1]
            while residue:
                left, right = Term.parse_prefix(residue)
                residue = right
                args.append(left)
            res = [Formula(root, args), s[right_par + 1:]]
            return res

    @staticmethod
    def parse(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3

    def substitute_variables(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the free occurrences of each variable v that appears in the
            dictionary substitution_map are replaced with the term
            substitution_map[v] """
        for variable in substitution_map:
            assert is_variable(variable) and \
                   type(substitution_map[variable]) is Term
        # Task 9.2

    def substitute_constants(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            the occurrences of each constant c that appears in the dictionary
            substitution_map are replaced with the term substitution_map[v] """
        for constant in substitution_map:
            assert is_constant(constant) and \
                   type(substitution_map[constant]) is Term
        # Ex12

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.5
