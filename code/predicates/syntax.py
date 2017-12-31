""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/syntax.py """

from propositions.syntax import Formula as PropositionalFormula
from predicates.util import *
from copy import deepcopy

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
            return variables
        if is_variable(term.root):
            variables.append(term.root)
            return variables
        for arg in term.arguments:
            variables = Term.variables_helper(arg, variables)
        return variables

    def variables(self):
        """ Return the set of variables in this term """
        # Task 7.5
        variables = Term.variables_helper(self, [])
        return set(variables)

    @staticmethod
    def functions_helper(term, functions: list):
        if is_function(term.root):
            functions.append((term.root, len(term.arguments)))
            for arg in term.arguments:
                if is_function(arg.root):
                    functions = Term.functions_helper(arg, functions)
            return functions
        return functions

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this term """
        # Task 8.1.1
        functions = Term.functions_helper(self, [])
        return set(functions)

    @staticmethod
    def substitute_recurse(term, substitution_map):
        if is_constant(term.root) or is_variable(term.root):
            if term.root in substitution_map.keys():
                term = substitution_map[term.root]

        elif is_function(term.root):
            for i in range(len(term.arguments)):
                term.arguments[i] = Term.substitute_recurse(term.arguments[i], substitution_map)

        else:
            raise Exception("substitute_recurse called with wrong argument type")

        return term

    def substitute(self, substitution_map):
        """ Return a term obtained from this term where all the occurrences of
            each constant name or variable name element_name that appears as a
            key in the dictionary substitution_map are replaced with the term
            substitution_map[element_name] """
        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term
        # Task 9.1
        if not substitution_map:
            return deepcopy(self)
        return Term.substitute_recurse(deepcopy(self), substitution_map)


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
    def parse_same_prefix(s):
        """ Parse a first-order formula from the prefix of a given string.
            Return a pair: the parsed formula, and unparsed remainder of the
            string """
        # Task 7.4.1
        if is_unary(s[0]):
            left, right = Formula.parse_same_prefix(s[1:])
            return [Formula(s[0], left), right]
        if s[0] == '(':  # binary cases
            right_par = get_idx_matching_r_par(s, '(', ')')
            residue = s[right_par + 1:]
            inner = s[1:right_par]
            l_op_idx, r_op_idx = get_index_of_binary_operator(inner)
            if l_op_idx == r_op_idx:  # cases &, |
                operator = inner[l_op_idx]
                left_formula = Formula.parse_same_prefix(inner[:l_op_idx])[0]
                right_formula = Formula.parse_same_prefix(inner[l_op_idx + 1:])[0]
            else:
                operator = inner[l_op_idx:r_op_idx + 1]
                left_formula = Formula.parse_same_prefix(inner[:l_op_idx])[0]
                right_formula = Formula.parse_same_prefix(inner[r_op_idx + 1:])[0]
            result = [Formula(operator, left_formula, right_formula), residue]
            return result

        if is_quantifier(s[0]):
            left_par = s.find('[')
            right_par = get_idx_matching_r_par(s, '[', ']')
            term = s[1:left_par]
            formula, residue = Formula.parse_same_prefix(s[left_par + 1:right_par])
            return [Formula(s[0], term, formula), s[right_par + 1:]]
        if is_variable(s[0]) or is_constant(s[0]) or is_function(s[0]):
            equal_idx = s.find('=')
            if equal_idx == -1:  # case not equality, just term
                return Term.parse_same_prefix(s)
            # case terms between equality
            left_term, left_residue = Term.parse_prefix(s[:equal_idx])
            right_term, right_residue = Term.parse_prefix(s[equal_idx + 1:])
            return [Formula('SAME', [left_term, right_term]), right_residue]

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

    @staticmethod
    def parse_same(s):
        """ Return a first-order formula parsed from its given string
            representation """
        # Task 7.4.2
        return Formula.parse_same_prefix(s)[0]

    @staticmethod
    def free_variables_recurse(variables: list, term: Term, quantified_vars: list):
        if is_constant(term.root):
            pass
        elif is_variable(term.root):
            if term.root not in quantified_vars:
                variables.append(term.root)
        elif is_function(term.root):
            for arg in term.arguments:
                variables = Formula.free_variables_recurse(variables, arg, quantified_vars)
        return variables

    @staticmethod
    def formula_free_variables(formula, free_variables, quantified_vars):
        if is_relation(formula.root):
            for arg in formula.arguments:
                Formula.free_variables_recurse(free_variables, arg, quantified_vars)

        if is_binary(formula.root):
            Formula.formula_free_variables(formula.first, free_variables, quantified_vars)
            Formula.formula_free_variables(formula.second, free_variables, quantified_vars)

        if is_equality(formula.root):
            Formula.free_variables_recurse(free_variables, formula.first, quantified_vars)
            Formula.free_variables_recurse(free_variables, formula.second, quantified_vars)

        if is_unary(formula.root):
            Formula.formula_free_variables(formula.first, free_variables, quantified_vars)

        if is_quantifier(formula.root):
            quantified_vars.append(formula.variable)
            Formula.formula_free_variables(formula.predicate, free_variables, quantified_vars)

    def free_variables(self):
        """ Return the set of variables that are free in this formula """
        # Task 7.6
        free_variables = []
        Formula.formula_free_variables(self, free_variables, [])
        return set(free_variables)

    @staticmethod
    def functions_helper(formula, functions: list):
        if is_function(formula.root):
            functions.append((formula.root, len(formula.arguments)))
            for arg in formula.arguments:
                Formula.functions_helper(arg, functions)

        elif is_relation(formula.root):
            for term in formula.arguments:
                Term.functions_helper(term, functions)

        elif is_equality(formula.root) or is_binary(formula.root):
            Formula.functions_helper(formula.first, functions)
            Formula.functions_helper(formula.second, functions)

        elif is_unary(formula.root):
            Formula.functions_helper(formula.first, functions)

        if is_quantifier(formula.root):
            Formula.functions_helper(formula.predicate, functions)

    def functions(self):
        """ Return a set of pairs (function_name, arity) for all function names
            that appear in this formula """
        # Task 8.1.2
        functions = []
        Formula.functions_helper(self, functions)
        return set(functions)

    @staticmethod
    def relations_helper(formula, relations: list):
        if is_relation(formula.root):
            relations.append((formula.root, len(formula.arguments)))

        elif is_function(formula.root):
            for arg in formula.arguments:
                Formula.relations_helper(arg, relations)

        elif is_equality(formula.root) or is_binary(formula.root):
            Formula.relations_helper(formula.first, relations)
            Formula.relations_helper(formula.second, relations)

        elif is_unary(formula.root):
            Formula.relations_helper(formula.first, relations)

        if is_quantifier(formula.root):
            Formula.relations_helper(formula.predicate, relations)

    def relations(self):
        """ Return a set of pairs (relation_name, arity) for all relation names
            that appear in this formula """
        # Task 8.1.3
        relations = []
        Formula.relations_helper(self, relations)
        return set(relations)

    @staticmethod
    def substitute_helper(formula, substitution_map: dict, bound_vars: list):
        root = formula.root

        if is_relation(root):  # Populate self.root and self.arguments
            for i in range(len(formula.arguments)):
                if formula.arguments[i] not in bound_vars:
                    formula.arguments[i] = formula.arguments[i].substitute(substitution_map)

        elif is_equality(root):  # Populate self.first and self.second
            if formula.first not in bound_vars:
                formula.first = formula.first.substitute(substitution_map)
            if formula.second not in bound_vars:
                formula.second = formula.second.substitute(substitution_map)

        elif is_quantifier(root):  # Populate self.variable and self.predicate
            new_bound_vars = bound_vars + [formula.variable]
            formula.predicate = Formula.substitute_helper(formula.predicate, substitution_map, new_bound_vars)
        elif is_unary(root):  # Populate self.first
            formula.first = Formula.substitute_helper(formula.first, substitution_map, bound_vars)
        else:  # Populate self.first and self.second
            formula.first = Formula.substitute_helper(formula.first, substitution_map, bound_vars)
            formula.second = Formula.substitute_helper(formula.second, substitution_map, bound_vars)

        return formula

    def substitute(self, substitution_map):
        """ Return a first-order formula obtained from this formula where all
            occurrences of each constant name element_name and all *free*
            occurrences of each variable name element_name for element_name
            that appears as a key in the dictionary substitution_map are
            replaced with substitution_map[element_name] """
        for element_name in substitution_map:
            assert (is_constant(element_name) or is_variable(element_name)) and \
                   type(substitution_map[element_name]) is Term
        # Task 9.2
        if not substitution_map:
            return deepcopy(self)
        else:
            return Formula.substitute_helper(deepcopy(self), substitution_map, [])

    @staticmethod
    def get_and_update_new_name_if_needed(formula, name_map: dict):
        formula_key = str(formula)
        if formula_key in name_map.keys():
            return name_map[formula_key]
        else:
            new_name = next(fresh_variable_name_generator)
            name_map[formula_key] = new_name
            return new_name

    @staticmethod
    def skeletonize_formula(formula, name_map: dict):
        if is_relation(formula.root) or is_quantifier(formula.root):
            root = Formula.get_and_update_new_name_if_needed(formula, name_map)
            return PropositionalFormula(root)

        elif is_equality(formula.root):
            first = Formula.skeletonize_formula(formula.first, name_map)
            second = Formula.skeletonize_formula(formula.second, name_map)
            root = Formula.get_and_update_new_name_if_needed(formula, name_map)
            return PropositionalFormula(root, first, second)

        elif is_binary(formula.root):
            first = Formula.skeletonize_formula(formula.first, name_map)
            second = Formula.skeletonize_formula(formula.second, name_map)
            return PropositionalFormula(formula.root, first, second)

        elif is_unary(formula.root):
            first = Formula.skeletonize_formula(formula.first, name_map)
            return PropositionalFormula(formula.root, first)
        else:
            return None

    def propositional_skeleton(self):
        """ Return a PropositionalFormula that is the skeleton of this one.
            The variables in the propositional formula will have the names
            z1,z2,... (obtained by calling next(fresh_variable_name_generator)),
            starting from left to right """
        # Task 9.6
        skeleton = Formula.skeletonize_formula(self, {})
        if is_binary(skeleton.root):
            propositional_formula = PropositionalFormula(skeleton.root, skeleton.first, skeleton.second)
        elif is_unary(skeleton.root) or is_relation(skeleton.root):
            propositional_formula = PropositionalFormula(skeleton.root, skeleton.first)
        else:
            propositional_formula = PropositionalFormula(skeleton.root)
        return propositional_formula
