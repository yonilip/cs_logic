""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/semantics.py """

from itertools import product
from predicates.syntax import *


class Model:
    """ A model for first-order formulae: contains a universe - a set of
        elements, and a dictionary that maps every constant name to an element,
        every k-ary relation name to a set of k-tuples of elements, and every
        k-ary function name to a map from k-tuples of elements to an element """

    def __init__(self, universe, meaning):  # DONT EDIT
        assert type(universe) is set
        assert type(meaning) is dict
        self.universe = universe
        self.meaning = meaning

    def __repr__(self):  # DONT EDIT
        return 'Universe=' + str(self.universe) + '; Meaning=' + str(self.meaning)

    def evaluate_term(self, term, assignment={}):
        """ Return the value of the given term in this model, where variables   
            get their value from the given assignment """
        assert term.variables().issubset(assignment.keys())
        # Task 7.7
        if is_constant(term.root):
            return self.meaning[term.root]
        if is_function(term.root):
            args = []
            for arg in term.arguments:
                args.append(self.evaluate_term(arg, assignment))
            return self.meaning[term.root][tuple(args)]
        if is_variable(term.root):
            return assignment[term.root]

    def evaluate_formula(self, formula, assignment={}):
        """ Return the value of the given formula in this model, where
            variables that are free in the formula get their values from the
            given assignment """
        assert formula.free_variables().issubset(assignment.keys())
        # Task 7.8
        if is_relation(formula.root):
            args = []
            for arg in formula.arguments:
                args.append(self.evaluate_term(arg, assignment))
            return tuple(args) in self.meaning[formula.root]
        if is_equality(formula.root):
            return self.evaluate_term(formula.first, assignment) == \
                   self.evaluate_term(formula.second, assignment)
        if is_quantifier(formula.root):
            assignment = dict(assignment)
            results = []
            for elem in self.universe:
                assignment[formula.variable] = elem
                results.append(self.evaluate_formula(formula.predicate, assignment))
            if formula.root == 'A':
                return all(results)
            if formula.root == 'E':
                return any(results)

        if is_binary(formula.root):
            if formula.root == '&':
                return self.evaluate_formula(formula.first, assignment) and \
                       self.evaluate_formula(formula.second, assignment)
            if formula.root == '|':
                return self.evaluate_formula(formula.first, assignment) or \
                       self.evaluate_formula(formula.second, assignment)
            if formula.root == '->':
                return (not self.evaluate_formula(formula.first, assignment)) or \
                       self.evaluate_formula(formula.second, assignment)
        if is_unary(formula.root):
            return not self.evaluate_formula(formula.first, assignment)

    def is_model_of(self, formulae_repr):
        """ Return whether self a model of the formulae represented by the
            given list of strings. For this to be true, each of the formulae
            must be satisfied, if the formula has free variables, then it must
            be satisfied for every assignment of elements of the universe to
            the free variables """
        # Task 7.9
        for formula_str in formulae_repr:
            formula = Formula.parse(formula_str)
            free_vars = list(formula.free_variables())
            if free_vars:
                all_mappings = [zip(free_vars, item) for item in product(self.universe, repeat=len(free_vars))]
                for mapping in all_mappings:
                    assignment = dict((v, e) for v, e in mapping)
                    if not self.evaluate_formula(formula, assignment):
                        return False
            else:
                if not self.evaluate_formula(formula):
                    return False
        return True
