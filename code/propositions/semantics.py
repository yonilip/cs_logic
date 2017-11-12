""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """
import itertools
import string

from propositions.syntax import *

non_pipe_chars = string.printable.replace('|', '')


def _evaluate_constant(s):
    if s == 'T':
        return True
    elif s == 'F':
        return False
    else:
        raise ValueError("Given string isnt boolean. It is {s}".format(s=s))


def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    # Task 2.1
    if formula.is_constant_formula():
        return _evaluate_constant(formula.root)
    if formula.is_variable_formula():
        return model[formula.root]
    if formula.is_unary_formula():
        return not evaluate(formula.first, model)
    if formula.is_binary_formula():
        if formula.root == AND:
            return evaluate(formula.first, model) and evaluate(formula.second, model)
        elif formula.root == OR:
            return evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == NAND:
            return not (evaluate(formula.first, model) and evaluate(formula.second, model))
        elif formula.root == NOR:
            return not (evaluate(formula.first, model) or evaluate(formula.second, model))
        elif formula.root == IMPLIES:
            return not evaluate(formula.first, model) or evaluate(formula.second, model)
        elif formula.root == IFF:
            first = evaluate(formula.first, model)
            second = evaluate(formula.second, model)
            return (first and second) or (not first and not second)
        else:
            raise Exception("Invalid binary formula\n"
                            "formula parts:"
                            "root: {0} , first: {1} , second: {2}"
                            .format(formula.root, formula.first, formula.second))
    if formula.is_ternary_formula():
        first = evaluate(formula.first, model)
        if first:
            return evaluate(formula.second, model)
        else:
            return evaluate(formula.third, model)
    else:
        raise Exception("Invalid formula. Formula is {0}".format(formula))


def all_models(variables):
    """ Return an iterator over all possible models over the variables in the
        given list of variables. The order of the models is lexicographic
        according to the order of the variables in the given list, where False
        precedes True """
    # Task 2.2
    bool_gen_ordered = itertools.product([False, True], repeat=len(variables))
    for bool_model in bool_gen_ordered:
        yield dict(zip(variables, bool_model))


def truth_values(formula, models):
    """ Return a list of the truth values of the given formula in each model
        in the given list of models """
    # Task 2.3
    result = []
    for model in models:
        result.append(evaluate(formula, model))
    return result


def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    # Task 2.4
    all_mods = all_models(list(formula.variables()))
    for model in all_mods:
        if not evaluate(formula, model):
            return False
    return True


def _print_header(sorted_vars, formula_as_str):
    s = ''
    for v in sorted_vars:
        s += '| {v} '.format(v=v)
    formula_format = '| {formula_as_str} |'.format(formula_as_str=formula_as_str)
    print(s + formula_format)
    separator = ''.join('-' if i in non_pipe_chars else '|' for i in s)
    separator += '|' + "-" * (len(formula_format) - 2) + "|"
    print(separator)


def _print_inner_table(sorted_vars, formula, formula_as_str):
    suffix_str = ' ' * (len(formula_as_str)) + '|'
    for model in all_models(sorted_vars):
        s = ''
        for var, val in sorted(model.items()):
            val = 'T' if val else 'F'
            s += '| {val} '.format(val=val) + ' ' * (len(var) - 1)
        evaluated_formula = 'T' if evaluate(formula, model) else 'F'
        s += '| {evaluated_formula}'.format(evaluated_formula=evaluated_formula) + suffix_str
        print(s)


def print_truth_table(formula):
    """ Print the truth table of the given formula """
    # Task 2.5
    formula_as_str = formula.infix()
    sorted_vars = sorted(list(formula.variables()))
    _print_header(sorted_vars, formula_as_str)
    _print_inner_table(sorted_vars, formula, formula_as_str)


def synthesize_for_model(model):
    """ Return a propositional formula that evaluates to True in the given
        model, and to False in any other model over the same variables """
    # Task 2.6
    '''
    if given false, return unary
    AND between all vars
    '''
    formula_stack = []
    for key, val in model.items():
        if val:
            formula_stack.append(Formula(key))
        else:
            formula_stack.append(Formula(NOT, Formula(key)))

        if len(formula_stack) > 1:
            first_formula = formula_stack.pop()
            second_formula = formula_stack.pop()
            and_formula = Formula(AND, first_formula, second_formula)
            formula_stack.append(and_formula)
    return formula_stack[0]


def synthesize(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models """
    # Task 2.7
    if True in values:
        true_stack = []
        for i in range(len(models)):
            if values[i]:
                true_formula = synthesize_for_model(models[i])
                true_stack.append(true_formula)
                if len(true_stack) > 1:
                    f1, f2 = true_stack.pop(), true_stack.pop()
                    true_stack.append(Formula(OR, f1, f2))
        return true_stack[0]
    else:
        formula_stack = []
        for model in models:
            formula_stack.append(synthesize_for_model(model))
            if len(formula_stack) > 1:
                f1, f2 = formula_stack.pop(), formula_stack.pop()
                formula_stack.append(Formula(AND, f1, f2))
        return formula_stack[0]


def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    # Task 4.2


def is_tautological_inference(rule):
    """ Return whether the given inference rule is a semantically correct
        implication of its assumptions """
    # Task 4.3
