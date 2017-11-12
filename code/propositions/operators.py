""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/operators.py """

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula):
    """ Return an equivalent formula that has no operators beyond not, and, and
        or """
    # Task 3.3
    if formula.is_variable_formula():
        return formula
    root = formula.root
    if root == NAND:
        return Formula(NOT, Formula(AND, to_not_and_or(formula.first), to_not_and_or(formula.second)))
    elif root == NOR:
        return Formula(NOT, Formula(OR, to_not_and_or(formula.first), to_not_and_or(formula.second)))
    elif root == IMPLIES:
        return Formula(OR, Formula(NOT, to_not_and_or(formula.first)), to_not_and_or(formula.second))
    elif root == IFF:
        first = to_not_and_or(formula.first)
        second = to_not_and_or(formula.second)
        left_formula = Formula(AND, first, second)
        right_formula = Formula(AND, Formula(NOT, first), Formula(NOT, second))
        return Formula(OR, left_formula, right_formula)
    elif root == MUX:
        first = to_not_and_or(formula.first)  # chooser
        not_first = Formula(NOT, first)
        second = to_not_and_or(formula.second)
        third = to_not_and_or(formula.third)
        return Formula(OR, Formula(AND, first, second), Formula(AND, not_first, third))
    else:
        if formula.is_binary_formula():
            return Formula(root, to_not_and_or(formula.first), to_not_and_or(formula.second))
        elif formula.is_unary_formula():
            return Formula(root, to_not_and_or(formula.first))
        else:
            return formula


def to_not_and(formula):
    """ Return an equivalent formula that has no operators beyond not and and,
        and has no constants """
    # Task 3.4.1
    if formula.is_variable_formula():
        return formula
    root = formula.root
    if root == NOT:
        first = to_not_and(formula.first)
        return Formula(NOT, first)
    if root == AND:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        return Formula(AND, first, second)
    elif root == OR:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        return Formula(NOT, Formula(AND, Formula(NOT, first), Formula(NOT, second)))
    elif root == NAND:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        return Formula(NOT, Formula(AND, first, second))
    elif root == NOR:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        return Formula(AND, Formula(NOT, first), Formula(NOT, second))
    elif root == IMPLIES:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        return to_not_and(Formula(OR, Formula(NOT, first), second))
    elif root == IFF:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        lhs = Formula(AND, first, second)
        not_first = Formula(NOT, first)
        not_second = Formula(NOT, second)
        rhs = Formula(AND, not_first, not_second)
        return to_not_and(Formula(OR, lhs, rhs))
    elif root == MUX:
        first = to_not_and(formula.first)
        second = to_not_and(formula.second)
        third = to_not_and(formula.third)
        not_first = Formula(NOT, first)
        return to_not_and(Formula(OR, Formula(AND, first, second), Formula(AND, not_first, third)))
    else:
        raise ValueError("root not allowed: {0}".format(root))


def synthesize_not_and(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond not
        and and, and has no constants """
    # Task 3.4.2
    formula = synthesize(models, values)
    return to_not_and(formula)


def to_implies_false(formula):
    """ Return an equivalent formula that has no operators beyond implies, and
        has no constants beyond false """
    # Task 3.5.1
    if formula.is_variable_formula() or formula.is_constant_formula():
        return formula
    root = formula.root
    if root == IMPLIES:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        return Formula(IMPLIES, first, second)

    false_formula = Formula(F_str)
    if root == NOT:
        first = to_implies_false(formula.first)
        return Formula(IMPLIES, first, false_formula)
    if root == AND:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        return to_implies_false(Formula(NOT, Formula(NAND, first, second)))
    if root == OR:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        not_first = to_implies_false(Formula(NOT, first))
        return Formula(IMPLIES, not_first, second)
    if root == NAND:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        not_second = to_implies_false(Formula(NOT, second))
        return Formula(IMPLIES, first, not_second)
    if root == NOR:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        return to_implies_false(Formula(NOT, Formula(OR, first, second)))
    if root == IFF:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        side_1 = Formula(IMPLIES, first, second)
        side_2 = Formula(IMPLIES, second, first)
        return to_implies_false(Formula(AND, side_1, side_2))
    if root == MUX:
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        third = to_implies_false(formula.third)
        not_first = Formula(NOT, first)
        return to_implies_false(Formula(OR, Formula(AND, first, second), Formula(AND, not_first, third)))


def synthesize_implies_false(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        implies, and has no constants beyond false """
    # Task 3.5.2
    formula = synthesize(models, values)
    return to_implies_false(formula)


def to_nand(formula):
    """ Return an equivalent formula that has no operators beyond nand, and has
        no constants """
    # Task 3.6.1
    if formula.is_variable_formula():
        return formula
    root = formula.root
    if root == NAND:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        return Formula(NAND, first, second)
    if root == NOT:
        first = to_nand(formula.first)
        return Formula(NAND, first, first)
    if root == AND:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        return to_nand(Formula(NOT, Formula(NAND, first, second)))
    if root == OR:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        return Formula(NAND, Formula(NAND, first, first), Formula(NAND, second, second))
    if root == NOR:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        return to_nand(Formula(NOT, Formula(OR, first, second)))
    if root == IMPLIES:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        return to_nand(Formula(NAND, first, Formula(NOT, second)))
    if root == IFF:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        side_1 = to_nand(Formula(IMPLIES, first, second))
        side_2 = to_nand(Formula(IMPLIES, second, first))
        return to_nand(Formula(AND, side_1, side_2))
    if root == MUX:
        first = to_nand(formula.first)
        second = to_nand(formula.second)
        third = to_nand(formula.third)
        not_first = to_nand(Formula(NOT, first))
        return to_nand(Formula(OR, Formula(AND, first, second), Formula(AND, not_first, third)))


def synthesize_nand(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nand,
        and has no constants """
    # Task 3.6.2
    formula = synthesize(models, values)
    return to_nand(formula)

def to_nor(formula):
    """ Return an equivalent formula that has no operators beyond nor, and has
        no constants """
    # Task 3.7.1
    if formula.is_variable_formula():
        return formula
    root = formula.root
    if root == NOR:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        return Formula(NOR, first, second)
    if root == NOT:
        first = to_nor(formula.first)
        return Formula(NOR, first, first)
    if root == AND:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        return Formula(NOR, Formula(NOR, first, first), Formula(NOR, second, second))
    if root == OR:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        return to_nor(Formula(NOT, Formula(NOR, first, second)))
    if root == NAND:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        return to_nor(Formula(NOT, Formula(AND, first, second)))
    if root == IMPLIES:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        return to_nor(Formula(OR, Formula(NOT, first), second))
    if root == IFF:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        side_1 = to_nor(Formula(IMPLIES, first, second))
        side_2 = to_nor(Formula(IMPLIES, second, first))
        return to_nor(Formula(AND, side_1, side_2))
    if root == MUX:
        first = to_nor(formula.first)
        second = to_nor(formula.second)
        third = to_nor(formula.third)
        not_first = to_nor(Formula(NOT, first))
        return to_nor(Formula(OR, Formula(AND, first, second), Formula(AND, not_first, third)))


def synthesize_nor(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond nor,
        and has no constants """
    # Task 3.7.2
    formula = synthesize(models, values)
    return to_nor(formula)

def to_mux(formula):
    """ Return an equivalent formula that has no operators beyond mux """
    # Task 3.8.1
    if formula.is_variable_formula() or formula.is_constant_formula():
        return formula
    root = formula.root
    if root == MUX:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        third = to_mux(formula.third)
        return Formula(MUX, first, second, third)
    false_formula = Formula(F_str)
    true_formula = Formula(T_str)
    if root == NOT:
        first = to_mux(formula.first)
        return Formula(MUX, first, false_formula, true_formula)
    if root == AND:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return Formula(MUX, first, second, false_formula)
    if root == OR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return Formula(MUX, first, true_formula, second)
    if root == NAND:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return to_mux(Formula(NOT, Formula(AND, first, second)))
    if root == NOR:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return to_mux(Formula(NOT, Formula(OR, first, second)))
    if root == IMPLIES:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return Formula(MUX, first, second, true_formula)
    if root == IFF:
        first = to_mux(formula.first)
        second = to_mux(formula.second)
        return to_mux(Formula(AND, Formula(IMPLIES, first, second), Formula(IMPLIES, second, first)))

def synthesize_mux(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models, has no operators beyond
        mux """
    # Task 3.8.2
    formula = synthesize(models, values)
    return to_mux(formula)
