""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/functions.py """

from predicates.syntax import *
from predicates.semantics import *
from predicates.util import *
from copy import deepcopy
from itertools import product
from collections import deque


def replace_functions_with_relations_in_model(model):
    """ Return a new model obtained from the given model by replacing every
        function meaning with the corresponding relation meaning (i.e.,
        (x1,...,xn) is in the meaning if and only if x1 is the output of the
        function meaning for the arguments x2,...,xn), assigned to a relation
        with the same name as the function, except that the first letter is
        capitalized """
    assert type(model) is Model
    # Task 8.2
    new_meaning = {}
    for k, v in model.meaning.items():
        if not is_function(k):
            new_meaning[k] = v

        else:
            new_relation_name = k[0].upper() + k[1:]

            new_values = []
            for source, target in v.items():
                new_values.append((target,) + source)

            new_meaning[new_relation_name] = set(new_values)

    return Model(model.universe, new_meaning)


def verify_model_is_original(original_model: Model):
    functions = [f for f in original_model.meaning if is_function(f)]
    aritys = [len(list(original_model.meaning[f].keys())[0]) for f in functions]

    for f, arity in zip(functions, aritys):
        all_arg_combinations = list(product(original_model.universe, repeat=arity))
        for args in all_arg_combinations:
            if original_model.meaning[f].get(args) is None:
                return False
    return True


def replace_relations_with_functions_in_model(model, original_functions):
    """ Return a new model original_model with function names
        original_functions such that:
        model == replace_functions_with_relations_in_model(original_model)
        or None if no such original_model exists """
    assert type(model) is Model
    # Task 8.3
    new_meaning = {}
    for k, v in model.meaning.items():
        new_function_name = k[0].lower() + k[1:]
        if not is_relation(k) or new_function_name not in original_functions:
            new_meaning[k] = v

        else:
            new_function_values = {}
            for value in v:
                if new_function_values.get(value[1:]) is not None:  # verify each key has exactly one value
                    return None
                new_function_values[value[1:]] = value[0]
            new_meaning[new_function_name] = new_function_values

    original_model = Model(model.universe, new_meaning)

    # verify function gets all possible keys
    return original_model if verify_model_is_original(original_model) else None


def compile_term_helper(f: Term, steps: list):
    # if all(not is_function(g.root) for g in f.arguments):
    #     new_var = Term(next(fresh_variable_name_generator))
    #     step = Formula('=', new_var, f)
    #     steps.append(step)
    #     return new_var

    list_inner_new_args = []
    for g in f.arguments:
        if not is_function(g.root):
            list_inner_new_args.append(g)
        else:
            z = compile_term_helper(g, steps)
            list_inner_new_args.append(z)

    new_var = Term(next(fresh_variable_name_generator))
    steps.append(Formula('=', new_var, Term(f.root, list_inner_new_args)))
    return new_var


def compile_term(term):
    """ Return a list of steps that result from compiling the given term,
        whose root is a function invocation (possibly with nested function
        invocations down the term tree). Each of the returned steps is a
        Formula of the form y=f(x1,...,xk), where the y is a new variable name
        obtained by calling next(fresh_variable_name_generator) (you may assume
        that such variables do not occur in the given term), f is a
        single function invocation, and each of the xi is either a constant or
        a variable. The steps should be ordered left-to-right between the
        arguments, and within each argument, the computation of a variable
        value should precede its usage. The left-hand-side variable of the last
        step should evaluate to the value of the given term """
    assert type(term) is Term and is_function(term.root)
    # Task 8.4
    steps = []
    compile_term_helper(term, steps)
    return steps


def get_new_relation_from_equality(equality: Formula):
    z = equality.first
    old_func = equality.second
    old_func_name = old_func.root
    new_name = old_func_name[0].upper() + old_func_name[1:]
    return Formula(new_name, [z] + old_func.arguments)


def create_quantify_implies(all_steps: deque, new_R: Formula):
    if not all_steps:
        return new_R
    head = all_steps.popleft()
    z = head.first
    replaced_func = get_new_relation_from_equality(head)
    if not all_steps:
        rhs_implies = new_R
    else:
        rhs_implies = create_quantify_implies(all_steps, new_R)
    inner_formula = Formula('->', replaced_func, rhs_implies)
    return Formula('A', z.root, inner_formula)


def replace_functions_with_relations_in_formula_helper(formula: Formula):
    if is_equality(formula.root):
        phi_1 = formula.first
        phi_2 = formula.second
        if is_function(phi_1.root):
            phi_1_steps = compile_term(phi_1)
        else:
            phi_1_steps = []
        if is_function(phi_2.root):
            phi_2_steps = compile_term(phi_2)
        else:
            phi_2_steps = []

        lhs = phi_1_steps[-1].first if phi_1_steps else phi_1
        rhs = phi_2_steps[-1].first if phi_2_steps else phi_2
        new_R = Formula('=', lhs, rhs)
        return create_quantify_implies(deque(phi_1_steps + phi_2_steps), new_R)

    elif is_relation(formula.root):
        all_steps = []
        for term in formula.arguments:
            steps = compile_term(term) if is_function(term.root) else [term]
            all_steps.append(steps)

        new_args = [steps[-1].first if is_equality(steps[-1].root) else steps[-1] for steps in all_steps]
        new_R = Formula(formula.root, new_args)

        all_steps = [step for steps in all_steps for step in steps if is_equality(step.root)]  # flatten out
        return create_quantify_implies(deque(all_steps), new_R)

    elif is_unary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula_helper(formula.first))
    elif is_binary(formula.root):
        return Formula(formula.root,
                       replace_functions_with_relations_in_formula_helper(formula.first),
                       replace_functions_with_relations_in_formula_helper(formula.second))
    elif is_quantifier(formula.root):
        return Formula(formula.root, formula.variable,
                       replace_functions_with_relations_in_formula_helper(formula.predicate))


def replace_functions_with_relations_in_formula(formula):
    """ Return a function-free analog of the given formula. Every k-ary
        function that is used in the given formula should be replaced with a
        k+1-ary relation with the same name except that the first letter is
        capitalized (e.g., the function plus(x,y) should be replaced with the
        relation Plus(z,x,y) that stands for z=plus(x,y)). (You may assume
        that such relation names do not occur in the given formula, which
        furthermore does not contain any variables names starting with z.) The
        returned formula need only be equivalent to the given formula for
        models where each new relations encodes a function, i.e., is guaranteed
        to have single possible value for the first relation argument for every
        k-tuple of the other arguments """
    assert type(formula) is Formula
    # Task 8.5
    return replace_functions_with_relations_in_formula_helper(formula)


def replace_functions_with_relations_in_formulae(formulae):
    """ Return a list of function-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain function
        invocations. This equivalence is in the following sense:
        for every model of the given formulae,
        replace_functions_with_relations_in_model(model) should be a model
        of the returned formulae, and for every model of the returned formulae,
        replace_relations_with_functions_in_model(model) should be a model
        of the given formulae. Every k-ary function that is used in the given
        formulae should be replaced with a k+1-ary relation with the same name
        except that the first letter is capitalized (e.g., the function
        plus(x,y) should be replaced with the relation Plus(z,x,y) that stands
        for z=plus(x,y)). (You may assume that such relation names do not occur
        in the given formulae, which furthermore does not contain any variables
        names starting with z.) The returned list should have one formula for
        each formula in the given list, as well as one additional formula for
        every relation that replaces a function name from the given list """
    for formula in formulae:
        assert type(formula) is str
    # task 8.6


def replace_equality_with_SAME(formulae):
    """ Return a list of equality-free formulae (as strings) that is equivalent
        to the given formulae list (also of strings) that may contain the
        equality symbol. Every occurrence of equality should be replaced with a
        matching instantiation of the relation SAME, which you may assume
        does not occur in the given formulae. You may assume that the given
        formulae do not contain any function invocations. The returned list
        should have one formula for each formula in the given list, as well as
        additional formulae that ensure that SAME is reflexive, symmetric,
        transitive, and respected by all relations in the given formulae """
    for formula in formulae:
        assert type(formula) is str
    # Task 8.7


def add_SAME_as_equality(model):
    """ Return a new model obtained from the given model by adding the relation
        SAME that behaves like equality """
    assert type(model) is Model
    # Task 8.8


def make_equality_as_SAME(model):
    """ Return a new model where equality is made to coincide with the
        reflexive, symmetric, transitive, and respected by all relations,
        relation SAME in the the given model. The requirement is that for every
        model and every list formulae_list, if we take
        new_formulae=replace_equality_with_SAME(formulae) and
        new_model=make_equality_as_SAME(model) then model is a valid model
        of new_formulae if and only if new_model is a valid model of formulae.
        The universe of the returned model should correspond to the equivalence
        classes of the SAME relation in the given model. You may assume that
        there are no function meanings in the given model """
    assert type(model) is Model
    # Task 8.9
