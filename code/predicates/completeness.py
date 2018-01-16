""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/completeness.py """

from itertools import product, chain

from predicates.syntax import *
from predicates.semantics import *
from predicates.proofs import *
from predicates.prover import *
from predicates.prenex import *
from predicates.util import *


def is_closed(sentences, constants):
    """ Return whether the given set of sentences closed with respect to the
        given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    return is_primitively_closed(sentences, constants) and \
           is_universally_closed(sentences, constants) and \
           is_existentially_closed(sentences, constants)


def get_relations_and_const_helper(formula: Formula, relations: set):
    if is_relation(formula.root):
        relations.add((formula.root, tuple(term.root for term in formula.arguments)))

    elif is_function(formula.root):
        for arg in formula.arguments:
            get_relations_and_const_helper(arg, relations)

    elif is_equality(formula.root) or is_binary(formula.root):
        get_relations_and_const_helper(formula.first, relations)
        get_relations_and_const_helper(formula.second, relations)

    elif is_unary(formula.root) and is_relation(formula.first.root):
        relations.add(('~{}'.format(formula.first.root), tuple(term.root for term in formula.first.arguments)))

    if is_quantifier(formula.root):
        get_relations_and_const_helper(formula.predicate, relations)


def get_relations_and_constants(formula):
    '''
    :param formula:
    :return: set of relations and their consts where relation is R(*) or ~R(*)
    '''
    relations = set()
    get_relations_and_const_helper(formula, relations)
    return relations


def is_primitively_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        primitively closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.1.1
    relations_arity_set = {tup for sen in sentences for tup in sen.relations()}

    # Initialize dict
    relations_dict = dict()
    for relation, arity in relations_arity_set:
        relations_dict[relation, arity] = set()
        relations_dict['~{}'.format(relation), arity] = set()

    for sentence in sentences:
        relations_and_constants = get_relations_and_constants(sentence)
        for relation, constants_tuple in relations_and_constants:
            if any(c not in constants for c in constants_tuple):
                continue  # case not constant

            if relation + '(' + ','.join(constants_tuple) + ')' in sentences:  # add if relation is contained in S
                relations_dict[(relation, len(constants_tuple))].add(constants_tuple)

    for relation, arity in relations_arity_set:  # verify correctness
        if len(relations_dict[relation, arity]) + len(relations_dict['~{}'.format(relation), arity]) != \
                len(list(product(constants, repeat=arity))):
            return False
    return True


def is_universally_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        universally closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.1.2
    constant_terms = [Term(c) for c in constants]

    for sentence in sentences:
        if sentence.root == 'A':
            q_var = sentence.variable
            for c in constant_terms:
                sub_map = {q_var: c}
                sub_sent = sentence.predicate.substitute(sub_map)
                if sub_sent not in sentences:
                    return False
    return True


def is_existentially_closed(sentences, constants):
    """ Return whether the given set of prenex-normal-form sentences is
        existentially closed with respect to the given set of constant names """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.1.3
    constant_terms = [Term(c) for c in constants]

    for sentence in sentences:
        exists_c = False
        if sentence.root == 'E':
            q_var = sentence.variable
            for c in constant_terms:
                sub_map = {q_var: c}
                sub_sent = sentence.predicate.substitute(sub_map)
                if sub_sent in sentences:
                    exists_c = True
                    break
            if not exists_c:
                return False
    return True


def find_unsatisfied_quantifier_free_sentence(sentences, constants, model,
                                              unsatisfied):
    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, given a model whose universe is
        the given set of constant names, and given a sentence (which possibly
        contains quantifiers) from the given set that the given model does not
        satisfy, return a quantifier-free sentence from the given set that the
        given model does not satisfy. The set sentences may only be accessed
        using containment queries, i.e., using the "in" operator as in:
        if sentence in sentences """
    for constant in constants:
        assert is_constant(constant)
    assert type(model) is Model
    assert model.universe == constants
    assert type(unsatisfied) is Formula
    assert unsatisfied in sentences
    assert not model.evaluate_formula(unsatisfied)
    # Task 12.2

    constants_term = {Term(c) for c in constants}
    all_vars = []
    exists_vars = []
    inner_sent = unsatisfied
    while is_quantifier(inner_sent.root):
        if inner_sent.root == 'A':
            all_vars.append(inner_sent.variable)
        else:
            exists_vars.append(inner_sent.variable)
        inner_sent = inner_sent.predicate

    for all_tups in product(constants_term, repeat=len(all_vars + exists_vars)):

        sub_map = {z[0]: z[1] for z in zip(all_vars + exists_vars, all_tups)}
        sub_sent = inner_sent.substitute(sub_map)
        if not model.evaluate_formula(sub_sent):
            if sub_sent in sentences:
                return sub_sent


def get_primitives_helper(formula: Formula, relations: set):
    if is_relation(formula.root):
        # relations.add((formula.root, tuple(term.root for term in formula.arguments)))
        relations.add(Formula(formula.root, formula.arguments))

    elif is_function(formula.root):
        for arg in formula.arguments:
            get_primitives_helper(arg, relations)

    elif is_equality(formula.root) or is_binary(formula.root):
        get_primitives_helper(formula.first, relations)
        get_primitives_helper(formula.second, relations)

    elif is_unary(formula.root) and is_relation(formula.first.root):
        get_primitives_helper(formula.first, relations)

    if is_quantifier(formula.root):
        get_primitives_helper(formula.predicate, relations)


def get_primitives(quantifier_free):
    """ Return a set containing the primitive formulae (i.e., relation
        instantiations) that appear in the given quantifier-free formula. For
        example, if quantifier_free is '(R(c1,d)|~(Q(c1)->~R(c2,a))', then the
        returned set should be {'R(c1,d)', 'Q(c1)', 'R(c2,a)'} """
    assert type(quantifier_free) is Formula and \
           is_quantifier_free(quantifier_free)
    # Task 12.3.1
    primitives = set()
    get_primitives_helper(quantifier_free, primitives)
    return primitives


def model_or_inconsistent(sentences, constants):
    """ Given a set of prenex-normal-form sentences that is closed with respect
        to the given set of constants names, return either a model for the
        given set of sentences, or a proof of a contradiction from these
        sentences as assumptions """
    assert is_closed(sentences, constants)
    # Task 12.3.2
    all_relations_and_constants = set()
    for sentence in sentences:
        all_relations_and_constants.update(get_relations_and_constants(sentence))
    model_meaning = {c: c for c in constants}

    for relation, c_tup in all_relations_and_constants:
        if relation[0] != '~' and all(c in constants for c in c_tup):
            if not model_meaning.get(relation):
                model_meaning[relation] = set()
            model_meaning[relation].add(c_tup)

    model = Model(constants, model_meaning)

    unsatisfied = None
    for sentence in sentences:
        if not model.evaluate_formula(sentence):
            unsatisfied = sentence
            break
    if not unsatisfied:
        return model

    q_free_unsatisfied = find_unsatisfied_quantifier_free_sentence(sentences, constants, model, unsatisfied)
    primitives = get_primitives(q_free_unsatisfied)
    H = set()

    for sentence in sentences:
        for phi in primitives:
            not_phi = Formula('~', phi)
        if phi == sentence:
            H.add(str(phi))
            break
        if not_phi == sentence:
            H.add(str(phi))
            break
    # H.add(str(q_free_unsatisfied))
    # H.add(str(unsatisfied))

    conclusion = '({}&~{})'.format(str(q_free_unsatisfied), str(q_free_unsatisfied))

    prover = Prover(H, conclusion)
    lines = []
    for phi in H:
        lines.append(prover.add_assumption(phi))
    neg_line = prover.add_tautological_inference('~{}'.format(q_free_unsatisfied), lines)
    lines.append(neg_line)
    last_line = prover.add_tautological_inference(conclusion, lines)

    return prover.proof



def combine_contradictions(proof_true, proof_false):
    """ Given two proofs of contradictions from two lists of assumptions that
        differ only in the last assumption, where the last assumption of
        proof_false is the negation of that of proof_true, return a proof of a
        contradiction from only the assupmtions common to both proofs (without
        the last assumption of each proof). You can assume that each of the
        given proofs has Prover.AXIOMS (in order) as its first six
        axioms/assumptions, and that all of its axioms/assumptions are
        sentences """
    assert type(proof_true) is Proof and type(proof_false) is Proof
    assert proof_true.assumptions[:-1] == proof_false.assumptions[:-1]
    assert proof_false.assumptions[-1].templates == set()
    assert proof_true.assumptions[-1].templates == set()
    assert proof_false.assumptions[-1].formula == \
           Formula('~', proof_true.assumptions[-1].formula)
    # Task 12.4


def eliminate_universal_instance_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is an instantiation of the form 'formula(consatnt)'
        (for the given constant name) of the universal assumption of the form
        'Ax[formula(x)]' that immediately precedes it, return a proof of a
        contradiction from the same assumptions without the last (universally
        instantiated) one. You can assume that the given proof has
        Prover.AXIOMS (in order) as its first six axioms/assumptions, and that
        all of its axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "A"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})
    # Task 12.5


def universally_close(sentences, constants):
    """ Return a set of sentences that contains the given set of
        prenex-normal-form sentences and is universally closed with respect to
        the given set of constant names. For example, if sentences is the
        singleton {'Ax[Ay[R(x,y)]]'} and constants is {a,b}, then the returned
        set should be: {'Ax[Ay[R(x,y)]]', 'Ay[R(a,y)]', 'Ay[R(b,y)]', 'R(a,a)',
        'R(a,b)', 'R(b,a)', 'R(b,b)'} """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.6


def replace_constant(proof, constant, variable='zz'):
    """ Given a proof, a constant name that (potentially) appears in the
        assumptions and/or proof, and a variable name that does not appear
        anywhere in the proof or assumptions, return a "similar" (and also
        valid) proof where every occurrence of the given constant name in the
        assumptions and proof is replaced with the given variable name. You may
        assume that the given constant name only appears in the assumption
        schemata of the given proof as a non-template constant name """
    assert is_constant(constant)
    assert is_variable(variable)
    assert type(proof) is Proof
    # Task 12.7


def eliminate_existential_witness_assumption(proof, constant):
    """ Given a proof of a contradiction from a list of assumptions, where the
        last assumption is a witness of the form 'formula(constant)' (for the
        given constant name) for the existential assumption of the form
        'Ex[formula(x)]' that immediately precedes it, and where the given
        constant name does not appear anywhere else in the assumptions, return
        a proof of a contradiction from the same assumptions without the last
        (witness) one. You can assume that the given proof has Prover.AXIOMS
        (in order) as its first six axioms/assumptions, and that all of its
        axioms/assumptions are sentences """
    assert type(proof) is Proof
    assert proof.assumptions[-2].templates == set()
    assert proof.assumptions[-1].templates == set()
    assert proof.assumptions[-2].formula.root == "E"
    assert proof.assumptions[-1].formula == \
           proof.assumptions[-2].formula.predicate.substitute(
               {proof.assumptions[-2].formula.variable: Term(constant)})
    # Task 12.8


def existentially_close(sentences, constants):
    """ Return a pair of a set of sentences that contains the given set of
        prenex-normal-form sentences and a set of constant names that contains
        the given set of constant names, such that the returned set of
        sentences is universally closed with respect to the returned set of
        constants names. For example, if sentences is the singleton
        {'Ex[Ey[R(x,y)]]'} and constants is {a,b}, then the returned set could
        be: {'Ex[Ey[R(x,y)]]', 'Ey[R(c1,y)]', 'R(c1,c2)'}. New constant names
        should be generated using next(fresh_constant_name_generator) """
    for sentence in sentences:
        assert type(sentence) is Formula and is_in_prenex_normal_form(sentence)
    for constant in constants:
        assert is_constant(constant)
    # Task 12.9
