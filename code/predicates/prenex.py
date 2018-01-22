""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/prenex.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *
from predicates.util import *

ADDITIONAL_QUANTIFICATION_AXIOMS = [
    Schema('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))', {'x', 'R'}),
    Schema('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))', {'x', 'R'}),
    Schema('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))', {'x', 'R', 'Q'}),
    Schema('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))', {'x', 'R', 'Q'}),
    Schema('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))', {'x', 'R', 'Q'}),
    Schema('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))', {'x', 'R', 'Q'}),
    Schema('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))', {'x', 'R', 'Q'}),
    Schema('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))', {'x', 'R', 'Q'}),
    Schema('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))', {'x', 'R', 'Q'}),
    Schema('(((R(x)->Q(x))&(Q(x)->R(x)))->((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))', {'x', 'y', 'R', 'Q'}),
    Schema('(((R(x)->Q(x))&(Q(x)->R(x)))->((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))', {'x', 'y', 'R', 'Q'})]


def equivalence_of(formula1, formula2):
    """ Return the formula '((formula1->formula2)&(formula2->formula1))', which
        states the equivalence of the two given formulae """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def is_quantifier_free(formula):
    """ Return whether the given formula contains any quantifiers """
    assert type(formula) is Formula
    # Task 11.3.1
    root = formula.root
    if is_quantifier(root):
        return False
    elif is_unary(root):
        return is_quantifier_free(formula.first)
    elif is_binary(root):
        if not is_quantifier_free(formula.first) or not is_quantifier_free(formula.second):
            return False

    return True


def is_in_prenex_normal_form(formula):
    """ Return whether the given formula is in prenex normal form """
    assert type(formula) is Formula
    # Task 11.3.2
    if is_quantifier_free(formula):
        return True
    # Quantifier exists somewhere in formula
    else:
        if not is_quantifier(formula.root):
            return False
        else:
            return is_in_prenex_normal_form(formula.predicate)
    return True


def make_quantified_variables_unique_helper(formula, sub_map):
    if is_relation(formula.root) or is_equality(formula.root):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    elif is_unary(formula.root):
        inner_phi, inner_proof = make_quantified_variables_unique_helper(formula.first, sub_map)
        new_phi = Formula('~', inner_phi)

        old_conc = inner_proof.conclusion
        conclusion = equivalence_of(formula, new_phi)

        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        old_conc_step = prover.add_proof(old_conc, inner_proof)

        taut_step = prover.add_tautological_inference(str(conclusion), [old_conc_step])

        return new_phi, prover.proof

    elif is_binary(formula.root):
        old_left = formula.first
        old_right = formula.second
        inner_left_phi, inner_left_proof = make_quantified_variables_unique_helper(old_left, sub_map)
        inner_right_phi, inner_right_proof = make_quantified_variables_unique_helper(old_right, sub_map)

        new_phi = Formula(formula.root, inner_left_phi, inner_right_phi)
        old_left_conc = inner_left_proof.conclusion
        old_right_conc = inner_right_proof.conclusion
        conclusion = equivalence_of(formula, new_phi)

        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        old_left_conc_step = prover.add_proof(old_left_conc, inner_left_proof)
        old_right_conc_step = prover.add_proof(old_right_conc, inner_right_proof)

        taut_step = prover.add_tautological_inference(str(conclusion), [old_right_conc_step, old_left_conc_step])

        return new_phi, prover.proof



    elif is_quantifier(formula.root):
        inner_phi, inner_proof = make_quantified_variables_unique_helper(formula.predicate, sub_map)
        quantifier = formula.root
        old_var = formula.variable
        new_var = next(fresh_variable_name_generator)
        sub_map[old_var] = Term(new_var)

        inner_phi = inner_phi.substitute(sub_map)
        new_phi = Formula(quantifier, new_var, inner_phi)

        old_conc = inner_proof.conclusion
        conclusion = equivalence_of(formula, new_phi)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        old_conc_step = prover.add_proof(old_conc, inner_proof)

        if quantifier == 'A':
            axiom_idx = -2
        else:
            axiom_idx = -1
        R = old_conc.first.first
        Q = old_conc.first.second
        inst_assum_step = prover.add_instantiated_assumption(Formula('->', old_conc, conclusion),
                                                             ADDITIONAL_QUANTIFICATION_AXIOMS[axiom_idx],
                                                             {'x': old_var, 'y': new_var,
                                                              'R({v})'.format(v=old_var): str(R),
                                                              'Q({v})'.format(v=old_var): str(Q)})
        mp_step = prover.add_mp(conclusion, old_conc_step, inst_assum_step)

        return new_phi, prover.proof


def make_quantified_variables_unique(formula):
    """ Takes a formula and returns a pair: an equivalent formula with the
        exact same structure with the additional property that no two
        quantified variables, and no pair of quantified variable and free
        variable, in that formula have the same name, and a proof of the
        equivalence (i.e., a proof of equivalence_of(formula, returned_formula))
        from Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS.
        All quantified variable names should be replaced by new variable names,
        each generated using next(fresh_variable_name_generator) - you can
        assume that the original formula does not contain variable names that
        you have generated this way """
    assert type(formula) is Formula
    # Task 11.4
    return make_quantified_variables_unique_helper(formula, {})






def pull_out_quantifications_across_negation(formula):
    """ Takes a formula whose root is a negation, i.e., a formula of the form
        ~Q1x1[Q2x2[...Qnxn[inner_formula]...]] (where n>=0, each Qi is a
        quantifier, each xi is a variable name, and inner_formula does not
        start with a quantifier), and returns a pair:
        an equivalent formula of the form
        Q'1x1[Q'2x2[...Q'nxn[~inner_formula]...]] (where each Q'i is a
        quantifier, and where the xi's and inner_formula are the same as in the
        given formula), and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS """
    assert type(formula) == Formula and formula.root == '~'
    # Task 11.5


def pull_out_quantifications_from_left_across_binary_operator(formula):
    """ Takes a formula whose root is a binary operator, i.e., a formula of the
        form (Q1x1[Q2x2[...Qnxn[inner_first]...]]*second) (where * is a binary
        operator, n>=0, each Qi is a quantifier, each xi is a variable name,
        and inner_first does not start with a quantifier), and returns a pair:
        an equivalent formula of the form
        Q'1x1[Q'2x2[...Q'nxn[(inner_first*second)]...]] (where each Q'i is a
        quantifier, and where the operator *, the xi's, inner_first, and second
        are the same as in the given formula), and a proof of the equivalence
        (i.e., a proof of equivalence_of(formula, returned_formula)) from
        Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS. You may
        assume that no two quantified variables, and no pair of quantified
        variable and free variable, in formula have the same name """
    assert type(formula) == Formula and is_binary(formula.root)
    # Task 11.6.1


def pull_out_quantifications_from_right_across_binary_operator(formula):
    """ Takes a formula whose root is a binary operator, i.e., a formula of the
        form (first*Q1x1[Q2x2[...Qnxn[inner_second]...]]) (where * is a binary
        operator, n>=0, each Qi is a quantifier, each xi is a variable name,
        and inner_second does not start with a quantifier), and returns a pair:
        an equivalent formula of the form
        Q'1x1[Q'2x2[...Q'nxn[(first*inner_second)]...]] (where each Q'i is a
        quantifier, and where the operator *, the xi's, first, and inner_second
        are the same as in the given formula), and a proof of the equivalence
        (i.e., a proof of equivalence_of(formula, returned_formula)) from
        Prover.AXIOMS as well as from ADDITIONAL_QUANTIFICATION_AXIOMS. You may
        assume that no two quantified variables, and no pair of quantified
        variable and free variable, in formula have the same name """
    assert type(formula) == Formula and is_binary(formula.root)
    # Task 11.6.2


def pull_out_quantifications_across_binary_operator(formula):
    """ Takes a formula whose root is a binary operator, i.e., a formula of the
        form (Q1x1[Q2x2[...Qnxn[inner_first]...]]*
              P1y1[P2y2[...Pmym[inner_second]...]]) (where * is a binary
        operator, n>=0, m>=0, each Qi and each Pi is a quantifier, each xi and
        each yi is a variable name,  and neither inner_first nor inner_second
        starts with a quantifier), and returns a pair: an equivalent formula of
        the form
        Q'1x1[Q'2x2[...Q'nxn[P'1x1[P'2x2[...P'nxn[(inner_first*inner_second)]...]]]...]]
        (where each Q'i and each P'i is a quantifier, and where the operator *,
        the xi's, the yi's, inner_first, and inner_second are the same as in
        the given formula), and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS. You may assume that no two
        quantified variables, and no pair of quantified variable and free
        variable, in formula have the same name """
    assert type(formula) is Formula and is_binary(formula.root)
    # Task 11.7


def to_prenex_normal_form_from_unique_quantified_variables(formula):
    """ Takes a formula and returns a pair: an equivalent formula in prenex
        normal form, and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS. You may assume that no two
        quantified variables, and no pair of quantified variable and free
        variable, in formula have the same name """
    assert type(formula) is Formula
    # Task 11.8


def to_prenex_normal_form(formula):
    """ Takes a formula and returns a pair: an equivalent formula in prenex
        normal form, and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, retunred_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS. All quantified variable names
        should be replaced by new variable names, each generated using
        next(fresh_variable_name_generator) - you can assume that the original
        formula does not contain variable names that you have generated this
        way  """
    assert type(formula) is Formula
    # Task 11.9
