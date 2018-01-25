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


def make_quantified_variables_unique_helper(formula):
    if is_relation(formula.root) or is_equality(formula.root):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    elif is_unary(formula.root):
        inner_phi, inner_proof = make_quantified_variables_unique_helper(formula.first)
        new_phi = Formula('~', inner_phi)

        old_conc = inner_proof.conclusion
        conclusion = equivalence_of(formula, new_phi)

        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        old_conc_step = prover.add_proof(old_conc, inner_proof)

        taut_step = prover.add_tautological_inference(conclusion, [old_conc_step])

        return new_phi, prover.proof

    elif is_binary(formula.root):
        old_left = formula.first
        old_right = formula.second
        inner_left_phi, inner_left_proof = make_quantified_variables_unique_helper(old_left)
        inner_right_phi, inner_right_proof = make_quantified_variables_unique_helper(old_right)

        new_phi = Formula(formula.root, inner_left_phi, inner_right_phi)
        old_left_conc = inner_left_proof.conclusion
        old_right_conc = inner_right_proof.conclusion
        conclusion = equivalence_of(formula, new_phi)

        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        old_left_conc_step = prover.add_proof(old_left_conc, inner_left_proof)
        old_right_conc_step = prover.add_proof(old_right_conc, inner_right_proof)

        taut_step = prover.add_tautological_inference(conclusion, [old_right_conc_step, old_left_conc_step])

        return new_phi, prover.proof

    elif is_quantifier(formula.root):
        inner_phi, inner_proof = make_quantified_variables_unique_helper(formula.predicate)
        quantifier = formula.root
        old_var = formula.variable
        new_var = next(fresh_variable_name_generator)
        sub_map = {}
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
    return make_quantified_variables_unique_helper(formula)


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
    if not is_unary(formula.root):
        return

    without_neg = formula.first

    if not is_quantifier(without_neg.root):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    without_outer_Q = without_neg.predicate
    neg_without_outer_Q = Formula('~', without_outer_Q)
    neg_inside, neg_inside_proof = pull_out_quantifications_across_negation(neg_without_outer_Q)
    quantifier = 'A' if without_neg.root == 'E' else 'E'
    ax_idx = 14 if quantifier == 'A' else 15
    var = without_neg.variable

    neg_with_new_Q = Formula(quantifier, var, neg_without_outer_Q)  # left in sicum equiv
    new_Q_neg_inside = Formula(quantifier, var, neg_inside)  # right in equiv in step 4
    equiv_step_4_formula = equivalence_of(neg_with_new_Q, new_Q_neg_inside)

    equiv_step_5_formula = equivalence_of(formula, neg_with_new_Q)

    equiv_step_6_formula = equivalence_of(formula, new_Q_neg_inside)  # also conclusion

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, equiv_step_6_formula)
    step_2_proof_line = prover.add_proof(neg_inside_proof.conclusion, neg_inside_proof)
    step_4_line = prover.add_instantiated_assumption(Formula('->', neg_inside_proof.conclusion, equiv_step_4_formula),
                                                     ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var, 'y': var,
                                                      'R({v})'.format(v=var): str(neg_without_outer_Q),
                                                      'Q({v})'.format(v=var): str(neg_inside)}
                                                     )
    mp_step_4 = prover.add_mp(equiv_step_4_formula, step_2_proof_line, step_4_line)

    ax_idx = 0 if ax_idx == 15 else 1
    step_5_line = prover.add_instantiated_assumption(equiv_step_5_formula, ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var,
                                                      'R({v})'.format(v=var): str(without_outer_Q)})

    last_line = prover.add_tautological_inference(equiv_step_6_formula, [mp_step_4, step_5_line])

    return new_Q_neg_inside, prover.proof


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

    if is_binary(formula.root) and not is_quantifier(formula.first.root):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    left_part = formula.first
    outer_Q = left_part.root
    var = left_part.variable
    inner_formula = left_part.predicate

    binary_formula_inner = Formula(formula.root, inner_formula, formula.second)
    binary_formula_tag, binary_formula_tag_proof = \
        pull_out_quantifications_from_left_across_binary_operator(binary_formula_inner)

    if formula.root == '->':
        outer_Q = 'A' if outer_Q == 'E' else 'E'

    ax_idx = 14 if outer_Q == 'A' else 15

    new_Q_binary_formula_inner = Formula(outer_Q, var, binary_formula_inner)
    new_Q_binary_formula_tag = Formula(outer_Q, var, binary_formula_tag)
    step_4_equiv = equivalence_of(new_Q_binary_formula_inner, new_Q_binary_formula_tag)

    step_5_equiv = equivalence_of(formula, new_Q_binary_formula_inner)
    step_6_equiv = equivalence_of(formula, new_Q_binary_formula_tag)

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, step_6_equiv)
    step_2_proof_line = prover.add_proof(binary_formula_tag_proof.conclusion, binary_formula_tag_proof)
    step_4_line = prover.add_instantiated_assumption(Formula('->', binary_formula_tag_proof.conclusion,
                                                             step_4_equiv),
                                                     ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var, 'y': var,
                                                      'R({v})'.format(v=var): str(binary_formula_inner),
                                                      'Q({v})'.format(v=var): str(binary_formula_tag)}
                                                     )
    mp_step_4 = prover.add_mp(step_4_equiv, step_2_proof_line, step_4_line)

    if formula.root == '&':
        ax_idx = 2 if outer_Q == 'A' else 3
    elif formula.root == '|':
        ax_idx = 6 if outer_Q == 'A' else 7
    else:  # root == '->'
        ax_idx = 10 if outer_Q == 'A' else 11

    step_5_line = prover.add_instantiated_assumption(step_5_equiv, ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var,
                                                      'R({v})'.format(v=var): str(inner_formula),
                                                      'Q()': str(formula.second)})

    last_line = prover.add_tautological_inference(step_6_equiv, [mp_step_4, step_5_line])
    return new_Q_binary_formula_tag, prover.proof


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
    if is_binary(formula.root) and not is_quantifier(formula.second.root):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    right_part = formula.second
    outer_Q = right_part.root
    var = right_part.variable
    inner_formula = right_part.predicate

    binary_formula_inner = Formula(formula.root, formula.first, inner_formula)
    binary_formula_tag, binary_formula_tag_proof = \
        pull_out_quantifications_from_right_across_binary_operator(binary_formula_inner)

    ax_idx = 14 if outer_Q == 'A' else 15

    new_Q_binary_formula_inner = Formula(outer_Q, var, binary_formula_inner)
    new_Q_binary_formula_tag = Formula(outer_Q, var, binary_formula_tag)
    step_4_equiv = equivalence_of(new_Q_binary_formula_inner, new_Q_binary_formula_tag)

    step_5_equiv = equivalence_of(formula, new_Q_binary_formula_inner)
    step_6_equiv = equivalence_of(formula, new_Q_binary_formula_tag)

    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, step_6_equiv)
    step_2_proof_line = prover.add_proof(binary_formula_tag_proof.conclusion, binary_formula_tag_proof)
    step_4_line = prover.add_instantiated_assumption(Formula('->', binary_formula_tag_proof.conclusion,
                                                             step_4_equiv),
                                                     ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var, 'y': var,
                                                      'R({v})'.format(v=var): str(binary_formula_inner),
                                                      'Q({v})'.format(v=var): str(binary_formula_tag)}
                                                     )
    mp_step_4 = prover.add_mp(step_4_equiv, step_2_proof_line, step_4_line)

    if formula.root == '&':
        ax_idx = 4 if outer_Q == 'A' else 5
    elif formula.root == '|':
        ax_idx = 8 if outer_Q == 'A' else 9
    else:  # root == '->'
        ax_idx = 12 if outer_Q == 'A' else 13

    step_5_line = prover.add_instantiated_assumption(step_5_equiv, ADDITIONAL_QUANTIFICATION_AXIOMS[ax_idx],
                                                     {'x': var,
                                                      'R({v})'.format(v=var): str(inner_formula),
                                                      'Q()': str(formula.first)})

    last_line = prover.add_tautological_inference(step_6_equiv, [mp_step_4, step_5_line])
    return new_Q_binary_formula_tag, prover.proof


def get_first_unquantified(formula):
    if not is_quantifier(formula.root):
        return str(formula)
    else:
        return get_first_unquantified(formula.predicate)


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
    first, second = formula.first, formula.second

    first_inner = get_first_unquantified(first)
    first_ending = str(first)[str(first).find(str(first_inner)) + len(str(first_inner)):]

    second_inner = get_first_unquantified(second)
    second_quantifiers = str(second)[:str(second).find(str(second_inner))]
    second_ending = str(second)[str(second).find(str(second_inner)) + len(str(second_inner)):]

    # Pull from left
    left_formula, left_proof = pull_out_quantifications_from_left_across_binary_operator(formula)
    first_inner_and_second = Formula.parse(get_first_unquantified(left_formula))

    # Pull from right
    right_formula, right_proof = pull_out_quantifications_from_right_across_binary_operator(first_inner_and_second)

    # Extract quantifiers in their correct order (order might change when pulling out from right/left)
    tmp = get_first_unquantified(left_formula)
    first_quantifiers_modified = str(left_formula)[:str(left_formula).find(str(tmp))]
    operator = str(formula.root)
    quantifiers_split = first_quantifiers_modified.split('[')[:-1]
    quantifiers_split.reverse()

    conclusion = first_quantifiers_modified + second_quantifiers + \
                 '(' + first_inner + operator + second_inner + ')' + \
                 first_ending + second_ending
    final_iff = str(equivalence_of(formula, Formula.parse(conclusion)))

    # Create prover
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, final_iff)

    step1 = prover.add_proof(left_proof.conclusion, left_proof)
    step2 = prover.add_proof(right_proof.conclusion, right_proof)

    # prove that adding quantifiers (one by one) is valid.
    psi = str(right_proof.conclusion.first.first)
    phi = str(right_proof.conclusion.first.second)
    quantifier_steps = []
    for q in quantifiers_split:
        quantifier = q[0]
        variable = q[1:]
        psi_quantified = '{q}[{psi}]'.format(psi=psi, q=q)
        phi_quantified = '{q}[{phi}]'.format(phi=phi, q=q)

        psi_iff_phi = equivalence_of(Formula.parse(psi), Formula.parse(phi))
        psi_quantified_iff_phi_quantified = equivalence_of(Formula.parse(psi_quantified), Formula.parse(phi_quantified))
        instantiated = '({psi_iff_phi}->{psi_quantified_iff_phi_quantified})'.format(psi_iff_phi=psi_iff_phi,
            psi_quantified_iff_phi_quantified=psi_quantified_iff_phi_quantified)

        # Use axiom 14 (All) or 15 (Exists)
        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[-2] if quantifier == 'A' else ADDITIONAL_QUANTIFICATION_AXIOMS[-1]
        sub_map = {'x': variable, 'y': variable,
                   'R({v})'.format(v=variable): psi,
                   'Q({v})'.format(v=variable): phi
                   }
        quantifier_steps.append(prover.add_instantiated_assumption(instantiated, axiom, sub_map))

        # Prepare for next quantifer
        psi = psi_quantified
        phi = phi_quantified

    finalStep = prover.add_tautological_inference(final_iff, [step1, step2] + quantifier_steps)

    return Formula.parse(conclusion), prover.proof


def to_prenex_normal_form_from_unique_quantified_variables(formula):
    """ Takes a formula and returns a pair: an equivalent formula in prenex
        normal form, and a proof of the equivalence (i.e., a proof of
        equivalence_of(formula, returned_formula)) from Prover.AXIOMS as well
        as from ADDITIONAL_QUANTIFICATION_AXIOMS. You may assume that no two
        quantified variables, and no pair of quantified variable and free
        variable, in formula have the same name """
    assert type(formula) is Formula
    # Task 11.8
    formulas_and_proofs = []
    if is_in_prenex_normal_form(formula):
        conclusion = equivalence_of(formula, formula)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
        prover.add_tautology(conclusion)
        return formula, prover.proof

    # case3: unary.
    # We will prove ~A<=>~B.
    elif formula.root == '~':
        # Send first recursively we got A<=>B as tup[0].
        not_a = formula
        b, proof_a_iff_b = to_prenex_normal_form_from_unique_quantified_variables(formula.first)
        a_iff_b = proof_a_iff_b.conclusion
        not_b = Formula('~', proof_a_iff_b.conclusion.first.second)

        # Send ~tup[0] (=~B) to task 5 got ~B<=>C.
        c, proof_notB_iff_c = pull_out_quantifications_across_negation(not_b)

        # We want to prove ~A<=>C
        not_a_iff_c = str(equivalence_of(not_a, c))
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, not_a_iff_c)

        a_iff_b_line = prover.add_proof(a_iff_b, proof_a_iff_b)

        notA_iff_notB = equivalence_of(not_a, not_b)
        t_line = prover.add_tautology('({a_iff_b}->{notA_iff_notB})'.format(a_iff_b=str(a_iff_b),
                                                                            notA_iff_notB=str(notA_iff_notB)))
        notA_iff_notB_line = prover.add_tautological_inference(str(notA_iff_notB), [a_iff_b_line, t_line])

        notB_iff_c_line = prover.add_proof(proof_notB_iff_c.conclusion, proof_notB_iff_c)

        notA_iff_c = equivalence_of(not_a, c)
        notA_iff_c_line = prover.add_tautological_inference(notA_iff_c, [notA_iff_notB_line, notB_iff_c_line])

        return c, prover.proof

    elif is_binary(formula.root):
        ac = formula
        a, c = formula.first, formula.second
        operator = formula.root

        # case4: binary. Send first recursively we got A<=>B,
        b, proof_a_iff_b = to_prenex_normal_form_from_unique_quantified_variables(a)

        # Send second recursively we got C<=>D.
        d, proof_c_iff_d = to_prenex_normal_form_from_unique_quantified_variables(c)

        # We will prove A*C<=>B*D (* is the binary operator).
        # Build formula from B and D - Formula(*,B,D), and send it to
        # task7. We got B*D<=>E.
        bd = Formula(operator, b, d)
        e, proof_bd_iff_e = pull_out_quantifications_across_binary_operator(bd)

        # We would like to prove: A*C<=>E
        conclusion = equivalence_of(ac, e)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)

        # PROVER MOTHAFACKA
        ab_line = prover.add_proof(proof_a_iff_b.conclusion, proof_a_iff_b)

        cd_line = prover.add_proof(proof_c_iff_d.conclusion, proof_c_iff_d)

        ac_bd = equivalence_of(ac, bd)
        ac_bd_line = prover.add_tautological_inference(ac_bd, [ab_line, cd_line])

        bd_e_line = prover.add_proof(proof_bd_iff_e.conclusion, proof_bd_iff_e)

        ac_e = equivalence_of(ac, e)
        ac_e_line = prover.add_tautological_inference(ac_e, [ac_bd_line, bd_e_line])

        return e, prover.proof

    # case is_quantifier(formula.root): (Tests didnt cover this)
    else:
        # case2: quantifier. Send predicate recursively we got A<=>B as tup[0].
        # use 14/15 axiom to prove: A<=>B => Ax[A]<=>Ax[B]
        b, proof_a_iff_b = to_prenex_normal_form_from_unique_quantified_variables(formula.predicate)

        a = formula.predicate
        a_quantified = formula
        b_quantified = Formula.parse(formula.root + formula.variable + '[' + str(b) + ']')
        conclusion = equivalence_of(a_quantified, b_quantified)
        prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)

        a_iff_b_line = prover.add_proof(proof_a_iff_b.conclusion, proof_a_iff_b)

        axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[-2] if formula.root == 'A' else ADDITIONAL_QUANTIFICATION_AXIOMS[-1]

        sub_map = {'x': formula.variable, 'y': formula.variable,
         'R({v})'.format(v=formula.variable): str(a),
         'Q({v})'.format(v=formula.variable): str(b)}
        inst_assum_step = prover.add_instantiated_assumption(Formula('->', proof_a_iff_b.conclusion, conclusion),
             axiom, sub_map)


        final_step = prover.add_tautological_inference(conclusion, [a_iff_b_line, inst_assum_step])

        return b_quantified, prover.proof


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
    unique_formula, unique_proof = make_quantified_variables_unique(formula)

    pnf, pnf_proof = to_prenex_normal_form_from_unique_quantified_variables(unique_formula)

    conclusion = equivalence_of(formula, pnf)
    prover = Prover(ADDITIONAL_QUANTIFICATION_AXIOMS, conclusion)
    unique_line = prover.add_proof(unique_proof.conclusion, unique_proof)
    pnf_line = prover.add_proof(pnf_proof.conclusion, pnf_proof)

    prover.add_tautological_inference(str(conclusion), [unique_line, pnf_line])

    return pnf, prover.proof