""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.provers import MP, I1, I2, inverse_mp  # dont import *, come consts out of date
import operator

# Axiomatic Inference Rules (MP, I1, and I2 are imported from provers.py)
I3 = InferenceRule([], Formula.from_infix('(~p->(p->q))'))
NI = InferenceRule([], Formula.from_infix('(p->(~q->~(p->q)))'))

NN = InferenceRule([], Formula.from_infix('(p->~~p)'))

R = InferenceRule([], Formula.from_infix('((q->p)->((~q->p)->p))'))

AXIOMATIC_SYSTEM_IMPLIES_NOT = [MP, I1, I2, I3, NI, NN, R]

A = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
NA1 = InferenceRule([], Formula.from_infix('(~p->~(p&q))'))
NA2 = InferenceRule([], Formula.from_infix('(~q->~(p&q))'))

O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))

NO = InferenceRule([], Formula.from_infix('(~p->(~q->~(p|q)))'))

T = InferenceRule([], Formula.from_infix('T'))

NF = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, I3, NI, NN, A, NA1, NA2, O1, O2, NO, T, NF, R]


def prove_in_model_implies_not(formula: Formula, model: dict):
    """ Return a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT from the
        assumptions that all variables are valued as in model, with the
        assumptions being ordered alphabetically by the names of the variables.
        It is assumed that formula is true in model, and may only have the
        operators implies and not in it """
    # Task 6.1
    lines = []
    assumptions = [Formula(var) if val else Formula(NOT, Formula(var)) for var, val in sorted(model.items())]
    rules = AXIOMATIC_SYSTEM_IMPLIES_NOT
    return prove_in_model_implies_not_helper(formula, model, assumptions, rules, lines)


def update_lines(lines, new_lines):
    for line in new_lines:
        if line not in lines:
            if line.justification:
                for i in range(len(line.justification)):
                    line.justification[i] += len(lines)

    lines.extend(new_lines)


def prove_in_model_implies_not_helper(formula: Formula, model: dict, assumptions, rules, lines):


    # cases are (implication, negation of an implication, negation negation of φ)
    # Case φ=‘(φ1→φ2)’
    # if  eval(φ1) == F
    # use axiom I3 to prove
    # if eval (φ2) == T
    # use axiom I1 to prove
    statement = InferenceRule(assumptions, formula)

    if formula.root == IMPLIES:
        # print("Entering case for formula {0}".format(formula)) 
        if not evaluate(formula.first, model):
            # I3 : '(~p->(p->q))'
            p = formula.first
            not_p_proof = prove_in_model_implies_not_helper(Formula(NOT, p), model, assumptions, rules, lines)
            update_lines(lines, not_p_proof.lines)

            not_p = not_p_proof.statement.conclusion
            q = formula.second
            our_I3 = Formula(IMPLIES, not_p, Formula(IMPLIES, p, q))

            lines.append(DeductiveProof.Line(our_I3, 3, []))

            #     mp:
            lines.append(DeductiveProof.Line(our_I3.second, 0, [len(lines) - 2, len(lines) - 1]))
            proof = DeductiveProof(statement, rules, lines)
            return proof

        else:  # I1 : '(p->(q->p))'
            phi_1 = formula.first
            phi_2 = formula.second

            phi_2_proof = prove_in_model_implies_not_helper(phi_2, model, assumptions, rules, lines)
            update_lines(lines, phi_2_proof.lines)


            our_I1 = Formula(IMPLIES, phi_2, Formula(IMPLIES, phi_1, phi_2))
            lines.append(DeductiveProof.Line(our_I1, 1, []))

            # mp:
            lines.append(DeductiveProof.Line(our_I1.second, 0, [len(lines) - 2, len(lines) - 1]))
            proof = DeductiveProof(statement, rules, lines)
            return proof

    elif formula.root == NOT and formula.first.root == IMPLIES if hasattr(formula, 'first') else False:
        # Case φ=‘~(φ1→φ2)’
        # use axiom NI to prove. φ1 is True and φ2 is False
        # NI: '(p->(~q->~(p->q)))'
        # print("Entering case for formula {0}".format(formula)) 

        phi_1 = formula.first.first
        phi_2 = formula.first.second
        not_phi_2 = Formula(NOT, phi_2)

        phi_1_proof = prove_in_model_implies_not_helper(phi_1, model, assumptions, rules, lines)
        update_lines(lines, phi_1_proof.lines)
        phi_1_index = len(lines) - 1

        not_phi_2_proof = prove_in_model_implies_not_helper(not_phi_2, model, assumptions, rules, lines)
        update_lines(lines, not_phi_2_proof.lines)
        not_phi_2_index = len(lines) - 1

        # p, NI --> (p->(~q->~(p->q)))
        our_NI = Formula(IMPLIES, phi_1, Formula(IMPLIES, not_phi_2,
                                                 Formula(NOT, Formula(IMPLIES,
                                                                      phi_1,
                                                                      phi_2))))
        lines.append(DeductiveProof.Line(our_NI, 4, []))

        # mp 1
        lines.append(DeductiveProof.Line(our_NI.second, 0, [phi_1_index, len(lines) - 1]))

        # mp 2
        lines.append(DeductiveProof.Line(our_NI.second.second, 0, [not_phi_2_index, len(lines) - 1]))

        proof = DeductiveProof(statement, rules, lines)

        return proof

    elif formula.root == NOT and formula.first.root == NOT if hasattr(formula, 'first') else False:
        # Case φ=‘~~ψ’
        # use axiom NN to prove φ from ψ.
        # NN '(p->~~p)'
        # print("Entering case for formula {0}".format(formula)) 
        psi = formula.first.first
        psi_proof = prove_in_model_implies_not_helper(psi, model, assumptions, rules, lines)

        update_lines(lines, psi_proof.lines)

        our_NN = Formula(IMPLIES, psi, Formula(NOT, Formula(NOT, psi)))
        lines.append(DeductiveProof.Line(our_NN, 5, []))

        # mp: {psi, our_NN} ---> ~~psi
        lines.append(DeductiveProof.Line(our_NN.second, 0, [len(lines) - 2, len(lines) - 1]))
        proof = DeductiveProof(statement, rules, lines)
        return proof

    # Case not var
    elif formula.is_unary_formula():
        # print("Entering case for formula {0}".format(formula)) 
        lines = [DeductiveProof.Line(Formula(NOT, formula.first))]
        return DeductiveProof(statement, rules, lines)

    # case var
    elif formula.is_variable_formula():
        # print("Entering case for formula {0}".format(formula)) `
        lines = [DeductiveProof.Line(Formula(formula.root))]
        return DeductiveProof(statement, rules, lines)


def reduce_assumption(proof_true, proof_false):
    """ Return a proof of the same formula that is proved in both proof_true
        and proof_false, via the same inference rules used in both proof_true
        and proof_false, from the assumptions common to proof_true and
        proof_false. The first three of the inference rules in the given proofs
        are assumed to be M,I1,I2, any additional inference rules are assumed
        to have no assumptions, the inference rules in the given proofs are
        assumed to contain R, and the assumptions of both proofs are assumed to
        coincide, except for the last assumption, where that of proof_false is
        the negation of that of proof_true """
    # Task 6.2
    R_idx = proof_false.rules.index(AXIOMATIC_SYSTEM_IMPLIES_NOT[-1])
    lines = []
    phi_n = proof_true.statement.assumptions[-1]
    not_phi_n = proof_false.statement.assumptions[-1]
    phi_c = proof_true.statement.conclusion

    n_s_proof = inverse_mp(proof_true, phi_n)
    n_s = n_s_proof.statement.conclusion
    update_lines(lines, n_s_proof.lines)
    n_s_idx = len(lines) - 1

    not_n_s_proof = inverse_mp(proof_false, not_phi_n)
    not_n_s = not_n_s_proof.statement.conclusion
    update_lines(lines, not_n_s_proof.lines)
    not_n_s_idx = len(lines) - 1

    R_right = Formula(IMPLIES, not_n_s, phi_c)

    # our_R
    our_R = Formula(IMPLIES, n_s, R_right)
    lines.append(DeductiveProof.Line(our_R, R_idx, []))

    # MP1
    lines.append(DeductiveProof.Line(R_right, 0, [n_s_idx, len(lines) - 1]))

    # MP2
    lines.append(DeductiveProof.Line(phi_c, 0, [not_n_s_idx, len(lines) - 1]))

    assumptions = proof_false.statement.assumptions[:-1]
    rules = proof_false.rules
    statement = InferenceRule(assumptions, phi_c)

    return DeductiveProof(statement, rules, lines)


def ass_to_model(ass):
    model = {}
    for a in ass:
        if is_variable(a.root):
            model[a.root] = True
        else:
            model[a.first.infix()] = False
    keys = sorted(model.keys())
    model_sorted = {}
    for k in keys:
        model_sorted[k] = model[k]
    return model_sorted

def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    # Task 6.3
    models = list(all_models(formula.variables()))
    for model in models:
        if not evaluate(formula, model):
            return model

    models.reverse()
    iterations = len(formula.variables())
    proofs = [prove_in_model_implies_not(formula, model) for model in models]

    for i in range(iterations):
        upper_proofs = []

        while len(proofs) > 1:
            p2, p1 = proofs.pop(), proofs.pop()
            reduced_proof = reduce_assumption(p1, p2)
            upper_proofs.append(reduced_proof)

        proofs = upper_proofs
        proofs.reverse()

    return proofs[0]


def prove_in_model(formula, model):
    """ Return a proof of formula via AXIOMATIC_SYSTEM from the assumptions
        that all variables are valued as in model, with the assumptions being
        ordered alphabetically by the names of the variables. It is assumed
        that formula is true in model """
    # Task 6.4


def proof_or_counterexample(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM, or a model where
        formula does not hold """
    # Task 6.5


def proof_or_counterexample_for_inference(rule):
    """ Return either a proof of rule via AXIOMATIC_SYSTEM, or a model where
        rule does not hold """
    # Task 6.6


def model_or_inconsistent(formulae):
    """ Return either a model where all of formulae hold, or a list of two
        proofs, both from formulae via AXIOMATIC_SYSTEM, the first of some
        formula and the second of the negation of the same formula """
    # Task 6.7