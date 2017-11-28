""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/tautology.py """

from propositions.syntax import *
from propositions.semantics import *
from propositions.proofs import *
from propositions.provers import MP,I1,I2,inverse_mp  # dont import *, come consts out of date

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

T  = InferenceRule([], Formula.from_infix('T'))

NF  = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, I3, NI, NN, A, NA1, NA2, O1, O2, NO, T, NF, R]

def prove_in_model_implies_not(formula: Formula, model: dict):
    """ Return a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT from the
        assumptions that all variables are valued as in model, with the
        assumptions being ordered alphabetically by the names of the variables.
        It is assumed that formula is true in model, and may only have the
        operators implies and not in it """
    # Task 6.1
    '''
    The assumptions in statement must be ordered alphabetically by the names of the variables
    
    '''
    # TODO if works, export to helper function better complexity
    assumptions = [Formula(var) if val else Formula(NOT, Formula(var)) for var, val in sorted(model.items())]
    statement = InferenceRule(assumptions, formula)
    rules = AXIOMATIC_SYSTEM_IMPLIES_NOT

    # cases are (implication, negation of an implication, negation negation of φ)
    # Case φ=‘(φ1→φ2)’
        # if  eval(φ1) == F
            # use axiom I3 to prove
        # if eval (φ2) == T
            # use axiom I1 to prove

    if formula.root == IMPLIES:
        if not evaluate(formula.first, model):
            return prove_instance(prove_in_model_implies_not(formula.first, model), I3)
        else:
            return prove_instance(prove_in_model_implies_not(formula.second, model), I1)
    # Case φ=‘~(φ1→φ2)’
        # use axiom NI to prove. φ1 is True and φ2 is False
    elif formula.root == NOT and formula.first.root == IMPLIES if hasattr(formula, 'first') else False:
        if evaluate(formula.first, model):
            return prove_instance(prove_in_model_implies_not(formula.first, model), NI)
        else:
            return prove_instance(prove_in_model_implies_not(formula.second, model), NI)

    # Case φ=‘~~ψ’
        # use axiom NN to prove φ from ψ.
        # NN '(p->~~p)'
    elif formula.root == NOT and formula.first.root == NOT if hasattr(formula, 'first') else False:
        inner_proof = prove_in_model_implies_not(formula.first.first, model)
        new_lines = inner_proof.lines
        conclusion = Formula(IMPLIES, formula.first.first, Formula(NOT, Formula(NOT, formula.first.first)))
        # conclusion = Formula(NOT, Formula(NOT, formula.first.first))

        new_lines.append(DeductiveProof.Line(conclusion, 5, [len(new_lines) - 1]))
        new_lines.append(DeductiveProof.Line(Formula(NOT, Formula(NOT, formula.first.first))))
        proof = DeductiveProof(statement, rules, new_lines)
        print(proof)
        # return prove_instance(proof, NN)
        return proof

    # Case not var
    elif formula.is_unary_formula():
        lines = [DeductiveProof.Line(Formula(NOT, formula.first))]
        return DeductiveProof(statement, rules, lines)

    # case var
    else:
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

def proof_or_counterexample_implies_not(formula):
    """ Return either a proof of formula via AXIOMATIC_SYSTEM_IMPLIES_NOT, or a
        model where formula does not hold. It is assumed that formula may only
        have the operators implies and not in it """
    # Task 6.3

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
