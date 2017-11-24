""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/provers.py """

from functools import lru_cache

from propositions.syntax import *
from propositions.proofs import *

# Tautological Inference Rules
MP = InferenceRule([Formula.from_infix('p'), Formula.from_infix('(p->q)')],
                   Formula.from_infix('q'))

I1 = InferenceRule([], Formula.from_infix('(p->(q->p))'))
I2 = InferenceRule([], Formula.from_infix('((p->(q->r))->((p->q)->(p->r)))'))

N = InferenceRule([], Formula.from_infix('((~p->~q)->(q->p))'))

A1 = InferenceRule([], Formula.from_infix('(p->(q->(p&q)))'))
A2 = InferenceRule([], Formula.from_infix('((p&q)->p)'))
A3 = InferenceRule([], Formula.from_infix('((p&q)->q)'))

O1 = InferenceRule([], Formula.from_infix('(p->(p|q))'))
O2 = InferenceRule([], Formula.from_infix('(q->(p|q))'))
O3 = InferenceRule([], Formula.from_infix('((p->r)->((q->r)->((p|q)->r)))'))

T = InferenceRule([], Formula.from_infix('T'))

F = InferenceRule([], Formula.from_infix('~F'))

AXIOMATIC_SYSTEM = [MP, I1, I2, N, A1, A2, A3, O1, O2, O3, T, F]


@lru_cache(maxsize=1)  # Cache the return value of prove_implies_self
def prove_implies_self():
    """ Return a valid deductive proof for '(p->p)' via MP,I1,I2 """
    # Task 5.1
    '''
    DeductiveProof members:
    self.statement = statement  # InferenceRule
    self.rules = rules  # list of InferenceRules
    self.lines = lines  # list of Line
    
    Line members:
    self.conclusion = conclusion  # Formula
    self.rule = rule  # int
    self.justification = justification  # list of ints of previous rule
    '''
    statement = InferenceRule([], Formula(IMPLIES, Formula('p'), Formula('p')))
    rules = [MP, I1, I2]
    lines = [DeductiveProof.Line(Formula.from_infix('((p->((q->p)->p))->((p->(q->p))->(p->p)))'), 2, []),
             DeductiveProof.Line(Formula.from_infix('(p->((q->p)->p))'), 1, []),
             DeductiveProof.Line(Formula.from_infix('((p->(q->p))->(p->p))'), 0, [1, 0]),
             DeductiveProof.Line(Formula.from_infix('(p->(q->p))'), 1, []),
             DeductiveProof.Line(statement.conclusion, 0, [3, 2])
             ]
    return DeductiveProof(statement, rules, lines)


def inverse_mp(proof, assumption):
    """ Return a valid deductive proof for '(assumption->conclusion)', where
        conclusion is the conclusion of proof, from the assumptions of proof
        except assumption, via MP,I1,I2 """
    # Task 5.3


@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    # Task 5.4
