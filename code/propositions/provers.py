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
    statement = InferenceRule([], Formula(IMPLIES, Formula('p'), Formula('p')))
    rules = [MP, I1, I2]
    lines = [DeductiveProof.Line(Formula.from_infix('((p->((q->p)->p))->((p->(q->p))->(p->p)))'), 2, []),
             DeductiveProof.Line(Formula.from_infix('(p->((q->p)->p))'), 1, []),
             DeductiveProof.Line(Formula.from_infix('((p->(q->p))->(p->p))'), 0, [1, 0]),
             DeductiveProof.Line(Formula.from_infix('(p->(q->p))'), 1, []),
             DeductiveProof.Line(statement.conclusion, 0, [3, 2])
             ]
    return DeductiveProof(statement, rules, lines)


def case_imply_self(imply_self, new_lines_idx):
    lines = deepcopy(imply_self.lines)
    for line in lines:
        if line.justification is not None:
            line.justification = [new_lines_idx + j for j in line.justification]
    return lines


def case_not_mp_assump(line, new_lines_idx, assumption):
    line_by_I1_conc = Formula(IMPLIES, line.conclusion,
                              Formula(IMPLIES, assumption, line.conclusion))
    line_by_I1 = DeductiveProof.Line(line_by_I1_conc, 1, [])
    line_by_MP_conc = Formula(IMPLIES, assumption, line.conclusion)
    line_by_MP = DeductiveProof.Line(line_by_MP_conc, 0, [new_lines_idx, new_lines_idx + 1])
    return [line, line_by_I1, line_by_MP]


def case_mp_assump(lines, assumption, line, new_lines_idx, map_lines):
    p = assumption
    q = lines[line.justification[0]].conclusion
    r = line.conclusion
    part_1 = Formula(IMPLIES, p, Formula(IMPLIES, q, r))
    part_2 = Formula(IMPLIES, Formula(IMPLIES, p, q), Formula(IMPLIES, p, r))
    line_by_I2 = DeductiveProof.Line(Formula(IMPLIES, part_1, part_2), 2, [])
    first_MP = DeductiveProof.Line(part_2, 0, [map_lines[line.justification[1]], new_lines_idx])
    second_MP = DeductiveProof.Line(Formula(IMPLIES, p, r), 0, [map_lines[line.justification[0]], new_lines_idx + 1])
    return [line_by_I2, first_MP, second_MP]


def inverse_mp(proof, assumption):
    """ Return a valid deductive proof for '(assumption->conclusion)', where
        conclusion is the conclusion of proof, from the assumptions of proof
        except assumption, via MP,I1,I2 """
    # Task 5.3
    new_assumptions = [a for a in proof.statement.assumptions if a != assumption]
    imply_self = prove_instance(prove_implies_self(), InferenceRule([], Formula(IMPLIES, assumption, assumption)))
    imply_self_last_line_idx = len(imply_self.lines) - 1
    new_lines = imply_self.lines
    map_lines = {}
    new_lines_idx = len(new_lines)

    for i, line in enumerate(proof.lines):
        if line.conclusion == assumption:
            map_lines.update({i: imply_self_last_line_idx})
            continue
        elif line.rule is None or line.rule != 0:
            new_lines += case_not_mp_assump(line, new_lines_idx, assumption)
        else:
            new_lines += case_mp_assump(proof.lines, assumption, line, new_lines_idx, map_lines)
        new_lines_idx = len(new_lines)
        map_lines.update({i: new_lines_idx - 1})

    statement = InferenceRule(new_assumptions, new_lines[-1].conclusion)

    return DeductiveProof(statement, proof.rules, new_lines)


@lru_cache(maxsize=1)  # Cache the return value of prove_hypothetical_syllogism
def prove_hypothetical_syllogism():
    """ Return a valid deductive proof for '(p->r)' from the assumptions
        '(p->q)' and '(q->r)' via MP,I1,I2 """
    # Task 5.4
    statement = InferenceRule([Formula.from_infix('(p->q)'), Formula.from_infix('(q->r)')],
                              Formula(IMPLIES, Formula('p'), Formula('r')))
    rules = [MP, I1, I2]
    lines = [DeductiveProof.Line(Formula.from_infix('p')),
             DeductiveProof.Line(Formula.from_infix('(p->q)')),
             DeductiveProof.Line(Formula.from_infix('(q->r)')),
             DeductiveProof.Line(Formula.from_infix('q'), 0, [0, 1]),
             DeductiveProof.Line(Formula.from_infix('r'), 0, [3, 2])
             ]
    proof = DeductiveProof(statement, rules, lines)
    return inverse_mp(proof, Formula('p'))
