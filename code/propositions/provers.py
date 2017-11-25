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
    '''
    4 cases:
    
    1. looking at assumption* then should create assumption -> assumption using task1 p->p, should create instance of it
        and use prove_instance to create this. Can create this at the start and add to new_lines (since this should
        appear once in the whole proof). In our for loop when we get the line that is the assumption we can continue.
    2. line is regular assumption != assumption: create instance using I1 and with MP infer the line. it is a regular assumption so, we can add it
        next line's conclusion should be last line's conclusion -> (assumption->last line's conclusion) (which looks like I1) and there is no
        justification. line 3 will use MP using line1 as p, line 2 will be p->q. conclusion will be assumption->line1 conclusion
        rule will be MP, justification will be line 1 and line2. to get idx of line 1,2 we can look at the latest lines in new lines.
        Notice that line1 will not use MP thus not have justification.
    3. If line has MP as rule: its conclusion (f13), rule MP, justification is [f7 and f7->13]. p is f7 and p->q is f7->f13
        we want to have last line as assumption*->f13. We can use I2 using assumption* as p, q is f7 and r is f13. create instance of
        first line using I2 then use MP twice on part 1 and on part 2 of instance created by I2.
        For the first MP we need part 1 and the whole inferring (that is the instnce created from I2) and part1 is true
        since f7->f13 is in justification. anything that is before oure line should have an assumption*->last line
        in new lines. so we should have assumption*->(f7->f13) and thus we conclude part2.
        
    4. in the last line we should rely on justifications. find idx of assumption*->f7 and use MP to get assumption*->f13
        
        create a new proof with new conclusion, no assumption and 
    '''
    new_assumptions = [a for a in proof.statement.assumptions if a != assumption]
    imply_self = prove_instance(prove_implies_self(), InferenceRule([], Formula(IMPLIES, assumption, assumption)))
    new_lines = imply_self.lines

    for line in proof.lines:
        if line.conclusion == assumption:
            continue
        elif line in new_assumptions or (line.rule != 0 if line.rule is not None else True):
            new_lines.append(line)
            line_by_I1_conc = Formula(IMPLIES, line.conclusion, Formula(IMPLIES, assumption, line.conclusion))
            line_by_I1 = DeductiveProof.Line(line_by_I1_conc, 1, [])
            new_lines.append(line_by_I1)
            line_by_MP_conc = Formula(IMPLIES, assumption, line.conclusion)
            line_by_MP = DeductiveProof.Line(line_by_MP_conc, 0, [len(new_lines) - 2, len(new_lines) - 1])
            new_lines.append(line_by_MP)
        else:
            p = assumption
            q = proof.lines[line.justification[0]].conclusion
            r = line.conclusion
            part_1 = Formula(IMPLIES, p, Formula(IMPLIES, q, r))
            part_2 = Formula(IMPLIES, Formula(IMPLIES, p, q), Formula(IMPLIES, p, r))
            line_by_I2 = DeductiveProof.Line(Formula(IMPLIES, part_1, part_2), 2, [])
            new_lines.append(line_by_I2)
            for i, l2 in enumerate(new_lines):
                if l2.conclusion == part_1:
                    break
            first_MP = DeductiveProof.Line(part_2, 0, [i, len(new_lines) - 1])
            new_lines.append(first_MP)

            for i, l2 in enumerate(new_lines):
                if l2.conclusion == Formula(IMPLIES, p, q):
                    break
            second_MP = DeductiveProof.Line(Formula(IMPLIES, p, r), 0, [i, len(new_lines) - 1])
            new_lines.append(second_MP)

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
