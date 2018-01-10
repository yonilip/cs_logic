""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/deduction.py """

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

def inverse_mp(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a conclusion from a list of assumptions/axioms that contains the given
        assumption as a simple formula (i.e., without any templates), where no
        step of the proof is a UG step over a variable that is free in the
        given assumption, and returns a proof of (assumption−>conclusion) from
        the same assumptions except assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.1
    # oa = original assumption
    oa = assumption
    prover = Prover(proof.assumptions,
                    '({oa}->{conclusion})'.format(oa=oa, conclusion=proof.conclusion),
                    print_as_proof_forms)

    oa_line = prover.add_tautology('({oa}->{oa})'.format(oa=oa))

    line_map = {}

    for i in range(len(proof.lines)):
        old_line = proof.lines[i]
        psi = old_line.formula

        # psi = original assumption
        if str(psi) == oa:
            line_map[i] = oa_line
            continue

        # cae assumption
        elif old_line.justification[0] == 'A':
            line = prover.add_instantiated_assumption(psi, prover.proof.assumptions[old_line.justification[1]], old_line.justification[2])

            line = prover.add_tautological_inference('({oa}->{psi})'.format(oa=oa, psi=str(psi)),
                                                                [oa_line, line])
            line_map[i] = line

        # case tautology
        elif old_line.justification[0] == 'T':
            line = prover.add_tautology('({oa}->{psi})'.format(oa=oa, psi=str(psi)))
            line_map[i] = line

        # case mp. psi = (a, a->b, b)
        elif old_line.justification[0] == 'MP':
            lines = [line_map[old_line.justification[1]], line_map[old_line.justification[2]]]
            oa__q = '({oa}->{psi})'.format(oa=oa, psi=str(psi))
            line = prover.add_tautological_inference(oa__q, lines)
            line_map[i] = line
            # TODO if fails here might need to get oa -> q

        # case UG
        elif old_line.justification[0] == 'UG':
            p = psi.predicate
            # Add UG
            oa__p_line = line_map[old_line.justification[1]]
            oa__p = prover.proof.lines[oa__p_line].formula
            x = psi.variable
            line = prover.add_ug('A{x}[{oa__p}]'.format(x=x, oa__p=str(oa__p)), oa__p_line)

            assert str(oa__p.first) == str(oa) and str(oa__p.second) == str(p)
            # Add US
            ug_str = str(prover.proof.lines[line].formula)
            us_str = '(A{x}[({oa}->{p})]->({oa}->A{x}[{p}]))'.format(ug=ug_str, x=x, oa=oa, p=str(p))
            substitution_map = {'Q': oa, 'R(v)': str(p.substitute({x: Term('v')})), 'x': x}
            # Schema: (Ax[(Q()->R(x))]->(Q()->Ax[R(x)])) [templates: {'Q', 'R', 'x'}]
            line = prover.add_instantiated_assumption(us_str, Prover.US, substitution_map)

        else:
            print(line)

            # print(prover.proof.lines[-1])
    return prover.proof

def proof_by_contradiction(proof, assumption, print_as_proof_forms=False):
    """ Takes a proof, whose first six assumptions/axioms are Prover.AXIOMS, of
        a contradiction (a formula whose negation is a tautology)  a list of
        assumptions/axioms that contains the given assumption as a simple
        formula (i.e., without any templates), where no step of the proof is a
        UG step over a variable that is free in the given assumption, and
        returns a proof of ~assumption from the same assumptions except
        assumption """
    assert type(proof) is Proof
    assert proof.is_valid()
    assert type(assumption) is str
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions[:len(Prover.AXIOMS)] == Prover.AXIOMS
    # Task 11.2
