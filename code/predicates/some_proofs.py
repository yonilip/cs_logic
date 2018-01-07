""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/predicates/some_proofs.py """

from predicates.prover import *

def lovers_proof(print_as_proof_forms=False):
    """ Return a proof that from assumptions (in addition to Prover.AXIOMS):
        1) Everybody loves somebody and
        2) Everybody loves a lover
        derives the conclusion:
        Everybody loves everybody.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'],
                    'Ax[Az[Loves(z,x)]]', print_as_proof_forms)
    # Task 10.4
    step_1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step_2 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step_3 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step_1, 'x')
    step_4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step_2, 'x')
    step_5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step_4, 'z')
    step_6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step_5, 'y')
    step_7 = prover.add_existential_derivation('Loves(z,x)', step_3, step_6)
    step_8 = prover.add_ug('Az[Loves(z,x)]', step_7)
    step_9 = prover.add_ug('Ax[Az[Loves(z,x)]]', step_8)

    return prover.proof

def homework_proof(print_as_proof_forms=False):
    """ Return a proof that from the assumptions (in addition to Prover.AXIOMS):
        1) No homework is fun, and
        2) Some reading is homework
        derives the conclusion:
        Some reading is not fun.
        The Boolean flag print_as_proof_forms specifies whether the proof being
        constructed is to be printed in real time as it is being constructed """
    prover = Prover(['~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'],
                    'Ex[(Reading(x)&~Fun(x))]', print_as_proof_forms)
    # Task 10.5
    step_1 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step_2 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    step_3 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])', Prover.EI,
                                                {'R(v)': '(Homework(v)&Fun(v))', 'c': 'x'})
    step_4 = prover.add_tautological_inference('(~Ex[(Homework(x)&Fun(x))]->~(Homework(x)&Fun(x)))', [step_3])
    step_5 = prover.add_mp('~(Homework(x)&Fun(x))', step_1, step_4)
    step_6 = prover.add_tautological_inference('(Homework(x)->~Fun(x))', [step_5])
    step_7 = prover.add_instantiated_assumption('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])', Prover.EI,
                                                {'R(v)': '(Reading(v)&~Fun(v))', 'c': 'x'})

    step_8 = prover.add_tautological_inference('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])', [step_6, step_7])

    step_9 = prover.add_ug('Ax[((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])]', step_8)
    Q = 'Ex[(Reading(x)&~Fun(x))]'
    R_x = '(Homework(x)&Reading(x))'
    es_string = '((Ax[(' + R_x + '->' + Q + ')]&Ex[' + R_x + '])->' + Q + ')'
    step_10 = prover.add_instantiated_assumption(es_string, Prover.ES,
                                                 {'R(v)': '(Homework(v)&Reading(v))', 'Q()': Q})
    step_11 = prover.add_tautological_inference(Q, [step_9, step_2, step_10])

    return prover.proof

GROUP_AXIOMS = ['plus(0,x)=x', 'plus(minus(x),x)=0',
                'plus(plus(x,y),z)=plus(x,plus(y,z))']

def unique_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the group axioms (in addition to Prover.AXIOMS)
        and from the assumption a+c=a proves c=0. The Boolean flag
        print_as_proof_forms specifies whether the proof being constructed is
        to be printed in real time as it is being constructed """
    prover = Prover(GROUP_AXIOMS + ['plus(a,c)=a'], 'c=0', print_as_proof_forms)
    # Task 10.10
    zero_ax = prover.add_assumption('plus(0,x)=x')
    neg_ax = prover.add_assumption('plus(minus(x),x)=0')
    associativity_ax = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')

    step_1 = prover.add_assumption('plus(a,c)=a')
    step_2 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),a)', step_1, 'plus(minus(a),v)')

    step_3 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))', associativity_ax, {'x': 'minus(a)', 'y': 'a', 'z': 'c'})
    step_4 = prover.add_flipped_equality('plus(minus(a),plus(a,c))=plus(plus(minus(a),a),c)', step_3)
    step_5 = prover.add_flipped_equality('plus(minus(a),a)=plus(minus(a),plus(a,c))', step_2)
    step_6 = prover.add_chained_equality('plus(minus(a),a)=plus(plus(minus(a),a),c)', [step_5, step_4])
    step_7 = prover.add_flipped_equality('plus(plus(minus(a),a),c)=plus(minus(a),a)', step_6)

    step_8 = prover.add_free_instantiation('plus(minus(a),a)=0', neg_ax, {'x': 'a'})
    step_9 = prover.add_chained_equality('plus(plus(minus(a),a),c)=0', [step_7, step_8])
    step_10 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', step_8, 'plus(v,c)')
    step_11 = prover.add_free_instantiation('plus(0,c)=c', zero_ax, {'x': 'c'})
    step_12 = prover.add_chained_equality('plus(plus(minus(a),a),c)=c', [step_10, step_11])
    step_13 = prover.add_flipped_equality('0=plus(plus(minus(a),a),c)', step_9)
    step_14 = prover.add_chained_equality('0=c', [step_13, step_12])
    step_15 = prover.add_flipped_equality('c=0', step_14)
    return prover.proof

FIELD_AXIOMS = GROUP_AXIOMS + ['plus(x,y)=plus(y,x)', 'times(x,1)=x',
                               'times(x,y)=times(y,x)',
                               'times(times(x,y),z)=times(x,times(y,z))',
                               '(~x=0->Ey[times(y,x)=1])',
                               'times(x,plus(y,z))=plus(times(x,y),times(x,z))']


def multiply_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the field axioms (in addition to Prover.AXIOMS)
        proves 0*x=0. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(FIELD_AXIOMS, 'times(0,x)=0', print_as_proof_forms)
    # Task 10.11
    step_1 = prover.add_assumption('plus(0,x)=x')
    step_2 = prover.add_free_instantiation('plus(0,0)=0', step_1, {'x': '0'})
    step_3 = prover.add_substituted_equality('times(x,plus(0,0))=times(x,0)', step_2, 'times(x,v)')
    step_4 = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    step_5 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))', step_4, {'x':'x', 'y': '0', 'z': '0'})
    step_6 = prover.add_flipped_equality('times(x,0)=times(x,plus(0,0))', step_3)
    step_7 = prover.add_chained_equality('times(x,0)=plus(times(x,0),times(x,0))', [step_6, step_5])



    return prover.proof



PEANO_AXIOMS = ['(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))', 'times(x,0)=0',
                'times(x,s(y))=plus(times(x,y),x)',
                Schema('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])', 'R')]

def peano_zero_proof(print_as_proof_forms=False):
    """ Return a proof that from the Peano axioms (in addition to Prover.AXIOMS)
        proves 0+x=x. The Boolean flag print_as_proof_forms specifies whether
        the proof being constructed is to be printed in real time as it is
        being constructed """
    prover = Prover(PEANO_AXIOMS, 'plus(0,x)=x', print_as_proof_forms)
    # Task 10.12
    return prover.proof



COMPREHENSION_AXIOM = Schema('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]', {'R'})

def russell_paradox_proof(print_as_proof_forms=False):
    """ Return a proof that from the axiom schema of (unrestricted)
        comprehension (in addition to Prover.AXIOMS) proves the falsehood
        (z=z&~z=z). The Boolean flag print_as_proof_forms specifies whether the
        proof being constructed is to be printed in real time as it is being
        constructed """
    prover = Prover([COMPREHENSION_AXIOM], '(z=z&~z=z)', print_as_proof_forms)
    # Task 10.13
    conclusion = '(z=z&~z=z)'
    contradiction = '((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))'
    step0 = prover.add_instantiated_assumption('Ey[Ax[' + contradiction + ']]', COMPREHENSION_AXIOM,
                                               {'R(v)': '~In(v,v)'})

    contradiction_y = '((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))'
    ui_dict = {'R(v)': '((In(v,y)->~In(v,v))&(~In(v,v)->In(v,y)))', 'x': 'x', 'c': 'y'}
    ui_string = '(Ax[{c_x}]->{c_y})'.format(c_x=contradiction, c_y=contradiction_y)
    step1 = prover.add_instantiated_assumption(ui_string, Prover.UI, ui_dict)

    step2 = prover.add_tautology('({c_y}->{conc})'.format(c_y=contradiction_y, conc=conclusion))

    step3 = prover.add_tautological_inference('(Ax[{c_x}]->{conc})'.format(c_x=contradiction, conc=conclusion),
                                              [step1, step2])

    step4 = prover.add_existential_derivation(conclusion, step0, step3)

    return prover.proof