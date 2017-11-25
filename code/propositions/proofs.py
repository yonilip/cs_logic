""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

from copy import deepcopy
from propositions.syntax import *


def replace_var_for_formulae(formula: Formula, template: Formula, instantiation_map: dict):
    if template.is_variable_formula() or template.is_constant_formula():
        if template.root in instantiation_map.keys():
            return formula == instantiation_map[template.root]
        else:
            instantiation_map[template.root] = formula
        return True
    if formula.is_ternary_formula() and template.is_ternary_formula():
        first = replace_var_for_formulae(formula.first, template.first, instantiation_map)
        second = replace_var_for_formulae(formula.second, template.second, instantiation_map)
        third = replace_var_for_formulae(formula.third, template.third, instantiation_map)
        return all([first, second, third])
    if formula.is_binary_formula() and template.is_binary_formula() and formula.root == template.root:
        first = replace_var_for_formulae(formula.first, template.first, instantiation_map)
        second = replace_var_for_formulae(formula.second, template.second, instantiation_map)
        return all([first, second])
    if formula.is_unary_formula() and template.is_unary_formula():
        first = replace_var_for_formulae(formula.first, template.first, instantiation_map)
        return first


class InferenceRule:
    """ An inference rule, i.e., a list of zero or more assumed formulae, and
        a conclusion formula """

    def __init__(self, assumptions, conclusion):  # DONT EDIT
        assert type(conclusion) == Formula
        for assumption in assumptions:
            assert type(assumption) == Formula
        self.assumptions = assumptions  # list of Formulae
        self.conclusion = conclusion  # Formula

    def __eq__(self, other):  # DONT EDIT
        if (len(self.assumptions) != len(other.assumptions)):
            return False
        if self.conclusion != other.conclusion:
            return False
        for assumption1, assumption2 in zip(self.assumptions, other.assumptions):
            if assumption1 != assumption2:
                return False
        return True

    def __ne__(self, other):  # DONT EDIT
        return not self == other

    def __repr__(self):  # DONT EDIT
        return str([assumption.infix() for assumption in self.assumptions]) + \
               ' ==> ' + self.conclusion.infix()

    def variables(self):
        """ Return the set of atomic propositions (variables) used in the
            assumptions and in the conclusion of self. """
        # Task 4.1
        var_set = set()
        var_set.update(self.conclusion.vars)
        for assumption in self.assumptions:
            var_set.update(assumption.vars)
        return var_set

    def is_instance_of(self, rule, instantiation_map=None):
        """ Return whether there exist formulae f1,...,fn and variables
            v1,...,vn such that self is obtained by simultaneously substituting
            each occurrence of f1 with v1, each occurrence of f2 with v2, ...,
            in all of the assumptions of rule as well as in its conclusion.
            If so, and if instantiation_map is given, then it is (cleared and)
            populated with the mapping from each vi to the corresponding fi """
        # Task 4.4
        if len(self.assumptions) != len(rule.assumptions):
            return False
        if instantiation_map is None:
            instantiation_map = {}
        for i in range(len(self.assumptions)):
            if not InferenceRule._update_instantiation_map(self.assumptions[i],
                                                           rule.assumptions[i], instantiation_map):
                instantiation_map.clear()
                return False
        if not InferenceRule._update_instantiation_map(self.conclusion, rule.conclusion, instantiation_map):
            instantiation_map.clear()
            return False
        return True

    @staticmethod
    def _update_instantiation_map(formula: Formula, template: Formula, instantiation_map: dict):
        """ Return whether the given formula can be obtained from the given
            template formula by simultaneously and consistently substituting,
            for every variable in the given template formula, every occurrence
            of this variable with some formula, while respecting the
            correspondence already in instantiation_map (which maps from
            variables to formulae). If so, then instantiation_map is updated
            with any additional substitutions dictated by this matching. If
            not, then instantiation_map may be modified arbitrarily """
        # Task 4.4
        temp_dict = dict(instantiation_map)
        if replace_var_for_formulae(formula, template, temp_dict):
            instantiation_map.update(temp_dict)
            return True
        return False


class DeductiveProof:
    """ A deductive proof, i.e., a statement of an inference rule, a list of
        assumed inference rules, and a list of lines that prove the former from
        the latter """

    class Line:
        """ A line, i.e., a formula, the index of the inference rule whose
            instance justifies the formula from previous lines, and the list
            of indices of these previous lines """

        def __init__(self, conclusion, rule=None, justification=None):  # DONT EDIT
            self.conclusion = conclusion  # Formula
            self.rule = rule  # int
            self.justification = justification  # list of ints of previous rule

        def __repr__(self):  # DONT EDIT
            if (self.rule is None):
                return self.conclusion.infix()
            r = self.conclusion.infix() + ' (Inference Rule ' + str(self.rule)
            sep = ';'
            for i in range(len(self.justification)):
                r += sep + ' Assumption ' + str(i) + ': Line ' + \
                     str(self.justification[i])
                sep = ','
            r += '.)' if len(self.justification) > 0 else ')'
            return r

    def __init__(self, statement, rules, lines):  # DONT EDIT
        self.statement = statement  # InferenceRule
        self.rules = rules  # list of InferenceRules
        self.lines = lines  # list of Line

    def __repr__(self):  # DONT EDIT
        r = 'Proof for ' + str(self.statement) + ':\n'
        for i in range(len(self.rules)):
            r += 'Inference Rule ' + str(i) + ': ' + str(self.rules[i]) + '\n'
        for i in range(len(self.lines)):
            r += str(i) + ') ' + str(self.lines[i]) + '\n'
        return r

    def instance_for_line(self, line: int):
        """ Return the instantiated inference rule that corresponds to the
            given line number """
        # Task 4.5
        assumptions = []
        last_line = self.lines[line]
        if last_line.justification is not None:
            for i in last_line.justification:
                if i >= line:
                    # print(line)
                    return None
                assumptions.append(self.lines[i].conclusion)
        return InferenceRule(assumptions, last_line.conclusion)

    def is_valid(self):
        """ Return whether lines are a valid proof of statement from rules """
        # Task 4.6
        if self.statement.conclusion != self.lines[-1].conclusion:
            return False
        for i in range(len(self.lines)):
            _map = {}
            if self.lines[i].justification is not None:
                if len(self.lines[i].justification) > i:
                    return False
            if self.lines[i].rule is None:
                continue
            instance_i = self.instance_for_line(i)
            if not instance_i.is_instance_of(self.rules[self.lines[i].rule], _map):
                return False
        return True


def get_substituted_formula(formula, instantiation_map):
    if formula.is_variable_formula():
        if formula.root in instantiation_map.keys():
            formula = instantiation_map[formula.root]
        else:
            formula = list(instantiation_map.values())[0]
    elif formula.is_unary_formula():
        formula.first = get_substituted_formula(formula.first, instantiation_map)
    elif formula.is_binary_formula():
        formula.first = get_substituted_formula(formula.first, instantiation_map)
        formula.second = get_substituted_formula(formula.second, instantiation_map)
    elif formula.is_ternary_formula():
        formula.first = get_substituted_formula(formula.first, instantiation_map)
        formula.second = get_substituted_formula(formula.second, instantiation_map)
        formula.third = get_substituted_formula(formula.third, instantiation_map)
    elif formula.is_constant_formula():
        return formula
    return formula


def instantiate(formula, instantiation_map):
    """ Return a formula obtained from the given formula by simultaneously
        substituting, for each variable v that is a key of instantiation_map,
        each occurrence v with the formula instantiation_map[v] """
    # Task 5.2.1
    return get_substituted_formula(formula, instantiation_map)


def prove_instance(proof: DeductiveProof, instance: InferenceRule):
    """ Return a proof of the given instance of the inference rule that proof
        proves, via the same inference rules used by proof """
    # Task 5.2.1
    proof = deepcopy(proof)
    statement = instance
    new_lines = []
    _map = {}
    if not instance.is_instance_of(proof.statement, _map):
        print("Problem")
        return None
    for line in proof.lines:
        new_lines.append(DeductiveProof.Line(instantiate(line.conclusion, _map), line.rule, line.justification))
    return DeductiveProof(statement, proof.rules, new_lines)


def inline_proof(main_proof: DeductiveProof, lemma_proof: DeductiveProof):
    """ Return a proof of the inference rule that main_proof proves, via the
        inference rules used in main_proof except for the one proven by
        lemma_proof, as well as via the inference rules used in lemma_proof
        (with duplicates removed) """
    # Task 5.2.2
    idx_of_lemma_rule = main_proof.rules.index(lemma_proof.statement)
    new_rules = [rule for rule in main_proof.rules if str(rule) != str(lemma_proof.statement)]
    new_rules.extend([rule for rule in lemma_proof.rules if rule not in new_rules])
    main_proof_rule_mapping = {i: new_rules.index(rule) if rule in new_rules else None
                               for i, rule in enumerate(main_proof.rules)}
    lemma_rule_mapping = {i: new_rules.index(rule) if rule in new_rules else None
                          for i, rule in enumerate(lemma_proof.rules)}
    main_proof_line_mapping = {}
    new_lines = []
    for i, line in enumerate(main_proof.lines):
        if line.rule == idx_of_lemma_rule:
            inf_rule = InferenceRule([main_proof.lines[l_i].conclusion for l_i in line.justification]
                                     if line.justification else [], line.conclusion)
            adjusted_lemma = prove_instance(lemma_proof, inf_rule)
            lines_of_adjusted_lemma = adjusted_lemma.lines
            for j in lines_of_adjusted_lemma:
                j.rule = lemma_rule_mapping[j.rule] if j.rule is not None else None
                j.justification = [l + len(new_lines) for l in j.justification] if j.justification is not None else None
            new_lines.extend(lines_of_adjusted_lemma)
            main_proof_line_mapping[i] = len(new_lines) - 1
        else:
            line_rule = main_proof_rule_mapping[line.rule] if line.rule is not None else None
            new_justification = [main_proof_line_mapping[j] for j in line.justification] \
                if line.justification is not None else None
            new_lines.append(DeductiveProof.Line(line.conclusion, line_rule, new_justification))
            main_proof_line_mapping[i] = len(new_lines) - 1  # update line mapping
    return DeductiveProof(main_proof.statement, new_rules, new_lines)
