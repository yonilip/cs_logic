""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

from propositions.syntax import *


def replace_var_for_formulae(formula: Formula, template: Formula, instantiation_map: dict):
    if template.is_variable_formula():
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
        self.assumptions = assumptions
        self.conclusion = conclusion

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
        # truth_vals = [InferenceRule._update_instantiation_map()]
        if len(self.assumptions) != len(rule.assumptions):
            return False
        if instantiation_map is None:
            instantiation_map = {}
        if not InferenceRule._update_instantiation_map(self.conclusion, rule.conclusion, instantiation_map):
            return False
        for i in range(len(self.assumptions)):
            if not InferenceRule._update_instantiation_map(self.assumptions[i],
                                                           rule.assumptions[i], instantiation_map):
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
            self.conclusion = conclusion
            self.rule = rule
            self.justification = justification

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
        self.statement = statement
        self.rules = rules
        self.lines = lines

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
        for i in range(line):
            if i in last_line.justification:
                assumptions.append(self.lines[i].conclusion)
        return InferenceRule(assumptions, last_line.conclusion)
        
    def is_valid(self):
        """ Return whether lines are a valid proof of statement from rules """
        # Task 4.6
        if self.statement.conclusion != self.lines[-1].conclusion:
            return False
        for i in range(len(self.lines)):
            _map = {}
            if self.lines[i].rule is None:
                continue
            instance_i = self.instance_for_line(i)
            if not instance_i.is_instance_of(self.rules[self.lines[i].rule], _map):
                return False
        return True


def instantiate(formula, instantiation_map):
    """ Return a formula obtained from the given formula by simultaneously
        substituting, for each variable v that is a key of instantiation_map,
        each occurrence v with the formula instantiation_map[v] """
    # Task 5.2.1

def prove_instance(proof, instance):
    """ Return a proof of the given instance of the inference rule that proof
        proves, via the same inference rules used by proof """
    # Task 5.2.1

def inline_proof(main_proof, lemma_proof):
    """ Return a proof of the inference rule that main_proof proves, via the
        inference rules used in main_proof except for the one proven by
        lemma_proof, as well as via the inference rules used in lemma_proof
        (with duplicates removed) """
    # Task 5.2.2
