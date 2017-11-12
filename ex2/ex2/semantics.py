""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """

from propositions.syntax import *

def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    # Task 2.1

def all_models(variables):
    """ Return an iterator over all possible models over the variables in the
        given list of variables. The order of the models is lexicographic
        according to the order of the variables in the given list, where False
        precedes True """
    # Task 2.2

def truth_values(formula, models):
    """ Return a list of the truth values of the given formula in each model
        in the given list of models """
    # Task 2.3

def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    # Task 2.4

def print_truth_table(formula):
    """ Print the truth table of the given formula """
    # Task 2.5

def synthesize_for_model(model):
    """ Return a propositional formula that evaluates to True in the given
        model, and to False in any other model over the same variables """
    # Task 2.6
    
def synthesize(models, values):
    """ Return a propositional formula that has the given list of respective
        truth values in the given list of models """
    # Task 2.7

def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    #Task 4.2

def is_tautological_inference(rule):
    """ Return whether the given inference rule is a semantically correct
        implication of its assumptions """
    # Task 4.3
