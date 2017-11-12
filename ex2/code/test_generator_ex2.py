from propositions.semantics import *
import random
import sys

def generate_model(variables):
    model = dict()
    for var in variables:
        if random.randint(0,1):
            model[var] = True
        else:
            model[var] = False
    return model


def task_1(formulas):
    with open('./results/task1', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            _ = formula.split('-')
            formula = _[0]
            formula = Formula.from_infix(formula)
            # Not soo good in security manners..
            model = eval(_[1].replace('\n', ''))
            result.write('(%d) Task_1 testing formula: %s evaluate result: %s\n' % (counter, formula.infix(), evaluate(formula, model)))
            result.write("model %s\n" % (sorted(list(model))))
            result.write("-------------------------------\n")
            counter += 1


def task_2(formulas):
    with open('./results/task2', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            variables = formula.variables()
            result.write('(%d) Task_2 testing formula: %s\n' % (counter, formula.infix()))
            models = sorted(all_models(list(variables)), key=lambda x: sorted(x.items()))
            # for i in range(len(models)):
            #     models[i]["id"] = i
            result.write("all_models: \n")
            for model in models:
                for key, value in sorted(model.items()):
                    result.write(str(key) + '=' + str(value) + ", ")
                result.write('\n')
            result.write("-------------------------------\n")
            counter += 1


def task_3(formulas):
    with open('./results/task3', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            variables = list(formula.variables())
            result.write('(%d) Task_3 testing formula: %s\n' % (counter, formula.infix()))
            result.write("truth_values %s\n" % (str(sorted(truth_values(formula, all_models(variables))))))
            result.write("-------------------------------\n")
            counter += 1


def task_4(formulas):
    with open('./results/task4', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_4 testing formula: %s\n' % (counter, formula.infix()))
            result.write("truth_values %s\n" % (str(is_tautology(formula))))
            result.write("-------------------------------\n")
            counter += 1


def task_5(formulas):
    with open('./results/task5', 'w') as result:
        old_target = sys.stdout
        sys.stdout = result
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_5 testing formula: %s\n' % (counter, formula.infix()))
            print_truth_table(formula)
            result.write("-------------------------------\n")
            counter += 1
        sys.stdout = old_target


def task_6(formulas):
    with open('./results/task6', 'w') as result:
        counter = 1
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            result.write('(%d) Task_6 testing formula: %s\n' % (counter, formula.infix()))
            models = all_models(list(formula.variables()))
            chosen_model = None
            for model in models:
                if len(model) != 0:
                    chosen_model = model
                    break
            if chosen_model is None:
                counter += 1
                result.write("-------------------------------\n")
                continue
            new_formula = synthesize_for_model(chosen_model)
            for model in models:
                if model == chosen_model and not evaluate(new_formula, model):
                    result.write('Fail\n')
                    continue
                elif model != chosen_model and evaluate(new_formula, model):
                    result.write('Fail\n')
                    continue
            result.write("-------------------------------\n")
            counter += 1


def task_7(formulas):
    with open('./results/task7', 'w') as result:
        counter = 1
        old_target = sys.stdout
        sys.stdout = result
        formulas.sort()
        for formula in formulas:
            formula = formula.replace('\n', '')
            formula = Formula.from_infix(formula)
            models = list(all_models(list(formula.variables())))
            result.write('(%d) Task_7 testing formula: %s Result: %s\n' % (counter, formula.infix(), truth_values(formula, models) == truth_values(synthesize(models, truth_values(formula, models)), models)))
            result.write("-------------------------------\n")
            counter += 1
        sys.__stdout__ = old_target


def run_tests():
    with open('./tests/hard_infix.text', 'r') as f_infix:
        formulas = f_infix.readlines()
        with open('./tests/task1_test') as task1_file:
            task_1(task1_file.readlines())
        task_2(formulas)
        task_3(formulas)
        task_4(formulas)
        task_5(formulas)
        task_6(formulas)
    with open('./tests/normal_infix.text') as f_infix:
        formulas = f_infix.readlines()
        task_7(formulas)


if __name__ == "__main__":
    run_tests()
