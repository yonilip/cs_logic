import random

BINARY_SYMBOLS = ['|', '&']

UNARY_SYMBOL = '~'

MIN_CHAR = 112

MAX_CHAR = 122


def generate_var():
    _1 = random.randint(0, 1)
    _2 = random.randint(0, 1)
    if _1:
        return chr(random.randint(MIN_CHAR, MAX_CHAR)) + str(random.randint(0, 10))
    else:
        if _2:
            return 'T'
        else:
            return 'F'


def generate_tests_infix(num_of_tests, max_length):
    assert num_of_tests > 0
    tests = []
    for i in range(num_of_tests):
        exp_len = random.randint(1, max_length)
        exp = generate_var()
        for j in range(exp_len):
            action = random.randint(1, 3)
            symbols_index = random.randint(0, 1)
            if action is 1:
                exp = UNARY_SYMBOL + exp
            elif action is 2:
                exp = '(' + exp + BINARY_SYMBOLS[symbols_index] + generate_var() + ')'
            else:
                exp = '((' + exp + BINARY_SYMBOLS[symbols_index] + generate_var() + ')'+ \
                      BINARY_SYMBOLS[(symbols_index+1)%2] + '(' + generate_var() + BINARY_SYMBOLS[symbols_index] +\
                      generate_var() + '))'
        tests.append(exp)
    return tests


def generate_tests_prefix(num_of_tests, max_length):
    assert num_of_tests > 0
    tests = []
    for i in range(num_of_tests):
        exp_len = random.randint(1, max_length)
        exp = generate_var()
        for j in range(exp_len):
            action = random.randint(1, 3)
            symbols_index = random.randint(0, 1)
            if action is 1:
                exp = UNARY_SYMBOL + exp
            elif action is 2:
                exp = BINARY_SYMBOLS[symbols_index] + exp + generate_var()
            else:
                exp = BINARY_SYMBOLS[(symbols_index + 1) % 2] + BINARY_SYMBOLS[symbols_index] + exp + generate_var() + \
                      BINARY_SYMBOLS[symbols_index] + generate_var() + generate_var()
        tests.append(exp)
    return tests


def generate_tests_variables(num_of_tests, max_length):
    assert num_of_tests > 0
    tests = []
    for i in range(num_of_tests):
        vars = set()
        exp_len = random.randint(1, max_length)
        exp = generate_var()
        if exp not in ['T', 'F']:
            vars.add(exp)
        for j in range(exp_len):
            action = random.randint(1, 3)
            symbols_index = random.randint(0, 1)
            if action is 1:
                exp = UNARY_SYMBOL + exp
            elif action is 2:
                var1 = generate_var()
                if var1 not in ['T', 'F']:
                    vars.add(var1)
                exp = '(' + exp + BINARY_SYMBOLS[symbols_index] + var1 + ')'
            else:
                var1 = generate_var()
                var2 = generate_var()
                var3 = generate_var()
                if var1 not in ['T', 'F']:
                    vars.add(var1)
                if var2 not in ['T', 'F']:
                    vars.add(var2)
                if var3 not in ['T', 'F']:
                    vars.add(var3)
                exp = '((' + exp + BINARY_SYMBOLS[symbols_index] + var1 + ')' + BINARY_SYMBOLS[(symbols_index+1)%2] + \
                      '(' + var2 + BINARY_SYMBOLS[symbols_index] + var3 + '))'
        tests.append((exp, vars))
    return tests

with open("./tests/easy_infix.text", 'w') as f:
    tests = generate_tests_infix(100, 1)
    f.write('\n'.join(tests))

with open("./tests/normal_infix.text", 'w') as f:
    tests = generate_tests_infix(200, 4)
    f.write('\n'.join(tests))

with open("./tests/hard_infix.text", 'w') as f:
    tests = generate_tests_infix(400, 10)
    f.write('\n'.join(tests))

with open("./tests/easy_prefix.text", 'w') as f:
    tests = generate_tests_prefix(100, 1)
    f.write('\n'.join(tests))

with open("./tests/normal_prefix.text", 'w') as f:
    tests = generate_tests_prefix(200, 4)
    f.write('\n'.join(tests))

with open("./tests/hard_prefix.text", 'w') as f:
    tests = generate_tests_prefix(400, 10)
    f.write('\n'.join(tests))