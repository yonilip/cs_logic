from propositions.syntax import Formula
from tests_generator_ex1 import generate_tests_variables


def test_from_infix(tests):
    test_num = 1
    passed_tests = 0
    failed_tests = 0
    print("Start Testing from_infix")
    for test in tests:
        test = test.replace('\n', '')
        result = Formula.from_infix(test).infix() == test
        if result:
            passed_tests += 1
        else:
            failed_tests += 1
        print("Test %d Formula %s result %s" % (test_num, test, result))
        test_num += 1
    print("Test Summary from_infix")
    print("Total tests: %d\nPassed:%d\nFailed:%d\n" % (len(tests), passed_tests, failed_tests))


def test_from_prefix(tests):
    test_num = 1
    passed_tests = 0
    failed_tests = 0
    print("Start Testing from_prefix")
    for test in tests:
        test = test.replace('\n', '')
        print("Testing", test)
        result = Formula.from_prefix(test).prefix() == test
        if result:
            passed_tests += 1
        else:
            failed_tests += 1
        print("Test %d Formula %s result %s" % (test_num, test, result))
        test_num += 1
    print("Test Summary from_prefix")
    print("Total tests: %d\nPassed:%d\nFailed:%d\n" % (len(tests), passed_tests, failed_tests))


def test_variables(tests):
    test_num = 1
    passed_tests = 0
    failed_tests = 0
    print("Start Testing for variables")
    for test in tests:
        print("Testing", test[0], test[1])
        result = Formula.from_infix(test[0]).variables() == test[1]

        if result:
            passed_tests += 1
        else:
            failed_tests += 1
        print("Test %d Formula %s result %s" % (test_num, test, result))
        test_num += 1
    print("Test Summary from_prefix")
    print("Total tests: %d\nPassed:%d\nFailed:%d\n" % (len(tests), passed_tests, failed_tests))


def run_tests():
    # Easy Tests
    print("#############################")
    print("#        EASY TESTS         #")
    print("#############################")
    with open('./tests/easy_infix.text', 'r') as f_infix:
        test_from_infix(f_infix.readlines())
    with open('./tests/easy_prefix.text', 'r') as f_prefix:
        test_from_prefix(f_prefix.readlines())

    # Normal Tests
    print("#############################")
    print("#      Normal TESTS         #")
    print("#############################")
    with open('./tests/normal_infix.text', 'r') as f_infix:
        test_from_infix(f_infix.readlines())
    with open('./tests/normal_prefix.text', 'r') as f_prefix:
        test_from_prefix(f_prefix.readlines())

    #Hard Tests
    print("#############################")
    print("#        Hard TESTS         #")
    print("#############################")
    with open('./tests/hard_infix.text', 'r') as f_infix:
        test_from_infix(f_infix.readlines())
    with open('./tests/hard_prefix.text', 'r') as f_prefix:
        test_from_prefix(f_prefix.readlines())

    print("##################################")
    print("#         TEST Variables         #")
    print("##################################")
    test_variables(generate_tests_variables(400, 8))


if __name__ == "__main__":
    run_tests()
