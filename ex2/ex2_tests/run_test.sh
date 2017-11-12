#!/bin/bash

python3 ex2_tests_eliav.py
cd results

echo "Check Task1"
if diff task1 task1_temp; then
	echo "Passed Task1"
else
	echo "Failed Task1"
fi

echo "Check Task2"
if diff task2 task2_temp; then
	echo "Passed Task2"
else
	echo "Failed Task2"
fi

echo "Check Task3"
if diff task3 task3_temp; then
	echo "Passed Task3"
else
	echo "Failed Task3"
fi

echo "Check Task4"
if diff task4 task4_temp; then
	echo "Passed Task4"
else
	echo "Failed Task4"
fi

echo "Check Task5"
if diff task5 task5_temp; then
	echo "Passed Task5"
else
	echo "Failed Task5"
fi

echo "Check Task6"
if diff task6 task6_temp; then
	echo "Passed Task6"
else
	echo "Failed Task6"
fi

echo "Check Task7"
if diff task7 task7_temp; then
	echo "Passed Task7"
else
	echo "Failed Task7"
fi

rm -f *_temp
