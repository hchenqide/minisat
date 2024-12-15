#!/bin/bash

# Check if the user provided the required arguments
if [ $# -lt 4 ]; then
    echo "Usage: $0 <number_of_rounds> <path_to_cnfuzz_executable> <path_to_fuzz_executable> <path_to_drup_checker>"
    exit 1
fi

# Number of rounds passed as the first parameter
num_rounds=$1

# Path to the `cnfuzz` executable passed as the second parameter
cnfuzz_executable=$2

# Path to the `fuzz` executable passed as the third parameter
fuzz_executable=$3

# Path to the `drup` proof checker passed as the fourth parameter
drup_checker=$4

# Check if the specified cnfuzz executable exists
if [ ! -x "$cnfuzz_executable" ]; then
    echo "Error: Specified cnfuzz executable '$cnfuzz_executable' not found or not executable"
    exit 2
fi

# Check if the specified fuzz executable exists
if [ ! -x "$fuzz_executable" ]; then
    echo "Error: Specified fuzz executable '$fuzz_executable' not found or not executable"
    exit 3
fi

# Check if the specified drup checker exists
if [ ! -x "$drup_checker" ]; then
    echo "Error: Specified drup checker '$drup_checker' not found or not executable"
    exit 4
fi

# Loop for the specified number of rounds
for (( round=1; round<=num_rounds; round++ )); do
    echo "Round $round"

    cnf_file="temp.cnf"
    proof_file="temp.proof"

    # Step 1: Generate a large random positive integer for the seed
    seed=$(((RANDOM << 15) | RANDOM ))
    echo "seed: $seed"

    # Step 2: Run cnfuzz with the seed and redirect output to cnf_file
    $cnfuzz_executable $seed > $cnf_file
    if [ $? -ne 0 ]; then
        echo "Error: Failed to run cnfuzz"
        exit 5
    fi

    # Step 3: Run the fuzz executable with cnf_file and produce proof_file.
    $fuzz_executable $cnf_file $proof_file
    if [ $? -ne 0 ]; then
        echo "Error: $fuzz_executable failed to process temp.cnf"
        exit 6
    fi

    # Step 4: Use the drup checker to validate the proof against the original CNF
    $drup_checker $cnf_file $proof_file
    if [ $? -ne 0 ]; then
        echo "Error: Proof validation failed for round $round"
        exit 7
    fi

    echo "-----------------------------------"
done

echo "All $num_rounds rounds completed!"
