#!/bin/bash

# Check if the user provided the required arguments
if [ $# -lt 3 ]; then
    echo "Usage: $0 <path_to_cnfuzz_executable> <path_to_fuzz_executable> <path_to_drup_checker>"
    exit 1
fi

# Path to the `cnfuzz` executable passed as the first parameter
cnfuzz_executable=$1

# Path to the `fuzz` executable passed as the second parameter
fuzz_executable=$2

# Path to the `drup` proof checker passed as the third parameter
drup_checker=$3

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

# Run indefinitely
while true; do
    cnf_file="temp.cnf"
    proof_file="temp.proof"

    # Generate a large random positive integer for the seed
    seed=$(((RANDOM << 15) | RANDOM))

    # Run cnfuzz with the seed and redirect output to cnf_file
    $cnfuzz_executable $seed > $cnf_file
    if [ $? -ne 0 ]; then
        echo "Error: Failed to run cnfuzz (seed: $seed)"
        exit 5
    fi

    # Run the fuzz executable with cnf_file and produce proof_file
    $fuzz_executable $cnf_file $proof_file
    fuzz_result=$?
    if [ $fuzz_result -eq 1 ]; then
        # Use the drup checker to validate the proof against the original CNF
        $drup_checker $cnf_file $proof_file > /dev/null
        if [ $? -ne 0 ]; then
            echo "Error: Proof validation failed (seed: $seed)"
            exit 7
        fi
    elif [ $fuzz_result -ne 0 ]; then
        echo "Error: $fuzz_executable encountered an error (unexpected return value: $fuzz_result, seed: $seed)"
        exit 6
    fi
done
