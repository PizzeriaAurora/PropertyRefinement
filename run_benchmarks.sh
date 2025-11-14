#!/bin/bash
# Usage: ./run_check_refinements.sh /path/to/folder [simulation|language_inclusion|ctl_sat] [serial|parallel]

#nohup ./run_benchmarks.sh ./assets/benchmark/Dataset/Properties language_inclusion parallel > all_logs/lang_parallel_transitive.log 2>&1 &


#nohup ./run_benchmarks.sh ./assets/benchmark/Dataset/Properties language_inclusion serial > all_logs/lang_serial_transitive.log 2>&1 &

#nohup ./ctl_refine_tool ../.././assets/benchmark/Dataset/Properties/2021 --use-full-language-inclusion --verbose -o 2021 --no-parallel > logs.log 2>&1 &

#./check_refinements ./assets/benchmark/Dataset/Properties/2021 --use-full-language-inclusion --verbose -o results/language_inclusion_RCTLC_s/2021 --no-parallel > logs/2021_language_inclusion_s.log 2>&1 &



FOLDER="$1"
ANALYSIS_MODE="$2"
RUNNING_MODE="$3"  # "serial" or "parallel"
NO_TRANSITIVE_OPTIMIZATION="$4"  # true or false
EXTRA_ARGS=""
SUFFIX=""
if [[ -z "$FOLDER" ]]; then
    echo "Usage: $0 <folder> <simulation|language_inclusion|ctl_sat> <serial|parallel> <no_transitive_optimization>"
    exit 1
fi

if [[ -z "$RUNNING_MODE" ]]; then
    RUNNING_MODE="serial"
fi

if [[ -z "$ANALYSIS_MODE" ]]; then
    ANALYSIS_MODE="simulation"
fi

if [[ -z "$NO_TRANSITIVE_OPTIMIZATION" ]]; then
    EXTRA_ARGS+=""
else
    EXTRA_ARGS+="--no-transitive "
    SUFFIX+="_nto"
fi




if [[ "$ANALYSIS_MODE" != "simulation" && "$ANALYSIS_MODE" != "language_inclusion" && "$ANALYSIS_MODE" != "ctl_sat" ]]; then
    echo "Invalid analysis mode. Choose 'simulation', 'language_inclusion', or 'ctl_sat'."
    exit 1
fi


if [[ "$ANALYSIS_MODE" == "language_inclusion" ]]; then
    EXTRA_ARGS+="--use-full-language-inclusion"
elif [[ "$ANALYSIS_MODE" == "ctl_sat" ]]; then
    echo "Not yet implemented "
    exit 1

elif [[ "$ANALYSIS_MODE" == "simulation" ]]; then
    EXTRA_ARGS+=""
fi

PARENT_OUTPUT_FOLDER="results/"
mkdir -p "$PARENT_OUTPUT_FOLDER"


OUTPUT_FOLDER="${PARENT_OUTPUT_FOLDER}${ANALYSIS_MODE}_RCTLC"
mkdir -p logs

# Get all subfolders
shopt -s nullglob
SUBFOLDERS=("$FOLDER"/*/)

# Determine max concurrent jobs
if [[ "$RUNNING_MODE" == "parallel" ]]; then
    MAX_JOBS=1
    #add extra args for parallel execution
    EXTRA_ARGS+=" --parallel -j 6"
    SUFFIX+="_p"
elif [[ "$RUNNING_MODE" == "serial" ]]; then
    MAX_JOBS=1
    EXTRA_ARGS+=""
    SUFFIX+="_s"
else
    echo "Invalid running mode. Choose 'serial' or 'parallel'."
    exit 1
fi

mkdir -p "$OUTPUT_FOLDER$SUFFIX"
RESULTS_PREFIX="$OUTPUT_FOLDER$SUFFIX"

# Function to run a single job
run_job() {
    local subfolder="$1"
    local sub
    sub=$(basename "$subfolder")
    local log_file="logs/${sub}_${ANALYSIS_MODE}${SUFFIX}.log"

    echo "Starting check_refinements for $subfolder..."

    #echo "nohup ./ctl_refine_tool \"$subfolder\" -o \"$RESULTS_PREFIX/$year\" --verbose $EXTRA_ARGS > \"$log_file\" 2>&1 &"
    #check_refinements 
    nohup ./check_refinements "$subfolder" -o "$RESULTS_PREFIX/$sub" --verbose $EXTRA_ARGS > "$log_file" 2>&1 &
}

# Main loop
job_count=0
echo "Starting Refinement in $ANALYSIS_MODE in $RUNNING_MODE mode..."
echo "-------------------------------------"

for subfolder in "${SUBFOLDERS[@]}"; do
    [[ -d "$subfolder" ]] || continue

    run_job "$subfolder"
    ((job_count++))

    if (( job_count >= MAX_JOBS )); then
        wait
        job_count=0
    fi
done

wait
echo "All jobs completed."




