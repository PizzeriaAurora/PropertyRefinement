import subprocess
import os 
import time
import datetime
import psutil
import select
from tqdm import tqdm
import sys
import pandas as pd

#./check_refinements ./assets/benchmark/Dataset/Properties/2021 --use-full-language-inclusion --verbose -o results/language_inclusion_RCTLC_s/2021 --no-parallel 
#nohup python3 run_file_per_file.py > logs/2022_bis2.log 2>&1 &

def test_one_file(file_path, output_dir, timeout_h=10):
    cmd = ["./check_refinements", 
            file_path, "--use-full-language-inclusion", 
            "--verbose", 
            "--no-parallel",
            "-o", output_dir ]
    print("Running command:", " ".join(cmd))
    mem_usage = 0
    peak_mem = 0
    start_time = time.perf_counter()

    try:
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1  # line-buffered
        )
        p = psutil.Process(proc.pid)
        timeout_s = timeout_h * 3600

        full_output = []

        # Make stdout non-blocking
        fd = proc.stdout.fileno()
        os.set_blocking(fd, False)

        while True:
            # Check if process ended
            if proc.poll() is not None and not select.select([fd], [], [], 0)[0]:
                break

            # Non-blocking read if data is ready
            ready, _, _ = select.select([fd], [], [], 0.1)
            if ready:
                line = proc.stdout.readline()
                if line:
                    print(line, end="")
                    sys.stdout.flush()
                    full_output.append(line)

            # Track memory
            try:
                mem = p.memory_info().rss
                if mem > peak_mem:
                    peak_mem = mem
            except psutil.NoSuchProcess:
                break

            # Timeout check
            if time.perf_counter() - start_time > timeout_s:
                print(f"Timeout: killing process after {timeout_h} hours.")
                for child in p.children(recursive=True):
                    child.kill()
                p.kill()
                proc.wait()
                raise subprocess.TimeoutExpired(cmd, timeout=timeout_s)

        end_time = time.perf_counter()
        elapsed_time = end_time - start_time

        stdout = "".join(full_output)
        stderr = ""  # merged into stdout

        # Parse memory info from /usr/bin/time
        peak_memory = None
        for line in stdout.splitlines():
            if "Maximum resident set size" in line:
                try:
                    peak_memory = int(line.split(":")[1].strip())
                except (IndexError, ValueError):
                    pass

    except subprocess.TimeoutExpired:
        end_time = time.perf_counter()
        elapsed_time = end_time - start_time
        mem_usage = peak_mem // 1024
        peak_memory = None
        stdout, stderr = "", ""

    except Exception as e:
        end_time = time.perf_counter()
        elapsed_time = end_time - start_time
        mem_usage = peak_mem // 1024
        peak_memory = None
        stdout, stderr = "", ""
        print(f"Error running command: {e}")



    # from the output, extract the file analysis_results.csv
    

    mem_usage = peak_mem // 1024
    return elapsed_time, mem_usage, peak_memory



def load_or_create_file(output_dir):
    output_csv_path = os.path.join(output_dir, "analysis_results.csv")
    if not os.path.exists(output_csv_path):
        with open(output_csv_path, "w") as f:
            fwrite = "Input,Total_Properties,Equivalence_Classes,Total_Refinements,Required_Properties,Properties_Removed,TransitiveEliminations,Parsing_Time_ms,Equivalence_Time_ms,Refinement_Time_ms,Total_Time_ms,Total_Analysis_Memory_kB, Refinement_Memory_kB\n"
            f.write(fwrite)
    df = pd.read_csv(output_csv_path)
    return output_csv_path, df


files_dir = "./assets/benchmark/Dataset/Properties/2021"
output_base_dir = "test/2021_not_done"


output_dir_to_give_to_analysis = os.path.join(output_base_dir, "FileSpecific")
if not os.path.exists(output_dir_to_give_to_analysis):
    os.makedirs(output_dir_to_give_to_analysis)
files = sorted(os.listdir(files_dir))
files = [f for f in files if f.endswith(".txt")]


overview_df_path = "./results/language_inclusion_RCTLC_s/2021/analysis_results.csv"
overview_df = pd.read_csv(overview_df_path)
done_files= overview_df['Input'].tolist()
print(f"Number of done files in {overview_df_path}: {len(done_files)}")
difference = set(files) - set(done_files)
print(f"Number of not done files: {len(difference)}")



#save current status analysis_results.csv if it exists in output_base_dir, otherwise create it
if not os.path.exists(output_base_dir):
    os.makedirs(output_base_dir)
    output_csv_path, overall_analysis_df = load_or_create_file(output_base_dir)
else:
    output_csv_path, overall_analysis_df = load_or_create_file(output_base_dir)


not_done = []


for f in difference:
    if f != continue_from and continue_from is not None:
        continue
    if f == continue_from:
        continue_from = None
        continue
    
    file_path = os.path.join(files_dir, f)
    test_one_file(file_path, os.path.join(output_dir_to_give_to_analysis, f.replace(".txt","")))
    try:
        temp_df = pd.read_csv(os.path.join(output_dir_to_give_to_analysis, f.replace(".txt",""), "analysis_results.csv"))
    except Exception as e:
        print(f"Error reading analysis_results.csv for file {f}: {e}")
        not_done.append(f)
        continue
    #append temp_df to overall_analysis_df
    overall_analysis_df = pd.concat([overall_analysis_df, temp_df], ignore_index=True)
    #save overall_analysis_df to output_csv_path
    overall_analysis_df.to_csv(output_csv_path, index=False)
    print(f"Saved results to {output_csv_path}")


#save not done in a text file
if len(not_done) > 0:
    with open(os.path.join(output_base_dir, "not_done.txt"), "w") as f:
        for item in not_done:
            f.write(f"{item}\n")
    print(f"Some files were not done. See {os.path.join(output_base_dir, 'not_done.txt')} for details.")