import random
import pandas as pd
import os
import subprocess
import time
import psutil
import select
import sys
import matplotlib.pyplot as plt
results_folder = "./results/language_inclusion_RCTLC_s/"
analysis_file = "analysis_results.csv"
num_results = 20
first_folder = "2018"
other_folders = ["2019", "2020"]
file_input_path = "FileSpecific"
output_folder = "./results/test/"
where_to_create_folder = "./assets/benchmark/IterativeBenchmark"
benchmark_folder = "./assets/benchmark/Dataset/Properties"
properties_per_other = 5

analysis_folder = "./analysis/test"
combined_summary_file = "analysis/LI Optimized (S)/combined_results.csv"
random.seed(42)


def get_best_performing_results(df, num_results=3):
    # Sort by 'Reduction_Percentage' in descending order and get the top results
    best_results = df.sort_values(by='Properties_Removed', ascending=False).head(num_results)
    return best_results

def get_df():
    # Load the analysis results
    first_folder_path = os.path.join(results_folder, first_folder)
    analysis_path = os.path.join(first_folder_path, analysis_file)
    df_first = pd.read_csv(analysis_path)
    df_best = get_best_performing_results(df_first, num_results=num_results)
    return df_best

def get_required_set(best_df):
    # for the first df, we enter in results_folder/FileSpecific and we load the required_properties.csv
    required_for_each_input_file = {}
    for index, row in best_df.iterrows():
        input_file = row['Input']
        file_name = input_file.split('.')[0]
        specific_folder = os.path.join(results_folder, first_folder, file_input_path, file_name)
        required_properties_path = os.path.join(specific_folder, "required_properties.csv")
        required_for_each_input_file[input_file] = pd.read_csv(required_properties_path, index_col=0)
    return required_for_each_input_file



def create_minimal_sets(minimal_sets):
    # create a folder in where_to_create_folder named first_folder with a txt for each value in required_for_each_input_file
    output_base_folder = os.path.join(where_to_create_folder, first_folder+"_minimal_sets")
    os.makedirs(output_base_folder, exist_ok=True)
    for input_file, df in minimal_sets.items():
        file_name = input_file.split('.')[0]
        output_file_path = os.path.join(output_base_folder, f"{file_name}.txt")
        with open(output_file_path, 'w') as f:
            for index, row in df.iterrows():
                f.write(f"{row['Property']}\n")



def get_other_properties(df_best, how_many_to_load):
    properties = {}
    for folder in other_folders:
        folder_path = os.path.join(benchmark_folder, folder)
        properties[folder] = {}
        for file in os.listdir(folder_path):
            if file.endswith(".txt") and file in df_best['Input'].values:
                # load only how_many_to_load properties from the file, randomly
                with open(os.path.join(folder_path, file), 'r') as f:
                    lines = f.readlines()
                    properties[folder][file] = random.choices(lines, k=how_many_to_load)
                #other_properties_files[folder].append(os.path.join(folder_path, file))

    return properties
        #df_best_other = df_other[df_other['Input'].isin(df_best['Input'])]

def dump_other_properties(other_properties):
    output_base_folder = os.path.join(where_to_create_folder, first_folder+"_other_properties")
    os.makedirs(output_base_folder, exist_ok=True)
    for folder, files_dict in other_properties.items():
        folder_output_path = os.path.join(output_base_folder, folder)
        os.makedirs(folder_output_path, exist_ok=True)
        for input_file, properties in files_dict.items():
            file_name = input_file.split('.')[0]
            output_file_path = os.path.join(folder_output_path, f"{file_name}_other.txt")
            with open(output_file_path, 'w') as f:
                for prop in properties:
                    f.write(prop)





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
            ["/usr/bin/time", "-v"] + cmd,
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


"""
In essence the analysis works as follows:
After we loaded everythin we need, for each of the best performing files in best_df, 
1. For each of the other folders, we "add" one property to the minimal set, save it as a temp.txt file
2. We create a folder in output_folder with the name of the file (without extension) and the index of the property added.
3. We run the the tool on it with input this temp.txt file and the output folder created in point 2.
4. We then load the new required properties from the output folder from the file called required_properties.csv
5. Iterate until all properties from all other folders have been analyzed
"""

def run_tests(best_df):
    for index, row in best_df.iterrows():
        input_file = row['Input']
        file_name = input_file.split('.')[0]
        minimal_set_path = os.path.join(where_to_create_folder, first_folder+"_minimal_sets", f"{file_name}.txt")
        with open(minimal_set_path, 'r') as f:
            minimal_properties = f.readlines()
        
        for folder in other_folders:
            other_properties_path = os.path.join(where_to_create_folder, first_folder+"_other_properties", folder, f"{file_name}_other.txt")
            try:
                with open(other_properties_path, 'r') as f:
                    other_properties = f.readlines()
            except FileNotFoundError:
                print(f"File not found: {other_properties_path}")
                continue

            current_properties = minimal_properties.copy()
            for i, prop in enumerate(other_properties):
                current_properties.append(prop)
                temp_file_path = os.path.join(output_folder, f"{file_name}_temp.txt")
                with open(temp_file_path, 'w') as temp_f:
                    for p in current_properties:
                        print(p)
                        temp_f.write(p)
                
                specific_output_dir = os.path.join(output_folder, f"{file_name}_analysis_{folder}_{i}")
                os.makedirs(specific_output_dir, exist_ok=True)
                
                elapsed_time, mem_usage, peak_memory = test_one_file(temp_file_path, specific_output_dir)
                
                # Load new required properties
                path =  os.path.join(specific_output_dir, "required_properties.csv")
                required_properties_df = pd.read_csv(path, index_col=0)
                # update minimal_properties for next iteration
                minimal_properties = required_properties_df['Property'].tolist()





"""
    From the output folder, we now do the analysis of the results. 
    We do a graph where the x is the "time steps", i..e from 0 to properties_per_other
    and the y is 
    - the number of properties removed.
    - the time taken
    - the memory used
    - total properties in the set
"""

"""
Does a graph for a given metric. Graph is saved in analysis_folder
Graph is a line plot where x is the step and y is the metric
"""
def __do_graph(df, metric):
    plt.figure()
    for input_file in df['File'].unique():
        df_file = df[df['File'] == input_file]
        plt.plot(df_file['Step'], df_file[metric], marker='o', label=input_file)
    plt.xlabel('Step')
    plt.ylabel(metric)
    plt.title(f'{metric} over Steps')
    plt.legend()
    graph_path = os.path.join(analysis_folder, f'iterative_{metric}.png')
    plt.savefig(graph_path)
    plt.close()


def do_graphs(df):
    __do_graph(df, 'PropertiesRemoved')
    __do_graph(df, 'Time_Taken')
    __do_graph(df, 'Memory_Used')
    __do_graph(df, 'Total_Properties')

def analyze_output(best_df, input,output):
    analysis_df = pd.DataFrame(columns=['Step', 'PropertiesRemoved', 'Time_Taken', 'Memory_Used', 'Total_Properties', "File"])
    current_step = 0
    for index, row in best_df.iterrows():
        input_file = row['Input']
        file_name = input_file.split('.')[0]
        # add first row with 0 properties added
        analysis_df.loc[current_step]=[0,0,0,0,row['Required_Properties'], input_file]
        current_step += 1 
        try:
            for folder in other_folders:
                for i in range(properties_per_other):
                    spec_file = pd.read_csv(os.path.join(input, f"{file_name}_analysis_{folder}_{i}", "analysis_results.csv"))
                    properties_removed = spec_file['Properties_Removed'].values[0]
                    time_taken = spec_file['Refinement_Time_ms'].values[0]
                    memory_used = spec_file[' Refinement_Memory_kB'].values[0]
                    total_properties = spec_file['Required_Properties'].values[0]
                    analysis_df.loc[current_step] = [current_step, properties_removed, time_taken, memory_used, total_properties, input_file]
                    current_step += 1
            analysis_output_path = os.path.join(output, f"iterative_analysis.csv")
            analysis_df.to_csv(analysis_output_path, index=False)
        except FileNotFoundError:
            print(f"Analysis files for {file_name} are incomplete, skipping analysis.")
    do_graphs(analysis_df)
    # print average time on a per file basis

    tot_results = pd.read_csv(combined_summary_file)
    #create a csv called comparison
    comparison_df = pd.DataFrame(columns=['File', 'Avg_Time_Iterative_ms', 'Avg_Time_Combined_ms', "Speedup"])
    i = 0
    for input_file in analysis_df['File'].unique():
        df_file = analysis_df[analysis_df['File'] == input_file]
        avg_time = df_file['Time_Taken'].mean()
        #f.write(f"{input_file}, {avg_time} ms\n")

        # take the result of the file from tot_results
        tot_file = tot_results[tot_results['Input'] == input_file]
        tot_file = tot_file[tot_file['Year'] == f"MCC{first_folder}"]


        if tot_file.empty:
            print(f"No combined result for {input_file} in year MCC{first_folder}, skipping.")
            continue
        combined_time = tot_file['Refinement_Time_ms'].values[0]
        speedup = combined_time / avg_time if avg_time > 0 else float('inf')
        comparison_df.loc[i] = [input_file, avg_time, combined_time, speedup]
        i += 1
    comparison_df.to_csv(os.path.join(output, "iterative_vs_combined_comparison.csv"), index=False)


    
if __name__ == "__main__":
    os.makedirs(analysis_folder, exist_ok=True)
    os.makedirs(output_folder, exist_ok=True)
    output_folder = os.path.join(output_folder, "IterativeTests")
    os.makedirs(output_folder, exist_ok=True)
    best_df = get_df()
    minimal_sets = get_required_set(best_df)
    create_minimal_sets(minimal_sets)    
    other_properties = get_other_properties(best_df, properties_per_other)
    dump_other_properties(other_properties)
    #run_tests(best_df)
    analyze_output(best_df, output_folder, analysis_folder)

    