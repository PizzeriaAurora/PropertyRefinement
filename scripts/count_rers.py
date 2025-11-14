import pandas as pd


#read a list of csv files and sum the Required_Properties column for each file
def sum_required_properties(csv_files):
    total_required_properties = 0
    for file in csv_files:
        df = pd.read_csv(file)
        total_required_properties += df['Required_Properties'].sum()
    return total_required_properties
def sum_number_bencharks(csv_files):
    total_benchmarks = 0
    for file in csv_files:
        df = pd.read_csv(file)
        total_benchmarks += len(df)
    return total_benchmarks



#list of dfs 
mother_dir = "results/language_inclusion_RCTLC_s/"
dataframe_files = ["ParallelRers2019Ctl/analysis_results.csv", 
                   "Rers2019Ind/analysis_results.csv"]

csv_files = [mother_dir + f for f in dataframe_files]
total = sum_required_properties(csv_files)
print(f"Total Required_Properties across datasets: {total}")
total_benchmarks = sum_number_bencharks(csv_files)
print(f"Total Benchmarks across datasets: {total_benchmarks}")