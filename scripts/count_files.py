import os 


input_folder = "./assets/benchmark/Dataset/Properties/2021"

files= os.listdir(input_folder)
files = [f for f in files if f.endswith(".txt")]
print(f"Number of files in {input_folder}: {len(files)}")
files = sorted(files)

#print file at the middle
middle_index = len(files) // 2
print(f"Middle file: {files[middle_index]}")


#count all files after a specific one
file = "TriangularGrid-PT-3011.txt"
start_counting = False
count = 0
for f in files:
    if f == file:
        start_counting = True
        continue
    if start_counting:
        count += 1
print(f"Number of files after {file}: {count}")


import pandas as pd

overview_df_path = "./results/language_inclusion_RCTLC_s/2021/analysis_results.csv"
overview_df = pd.read_csv(overview_df_path)
done_files= overview_df['Input'].tolist()
print(f"Number of done files in {overview_df_path}: {len(done_files)}")
difference = set(files) - set(done_files)
print(f"Number of not done files: {len(difference)}")