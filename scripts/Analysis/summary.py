

import os
import pandas as pd


def write_summary(summary_output_dir,folder, subfolder, df, create_df = True, benchmarks_folder=""):
        summary_file = os.path.join(summary_output_dir, f"{os.path.basename(subfolder)}_summary.txt")
        with open(summary_file, "w") as f:
            pass
        #create df equivalent for the summary
        
        info= {}

        info["Benchmark Completed"] = df.shape[0]
        info["Average Properties"] = df['Total_Properties'].mean()
        info["Average refinement time (s)"] = df['Refinement_Time_ms'].mean()/1000  # in seconds
        info["Average refinement time (ms)"] = df['Refinement_Time_ms'].mean()  # in milliseconds
        info["Total properties removed"] = df['Properties_Removed'].sum()
        info["Average properties removed"] = df['Properties_Removed'].mean()
        info["Average reduction (%)"] = df['Properties_Removed'].mean()/df['Total_Properties'].mean()*100 if info["Average Properties"] > 0 else 0
        # Calculate reduction percentage excluding files with zero properties removed
        non_zero_df = df[df['Properties_Removed'] > 0]
        if len(non_zero_df) > 0:
            info["Average reduction (%) - Non-Zero Only"] = non_zero_df['Properties_Removed'].mean()/non_zero_df['Total_Properties'].mean()*100
        else:
            info["Average reduction (%) - Non-Zero Only"] = 0
        info["Total refinements"] = df['Total_Refinements'].sum()
        info["Average refinements"] = df['Total_Refinements'].mean()
        info["Total equivalence classes"] = df['Equivalence_Classes'].sum()
        info["Average equivalence classes"] = df['Equivalence_Classes'].mean()

        total_number_of_benchmarks = 0
        # list all txt files in the benchmarks_folder and sum the number of lines
        total_number_of_properties = 0

        benchmark_name = subfolder.split("/")[-1]
        print(f"Benchmark name: {benchmark_name}")
        """
        if benchmark_name != "overall":

            if benchmark_name == "ParallelRers2019Ctl" or benchmark_name == "Rers2019Ind":
                benchmarks_folder = benchmarks_folder.split("/")[:-3]
                #append Dataset_lite to the path
                benchmarks_folder = "/".join(benchmarks_folder) + "/Dataset_lite"
                #append benchmark_name to the path
                benchmarks_folder = os.path.join(benchmarks_folder, benchmark_name)
                print(f"Adjusted benchmarks folder to {benchmarks_folder} for RERS benchmarks.")
            if benchmarks_folder != "" and os.path.exists(benchmarks_folder):
                #check if benchmarks_folder has any subfolder
                if any(os.path.isdir(os.path.join(benchmarks_folder, d)) for d in os.listdir(benchmarks_folder)):
                    # has subfolders
                    for sub in os.listdir(benchmarks_folder):
                        sub_path =  os.path.join(benchmarks_folder, sub)
                        if os.path.isdir(sub_path):
                            if not benchmark_name == "Rers2019Ind" and not benchmark_name == "ParallelRers2019Ctl":
                                total_number_of_benchmarks = len(os.listdir(benchmarks_folder)) / 2  # half is CTL extension
                            else :
                                total_number_of_benchmarks = len(os.listdir(benchmarks_folder))  # RERS2019Ind has no CTL extension files
                            for f in os.listdir(sub_path):
                                if f.endswith(".txt"):
                                    with open(os.path.join(sub_path, f), "r") as file:
                                        lines = file.readlines()
                                        total_number_of_properties += len(lines)

                else:   
                    # no subfolders
                    if not benchmark_name == "Rers2019Ind" and not benchmark_name == "ParallelRers2019Ctl":
                        total_number_of_benchmarks = len(os.listdir(benchmarks_folder)) / 2  # half is CTL extension
                    else :
                        total_number_of_benchmarks = len(os.listdir(benchmarks_folder))  # RERS2019Ind has no CTL extension files
                    for f in os.listdir(benchmarks_folder):
                        if f.endswith(".txt"):
                            with open(os.path.join(benchmarks_folder, f), "r") as file:
                                lines = file.readlines()
                                total_number_of_properties += len(lines)
                info["Total number of benchmarks"] = total_number_of_benchmarks # add 39 for the ParallelRers2019Ctl benchmarks
                info["Total number of properties"] = total_number_of_properties # add 605 for the RERS benchmarks
            else:
                print(f"Benchmarks folder {benchmarks_folder} does not exist. Cannot compute total number of benchmarks and properties.")
                info["Total number of benchmarks"] = 0
                info["Total number of properties"] = 0
        else:
            info["Total number of benchmarks"] = df.size
            info["Total number of properties"] = df['Total_Properties'].sum()
        """
        info["Total number of benchmarks"] = df.shape[0]
        info["Total number of properties"] = df['Total_Properties'].sum()
        info["Completion Percentage"] = df.shape[0] / total_number_of_benchmarks * 100 if total_number_of_benchmarks > 0 else 0
        info["Transitive Elimination"] = df["TransitiveEliminations"].sum()
        info["Average Transitive Eliminations"] = df["TransitiveEliminations"].mean()
        print(df.columns)
        memory = df[" Refinement_Memory_kB"]
        #remove data from memory that has more than 10^12 and replace them with 0
        memory[memory > 10**12] = 0
        info["Memory MB"] = memory.mean() / 1024  # Convert to MB
        #print(f"Total number of benchmarks for folder {subfolder}: {total_number_of_benchmarks}")
            # Create a simple txt summary file with the following information:
        # Average reduction, refinement time, properties_removed, total refinements and equivalence classes for subfolder
        with open(summary_file, "a") as f:
            f.write(f"Benchmark Completed: {info['Benchmark Completed']}\n")
            f.write(f"Total number of benchmarks: {info['Total number of benchmarks']}\n")
            f.write(f"Completion Percentage: {info['Completion Percentage']} %\n")
            f.write(f"Average Properties: {info['Average Properties']}\n")
            #refinement time in s
            f.write(f"Average refinement time: {info['Average refinement time (s)']}\n")
            f.write(f"Total properties removed: {info['Total properties removed']}\n")
            f.write(f"Average properties removed: {info['Average properties removed']}\n")
            f.write(f"Average reduction (%): {info['Average reduction (%)']}\n")
            f.write(f"Average reduction (%) - Non-Zero Only: {info['Average reduction (%) - Non-Zero Only']}\n")
            f.write(f"Total refinements: {info['Total refinements']}\n")
            f.write(f"Average refinements: {info['Average refinements']}\n")
            f.write(f"Total equivalence classes: {info['Total equivalence classes']}\n")
            f.write(f"Average equivalence classes: {info['Average equivalence classes']}\n")
            f.write(f"Total Transitive Eliminations: {info['Transitive Elimination']}\n")
            f.write(f"Average Transitive Eliminations: {info['Average Transitive Eliminations']}\n")
            
        # Append the above information to the df_summary
        
        

        # we also wanna print the one with lowest/higher refinement time, lowest/highest reduction and lowest/highest properties removed

        




        best_reduction = df.loc[df['Properties_Removed'].idxmax()]
        worst_reduction = df.loc[df['Properties_Removed'].idxmin()]
        fastest_refinement = df.loc[df['Refinement_Time_ms'].idxmin()]
        slowest_refinement = df.loc[df['Refinement_Time_ms'].idxmax()]
        most_properties_removed = df.loc[df['Properties_Removed'].idxmax()]
        least_properties_removed = df.loc[df['Properties_Removed'].idxmin()]
        most_refinements = df.loc[df['Total_Refinements'].idxmax()]


        info["Best Reduction"] = best_reduction["Input"]
        info["Highest Reduction"] = best_reduction["Properties_Removed"]/best_reduction["Total_Properties"]*100 if best_reduction["Total_Properties"] > 0 else 0
        info["Worst Reduction"] = worst_reduction["Input"]
        info["Fastest Refinement"] = fastest_refinement["Input"]
        info["Slowest Refinement"] = slowest_refinement["Input"]
        info["Most Properties Removed"] = most_properties_removed["Input"]
        info["Least Properties Removed"] = least_properties_removed["Input"]
        info["Most Refinements"] = most_refinements["Input"]
        with open(summary_file, "a") as f:
            f.write("\nBest Reduction:\n")
            f.write(best_reduction.to_string())
            f.write("\n\nWorst Reduction:\n")
            f.write(worst_reduction.to_string())
            f.write("\n\nFastest Refinement:\n")
            f.write(fastest_refinement.to_string())
            f.write("\n\nSlowest Refinement:\n")
            f.write(slowest_refinement.to_string())
            f.write("\n\nMost Properties Removed:\n")
            f.write(most_properties_removed.to_string())
            f.write("\n\nLeast Properties Removed:\n")
            f.write(least_properties_removed.to_string())
            f.write("\n\nMost Refinements:\n")
            f.write(most_refinements.to_string())

        # we also want to know how many have zero properties removed
        info["Zero Properties Removed"] = df[df['Properties_Removed'] == 0].shape[0]
        info["Percentage Zero Properties Removed"] = info["Zero Properties Removed"]/df.shape[0]*100 if df.shape[0] > 0 else 0
        with open(summary_file, "a") as f:
            f.write(f"\nBenchmark Completed with zero properties removed: {info['Zero Properties Removed']}\n")
            f.write(f"Percentage of cases with zero properties removed: {info['Percentage Zero Properties Removed']} %\n")

        

        # We also want to know for each of the 0 properties removed, the average refinement time
        if info["Zero Properties Removed"] > 0:
            info["Average refinement time for zero properties removed"] = df[df['Properties_Removed'] == 0]['Refinement_Time_ms'].mean()/1000
            with open(summary_file, "a") as f:
                f.write(f"Average refinement time for cases with zero properties removed: {info['Average refinement time for zero properties removed']} s\n")
        if info["Zero Properties Removed"] > 0:
            info["Average Time for Zero Properties (s)"] = df[df['Properties_Removed'] ==0]['Total_Time_ms'].mean()/1000
            info["Median Time for Zero Properties (s)"] = df[df['Properties_Removed'] == 0]['Total_Time_ms'].median()/1000
            info["Max Time for Zero Properties (s)"] = df[df['Properties_Removed'] ==0]['Total_Time_ms'].max()/1000
            info["Min Time for Zero Properties (s)"] = df[df['Properties_Removed'] == 0]['Total_Time_ms'].min()/1000
            with open(summary_file, "a") as f:
                f.write(f"Benchmark Completed with zero properties removed: {info['Zero Properties Removed']}\n")
                f.write(f"Average Time for Zero Properties (s): {info['Average Time for Zero Properties (s)']}\n")
                f.write(f"Median Time for Zero Properties (s): {info['Median Time for Zero Properties (s)']}\n")
                f.write(f"Max Time for Zero Properties (s): {info['Max Time for Zero Properties (s)']}\n")
                f.write(f"Min Time for Zero Properties (s): {info['Min Time for Zero Properties (s)']}\n")

        # As well as the number of classes when it has zero properties removed
        if info["Zero Properties Removed"] > 0:
            info["Average equivalence classes for zero properties removed"] = df[df['Properties_Removed'] == 0]['Equivalence_Classes'].mean()
            with open(summary_file, "a") as f:
                f.write(f"Average equivalence classes for cases with zero properties removed: {info['Average equivalence classes for zero properties removed']}\n")

        info["Non-Zero Properties Removed"] = df[df['Properties_Removed'] > 0].shape[0]
        if info["Non-Zero Properties Removed"] > 0:
            info["Average Time for Non-Zero Properties (s)"] = df[df['Properties_Removed'] > 0]['Total_Time_ms'].mean()/1000
            info["Median Time for Non-Zero Properties (s)"] = df[df['Properties_Removed'] > 0]['Total_Time_ms'].median()/1000
            info["Max Time for Non-Zero Properties (s)"] = df[df['Properties_Removed'] > 0]['Total_Time_ms'].max()/1000
            info["Min Time for Non-Zero Properties (s)"] = df[df['Properties_Removed'] > 0]['Total_Time_ms'].min()/1000
            with open(summary_file, "a") as f:
                f.write(f"Benchmark Completed with non-zero properties removed: {info['Non-Zero Properties Removed']}\n")
                f.write(f"Average Time for Non-Zero Properties (s): {info['Average Time for Non-Zero Properties (s)']}\n")
                f.write(f"Median Time for Non-Zero Properties (s): {info['Median Time for Non-Zero Properties (s)']}\n")
                f.write(f"Max Time for Non-Zero Properties (s): {info['Max Time for Non-Zero Properties (s)']}\n")
                f.write(f"Min Time for Non-Zero Properties (s): {info['Min Time for Non-Zero Properties (s)']}\n")

        if create_df:
            df_summary = pd.DataFrame.from_dict(info, orient='index', columns=["Value"])
            df_summary.index = df_summary.index.rename("Metric")
            df_summary.to_csv(os.path.join(summary_output_dir, f"{os.path.basename(subfolder)}_summary.csv"))
            return df_summary
        
        

