import os
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import math
from typing import Dict, List, Tuple
import glob
from pathlib import Path
from tqdm import tqdm
import shutil



from Analysis import (
    create_single_analysis, 
    create_compared_analysis,
    categorize_benchmarks,
    write_summary,
    generate_overview_table,
    generate_benchmark_table,
    generate_benchmark_table_v2,
    generate_benchmark_table_transposed,
    create_all_correlation_plots,
    
)


plt.style.use('default')
plt.rcParams.update({
    'font.size': 10,
    'axes.titlesize': 12,
    'axes.labelsize': 11,
    'xtick.labelsize': 9,
    'ytick.labelsize': 9,
    'legend.fontsize': 9,
    'figure.titlesize': 14,
    'lines.linewidth': 2,
    'lines.markersize': 6,
    'axes.grid': True,
    'grid.alpha': 0.3, 
})


def parse():
    """Parse configuration from a YAML file.

    Behavior:
    - If the first command-line argument is provided it is treated as the path to a YAML config file.
    - Otherwise the function will search for one of: 'analysis_config.yaml', 'config.yaml', 'analysis.yaml' in the current working dir.
    - The config file may contain the keys:
        input_folder: str (required)
        output_dir: str (default: 'analysis')
        summary_folder: str (default: 'summary')
        representatives: list[int] (default: [25,50,75,90])
        num_representatives: int (default: 5)
        only_summary: bool (default: False)
        compare_to: str or list[str] (optional)

    Returns a SimpleNamespace with attributes matching the old argparse args for backward compatibility.
    """
    import sys
    try:
        import yaml
    except Exception as e:
        raise RuntimeError("PyYAML is required to read YAML configs. Install with: pip install pyyaml") from e

    # Determine config path
    config_path = None
    if len(sys.argv) > 1:
        # First arg is considered path to YAML config
        config_path = sys.argv[1]
    else:
        print("No config file specified, searching for default config files...")
        config_path = "assets/analysis_config.yaml"
        if not os.path.exists(config_path):
            print("Error: No config file found. Please provide a YAML config file as the first argument.")
            sys.exit(1)

    config = {}
    if config_path:
        with open(config_path, "r") as fh:
            config = yaml.safe_load(fh) or {}

    # Helper to extract values with defaults
    def _get(k, default):
        return config.get(k, default)

    

    output_dir = _get("output_dir", "analysis")
    summary_folder = _get("summary_folder", "summary")

    representatives = _get("representatives", [25, 50, 75, 90])
    # allow single int or comma separated string
    if isinstance(representatives, (int, float)):
        representatives = [int(representatives)]
    if isinstance(representatives, str):
        representatives = [int(x.strip()) for x in representatives.split(",") if x.strip()]

    num_representatives = int(_get("num_representatives", 5))
    only_summary = bool(_get("only_summary", False))

    input_folder = _get("input_folder", Dict)
    if input_folder is None or not isinstance(input_folder, dict):
        raise ValueError("input_folder must be specified in the YAML config in the way (graph_name: input_folder).")
    if isinstance(input_folder, dict):
        # Already a dict of named folders, e.g. {'s': './path1', 'p': './path2'}
        folders = {k: v for k, v in input_folder.items()}
    else:
        raise ValueError("input_folder must be specified in the YAML config in the way (graph_name: input_folder).")

    formula_info_folder = _get("formula_info_folder", "")

    create_output_folder_per_graph_name = _get("create_output_folder_per_graph_name", False)
    benchmark_folder = _get("benchmark_folder", "")
    print("Using benchmark folder:", benchmark_folder)
    from types import SimpleNamespace
    return SimpleNamespace(
        input_folders=dict(folders),
        output_dir=output_dir,
        summary_folder=summary_folder,
        representatives=representatives,
        num_representatives=num_representatives,
        only_summary=only_summary,
        use_graph_name = create_output_folder_per_graph_name,
        benchmark_folder=benchmark_folder,
        formula_info_folder=formula_info_folder,
    )



def create_analysis_single_run(folder, 
                    output_dir="analysis", 
                    summary_folder = "summary", 
                    representative_percentages = [25, 50, 75, 90],
                    num_representatives = 5, 
                    only_summary = False,
                    benchmarks_folder="",
                    formula_info_folder =""):
    if not os.path.exists(folder):
        print(f"Folder {folder} does not exist.")
        return

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    subfolders = sorted([
        f.path
        for f in os.scandir(folder)
    ])
    

    summary_output_dir = os.path.join(output_dir, summary_folder)
    if not os.path.exists(summary_output_dir):
        os.makedirs(summary_output_dir)
    total_df = pd.DataFrame()
    for subfolder in subfolders:
        if not os.path.isdir(subfolder):
            continue
        result_csv = os.path.join(subfolder, "analysis_results.csv")
        if not os.path.exists(result_csv):
            print(f"Result file {result_csv} does not exist, skipping.")
            continue

        #before reading the csv, remove the last element from every row (there was a problem in the output generation)
        #with open(result_csv, "r") as f:
        #    lines = f.readlines()
        #with open(result_csv, "w") as f:
        #    f.write(lines[0])  # write header
        #    for line in lines[1:]:
        #        parts = line.strip().split(",")
        #        if len(parts) > 1:
        #            f.write(",".join(parts[:-1]) + "\n")
        df = pd.read_csv(result_csv)
        if df.empty:
            print(f"Result file {result_csv} is empty, skipping.")
            continue
        year_benchmarks_folder = os.path.join(benchmarks_folder, os.path.basename(subfolder))
        write_summary(summary_output_dir,folder, subfolder, df, True, year_benchmarks_folder)
        # Label each benchmark with its subfolder name
        # Add "MCC" prefix only if the subfolder name is a 4-digit year
        subfolder_name = os.path.basename(subfolder)
        if subfolder_name.isdigit() and len(subfolder_name) == 4:
            df["Year"] = "MCC" + subfolder_name
        else:
            df["Year"] = subfolder_name
        total_df = pd.concat([total_df, df], ignore_index=True)

    #total_summary_file = os.path.join(output_dir, "total_summary.txt")
    summary_df = write_summary(output_dir,folder, "overall", total_df, True, benchmarks_folder)
    
    # Generate benchmark tables (LaTeX)
    summary_csv = os.path.join(output_dir, "overall_summary.csv")
    if os.path.exists(summary_csv):
        generate_benchmark_table(summary_csv, output_dir)
        generate_benchmark_table_v2(summary_csv, output_dir)
        generate_benchmark_table_transposed(summary_csv, output_dir)


    #create Reduction_Percentage column
    total_df['Reduction_Percentage'] = total_df['Properties_Removed'] / total_df['Total_Properties'] * 100
    total_df['Properties_Eliminated'] = total_df['Properties_Removed']
    categories = categorize_benchmarks(total_df["Input"].tolist())
    total_df["Category"] = total_df["Input"].apply(
        lambda x: next((cat for cat, files in categories.items() if x in files), "Other")
    )
    

    total_df.to_csv(os.path.join(output_dir, "combined_results.csv"), index=False)

    #find representatives (take the ones with smallest time) for 25, 75, 90 % reduction. 5 each
    representatives = {}
    for perc in representative_percentages:
        filtered_df = total_df[total_df['Reduction_Percentage'] >= perc].copy()
        # make sure time is numeric and ignore rows without a valid time
        filtered_df['Refinement_Time_ms'] = pd.to_numeric(filtered_df['Refinement_Time_ms'], errors='coerce')
        filtered_df = filtered_df.dropna(subset=['Refinement_Time_ms'])
        if not filtered_df.empty:
            #save only the name of the input file
            representatives[perc] = filtered_df.nsmallest(num_representatives, 'Refinement_Time_ms')['Input'].tolist()
        else:
            representatives[perc] = []

    # Save representatives to a CSV file, where index is representative percentage and column is the representative files
    # Convert to DataFrame with one list per row
    rep_df = pd.DataFrame({
        "Reduction Percentage": representatives.keys(),
        "Representatives": representatives.values()
    })
    rep_df["Representatives"] = rep_df["Representatives"].apply(str)

    rep_df.to_csv(os.path.join(output_dir, "representatives.csv"), index=False)

    if only_summary:
        return total_df
    
    # Merge formula info if available for single analysis plots
    total_df_with_formula = total_df.copy()
    if formula_info_folder and os.path.exists(formula_info_folder):
        # Load all formula info files
        formula_info_files = glob.glob(os.path.join(formula_info_folder, "info_per_file_*.csv"))
        if formula_info_files:
            formula_info_dfs = []
            for info_file in formula_info_files:
                info_df = pd.read_csv(info_file)
                formula_info_dfs.append(info_df)
            
            # Combine all formula info
            combined_formula_info = pd.concat(formula_info_dfs, ignore_index=True)
            combined_formula_info["Input"] = combined_formula_info["File"].apply(lambda x: x + ".txt")
            # Merge with total_df based on Input filename
            total_df_with_formula = total_df.merge(combined_formula_info, 
                                                   left_on='Input', 
                                                   right_on='Input', 
                                                   how='left')
    print("Creating single analysis plots...")
    total_df_with_formula.loc[
    total_df_with_formula[" Refinement_Memory_kB"] > 1e10,  # 10e12 = 1e13, measurement error
    " Refinement_Memory_kB"
    ] = 0
    # Convert time from ms to seconds for complexity plots
    if 'Refinement_Time_ms' in total_df_with_formula.columns:
        total_df_with_formula['Refinement_Time_s'] = total_df_with_formula['Refinement_Time_ms'] / 1000
    create_single_analysis(total_df_with_formula, output_dir)
    if(formula_info_folder and os.path.exists(formula_info_folder)):
        create_all_correlation_plots(total_df, formula_info_folder, output_dir)
    print(f"Analysis for folder {folder} completed. Results saved in {output_dir}.")

    return total_df,summary_df
    
    
if __name__ == "__main__":
    args = parse()

    names, input_folders = list(args.input_folders.keys()), list(args.input_folders.values())
    # determine output layout. Use the name of the input folder ( last part of the path)

    output_dir = os.path.join(args.output_dir, 
                              os.path.basename(input_folders[0]) if not args.use_graph_name else names[0]
                              )

    first_df,summary_df = create_analysis_single_run(
        input_folders[0],
        output_dir,
        args.summary_folder,
        args.representatives,
        args.num_representatives,
        args.only_summary,
        args.benchmark_folder,
        formula_info_folder=args.formula_info_folder,
    )
    dfs_to_compare = {names[0]: first_df}
    summary_dfs_to_compare = {names[0]: summary_df}
    if len(input_folders) > 1:
        for name, compare_to_folder in zip(names[1:],input_folders[1:]):
            
            second_df,summary_df_sec = create_analysis_single_run(
                compare_to_folder,
                os.path.join(args.output_dir, os.path.basename(compare_to_folder) 
                             if not args.use_graph_name else name
                             ),
                args.summary_folder,
                args.representatives,
                args.num_representatives,
                args.only_summary,
                args.benchmark_folder,
                formula_info_folder=args.formula_info_folder,
                )
            dfs_to_compare[name] = second_df
            summary_dfs_to_compare[name] = summary_df_sec
        create_compared_analysis(dfs_to_compare, os.path.join(args.output_dir, "Comparison"))
        # In the main folder, concatenate horizontally the summary dataframes and save as compared_summary.csv
        # The columns are the names of the pdfs, the index is the summary metrics
        compared_summary_df = pd.DataFrame()
        for name, sum_df in summary_dfs_to_compare.items():
            sum_df = sum_df.rename(columns={"Value": name})
            if compared_summary_df.empty:
                compared_summary_df = sum_df
            else:
                compared_summary_df = compared_summary_df.join(sum_df, how='outer')
        compared_summary_df.to_csv(os.path.join(args.output_dir, "compared_summary.csv"))
        generate_overview_table(os.path.join(args.output_dir, "compared_summary.csv"), args.output_dir)
    
    # make a folder
    paper_folder = os.path.join(args.output_dir, "paper_stuff")
    os.makedirs(paper_folder, exist_ok=True)
    # copy the stuff for the paper there
    shutil.copyfile(f"{output_dir}/benchmark_table_grouped.tex", os.path.join(paper_folder, "benchmark_table_grouped.tex"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/correlation_file_atomic_complexity_vs_reduction_percentage.png", os.path.join(paper_folder, "correlation_file_atomic_complexity_vs_reduction_percentage.png"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/correlation_file_atomic_complexity_vs_reduction_percentage.pgf", os.path.join(paper_folder, "correlation_file_atomic_complexity_vs_reduction_percentage.pgf"))

    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/correlation_file_formula_size_vs_reduction_percentage.png",
                    os.path.join(paper_folder, "correlation_file_formula_size_vs_reduction_percentage.png"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/correlation_file_formula_size_vs_reduction_percentage.pgf",
                    os.path.join(paper_folder, "correlation_file_formula_size_vs_reduction_percentage.pgf"))
    shutil.copyfile(f"{output_dir}/PNG/average_time_breakdown_per_category.png", os.path.join(paper_folder, "average_time_breakdown_per_category.png"))
    shutil.copyfile(f"{output_dir}/PGF/average_time_breakdown_per_category.pgf", os.path.join(paper_folder, "average_time_breakdown_per_category.pgf"))
    shutil.copyfile(f"{output_dir}/PNG/average_memory_and_time_dualaxis.png", os.path.join(paper_folder, "average_memory_and_time_dualaxis.png"))
    shutil.copyfile(f"{output_dir}/PGF/average_memory_and_time_dualaxis.pgf", os.path.join(paper_folder, "average_memory_and_time_dualaxis.pgf"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/correlation_file_atomic_complexity_vs_total_time.png", os.path.join(paper_folder, "correlation_file_atomic_complexity_vs_total_time.png"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/correlation_file_atomic_complexity_vs_total_time.pgf", os.path.join(paper_folder, "correlation_file_atomic_complexity_vs_total_time.pgf"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/correlation_file_formula_size_vs_total_time.png", os.path.join(paper_folder, "correlation_file_formula_size_vs_total_time.png"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/correlation_file_formula_size_vs_total_time.pgf", os.path.join(paper_folder, "correlation_file_formula_size_vs_total_time.pgf"))

    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/trajectory_atomic_complexity_time_memory.pgf", os.path.join(paper_folder, "trajectory_atomic_complexity_time_memory.pgf"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/trajectory_atomic_complexity_time_memory.png", os.path.join(paper_folder, "trajectory_atomic_complexity_time_memory.png"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PGF/trajectory_formula_size_time_memory.pgf", os.path.join(paper_folder, "trajectory_formula_size_time_memory.pgf"))
    shutil.copyfile(f"{output_dir}/FormulaSizeCorrelationPlots/PNG/trajectory_formula_size_time_memory.png", os.path.join(paper_folder, "trajectory_formula_size_time_memory.png"))