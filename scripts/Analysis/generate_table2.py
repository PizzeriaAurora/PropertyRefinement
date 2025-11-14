"""
Generate a LaTeX table from summary CSV files with benchmark sets as columns.

This table shows metrics for different benchmark sets (MCC2018, MCC2019, etc.) in a single analysis run.
Columns: Total + individual benchmarks. Rows: various metrics.

Usage:
  from Analysis.generate_table2 import generate_benchmark_table
  generate_benchmark_table(summary_csv_path, output_folder)

Metrics included:
  - Total number of properties
  - Number of specification suites
  - Average formula length
  - Average atomic complexity
  - Average reduction (%)
  - PRP (%) without zero-reduction cases
  - Total refinements
  - Average refinement time (s)
  - Average refinement time for zero-reduction cases
  - Zero-% Benchmarks
  - ETT (Transitive Elimination Total)
"""

from pathlib import Path
import pandas as pd


METRICS = [
    ("Total Number of Properties", "Total number of properties"),
    ("Number of Specification Files", "Total number of benchmarks"),
    ("Total Refinements", "Total refinements"),
    ("Average PRP (\\%)", "Average reduction (%)"),
    ("Zero-\\% Benchmarks", "Percentage Zero Properties Removed"),
    ("Avg. Refinement Time (s)", "Average refinement time (s)"),
    ("Avg. Ref. Time (Zero Cases)", "Average refinement time for zero properties removed"),
    ("Avg. Formula Length", "AvgSize"),  # From formula info
    ("Avg. Atomic Complexity", "AvgAtomicComplexity"),  # From formula info
    ("Average Memory (MB)", "Memory MB"),
]


def fmt_val(v):
    """Format a value for LaTeX table."""
    if pd.isna(v):
        return "--"
    # integers as ints
    try:
        if float(v).is_integer():
            return str(int(float(v)))
    except Exception:
        pass
    # otherwise round to 2 decimal places for readability
    try:
        fv = float(v)
        return f"{fv:.2f}"
    except Exception:
        return str(v)


def generate_benchmark_table(summary_csv_path: str, output_folder: str = "."):
    """
    Generate a LaTeX table with benchmark sets as columns.
    
    Args:
        summary_csv_path: Path to the overall_summary.csv file
        output_folder: Directory to save the output table and where summary/ subfolder exists
    """
    output_path_obj = Path(output_folder)
    summary_folder = output_path_obj / "summary"
    
    # Find all individual benchmark summary files
    benchmark_files = sorted(summary_folder.glob("*_summary.csv"))
    
    # Dictionary to store all data: benchmark_name -> {metric: value}
    all_data = {}
    benchmark_order = []
    
    # Read overall summary for "Total" column
    overall_df = pd.read_csv(summary_csv_path)
    overall_metrics = {}
    for _, row in overall_df.iterrows():
        overall_metrics[row['Metric']] = row['Value']
    all_data['Total'] = overall_metrics
    benchmark_order.append('Total')
    
    # Read each benchmark summary
    for bench_file in benchmark_files:
        # Extract benchmark name (e.g., "2018_summary.csv" -> "2018")
        bench_name = bench_file.stem.replace("_summary", "")
        print(bench_name)
        # Add "MCC" prefix only if it's a 4-digit year
        if bench_name.isdigit() and len(bench_name) == 4:
            display_name = f"MCC{bench_name}"
        elif bench_name == "ParallelRers2019Ctl":
            display_name = "Rers"
        elif bench_name == "Rers2019Ind":
            display_name = "RersInd"
        else:
            display_name = bench_name
        
        # Read benchmark summary CSV
        bench_df = pd.read_csv(bench_file)
        bench_metrics = {}
        for _, row in bench_df.iterrows():
            bench_metrics[row['Metric']] = row['Value']
        
        all_data[display_name] = bench_metrics
        benchmark_order.append(display_name)
    
    # Load formula info for each benchmark from assets/formula_info/
    formula_info_folder = Path("assets/formula_info")
    
    for bench_name in benchmark_order:
        if bench_name == 'Total':
            # For total, compute aggregated formula info across all benchmarks
            total_props = 0
            total_size = 0
            total_complexity = 0
            count = 0
            total_memory = 0
            
            for other_bench in benchmark_order:
                if other_bench == 'Total':
                    continue
                # Find the formula info file for this benchmark
                raw_name = other_bench.replace("MCC", "") if other_bench.startswith("MCC") else other_bench
                info_file = formula_info_folder / f"info_per_file_{raw_name}.csv"
                
                if info_file.exists():
                    info_df = pd.read_csv(info_file)
                    if not info_df.empty:
                        total_props += info_df['NumProperties'].sum()
                        total_size += (info_df['TotalSize']).sum()
                        total_complexity += (info_df['AvgAtomicComplexity'] * info_df['NumProperties']).sum()
                        count += info_df['NumProperties'].sum()
                        #total_memory += info_df['Memory KB'].mean() 
            
            if count > 0:
                all_data['Total']['AvgSize'] = total_size / count
                all_data['Total']['AvgAtomicComplexity'] = total_complexity / count
                #all_data['Total']['Average Memory (MB)'] = total_memory / count / 1024  # Convert kB to MB
        else:
            # Find the formula info file for this benchmark
            raw_name = bench_name.replace("MCC", "") if bench_name.startswith("MCC") else bench_name
            raw_name = "Rers2019Ind" if bench_name == "RersInd" else raw_name
            raw_name = "ParallelRers2019Ctl" if bench_name == "Rers" else raw_name
            info_file = formula_info_folder / f"info_per_file_{raw_name}.csv"
            print(bench_name, info_file)
            if info_file.exists():
                info_df = pd.read_csv(info_file)
                if not info_df.empty:
                    # Compute weighted averages
                    total_props = info_df['NumProperties'].sum()
                    all_data[bench_name]['AvgSize'] = (info_df['TotalSize']).sum() / total_props
                    all_data[bench_name]['AvgAtomicComplexity'] = \
                        (info_df['AvgAtomicComplexity'] * info_df['NumProperties']).sum() / total_props
                    #all_data[bench_name]["Average Memory (MB)"] = info_df['Memory KB'].mean() / 1024  # Convert kB to MB
    
    # Start building LaTeX table
    out = []
    out.append('\\begin{table*}[t]')
    out.append('\\centering')
    out.append('\\caption{Analysis Metrics by Benchmark Set}\\label{tab:benchmark_metrics}')
    
    # Column specification: metric name + one column per benchmark
    n_cols = len(benchmark_order)
    col_spec = 'l ' + ' '.join(['r'] * n_cols)
    out.append(f"\\begin{{tabular}}{{{col_spec}}}")
    out.append('\\toprule')
    
    # Header row
    header = ['\\textbf{Metric}'] + [f'\\textbf{{{b}}}' for b in benchmark_order]
    out.append(' & '.join(header) + ' \\\\')
    #out.append('\\midrule')
    
    # Add rows for each metric
    for label, metric_key in METRICS:
        if label == "Spec. Suites":
            label_name = "Number of Specification Files"
        elif label == "Avg. Reduction (\%)":
            label_name = "Average PRP (\%)"
        elif label == "Total Properties":
            label_name = "Total Number of Properties"
        else:
            label_name = label
        cells = [label_name]
        
        for bench in benchmark_order:
            bench_data = all_data.get(bench, {})
            if metric_key in bench_data:
                cells.append(fmt_val(bench_data[metric_key]))
            else:
                cells.append("--")
        
        out.append(' & '.join(cells) + ' \\\\')
    
    # Add row for highest PRP reduction per benchmark
    #out.append('\\midrule')
    prp_metric = "Average reduction (%) - Non-Zero Only"
    
    
    

    highest_reduction_value = -1
    for bench in benchmark_order:
        if bench == 'Total':
            continue
        bench_data = all_data.get(bench, {})
        if "Highest Reduction" in bench_data:
            val = bench_data["Highest Reduction"]
            try:
                if float(val) > highest_reduction_value:
                    highest_reduction_value = float(val)
            except (ValueError, TypeError):
                pass


    # Create the row showing Highest Reduction value for each benchmark
    cells = ['Highest PRP (\\%)']
    for bench in benchmark_order:
        if bench == 'Total':
            cells.append('--')
        else:
            bench_data = all_data.get(bench, {})
            if "Highest Reduction" in bench_data:
                val = bench_data["Highest Reduction"]
                try:
                    # Bold the highest value
                    if float(val) == highest_reduction_value:
                        cells.append(f'{fmt_val(val)}')
                    else:
                        cells.append(fmt_val(val))
                except (ValueError, TypeError):
                    cells.append('--')
            else:
                cells.append('--')

    out.append(' & '.join(cells) + ' \\\\')

    # Add row for lowest average refinement time per benchmark
    time_metric = "Average refinement time (s)"
    
    # Find the overall lowest time value across all benchmarks
    overall_best_time = float('inf')
    for bench in benchmark_order:
        if bench == 'Total':
            continue
        bench_data = all_data.get(bench, {})
        if time_metric in bench_data:
            val = bench_data[time_metric]
            try:
                if float(val) < overall_best_time:
                    overall_best_time = float(val)
            except (ValueError, TypeError):
                pass
    
                

    # Create the row showing time value for each benchmark
    cells = ['Lowest Avg. Time (s)']
    for bench in benchmark_order:
        if bench == 'Total':
            cells.append('--')
        else:
            bench_data = all_data.get(bench, {})
            if time_metric in bench_data:
                val = bench_data[time_metric]
                try:
                    # Bold the lowest value
                    if float(val) == overall_best_time:
                        cells.append(f'\\textbf{{{fmt_val(val)}}}')
                    else:
                        cells.append(fmt_val(val))
                except (ValueError, TypeError):
                    cells.append('--')
            else:
                cells.append('--')

    
    
    out.append(' & '.join(cells) + ' \\\\')
    out.append('\\bottomrule')
    out.append('\\end{tabular}')
    out.append('\\end{table*}')
    
    # Write to file
    output_path = output_path_obj / "benchmark_table.tex"
    with open(output_path, "w") as f:
        f.write('\n'.join(out))
    
    print(f"LaTeX table written to: {output_path}")


if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("Usage: python generate_table2.py <summary_csv_path> [output_folder]")
        sys.exit(1)
    
    csv_path = Path(sys.argv[1])
    output_folder = sys.argv[2] if len(sys.argv) > 2 else "."
    
    generate_benchmark_table(csv_path, output_folder)
