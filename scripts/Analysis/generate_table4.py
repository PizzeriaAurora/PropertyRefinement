"""
Generate a transposed LaTeX table with benchmarks as rows and metrics as columns.

This is the EXACT transposed version of generate_table2.py.
Rows: Benchmark sets (Total, MCC2018, MCC2019, etc.)
Columns: Metrics (same as in generate_table2.py)

Usage:
  from Analysis.generate_table4 import generate_benchmark_table_transposed
  generate_benchmark_table_transposed(summary_csv_path, output_folder)
"""

from pathlib import Path
import pandas as pd


# EXACT same metrics as generate_table2.py
METRICS = [
    ("Total Number of Properties", "Total number of properties"),
    ("Number of Specification Files", "Total number of benchmarks"),
    ("Total Refinements", "Total refinements"),
    ("Average PRP (\\%)", "Average reduction (%)"),
    ("Zero-\\% Benchmarks", "Percentage Zero Properties Removed"),
    ("Avg. Refinement Time (s)", "Average refinement time (s)"),
    ("Avg. Ref. Time (Zero Cases)", "Average refinement time for zero properties removed"),
    ("Avg. Formula Length", "AvgSize"),
    ("Avg. Atomic Complexity", "AvgAtomicComplexity"),
    ("Average Memory (MB)", "Memory MB"),
]


def fmt_val(v):
    """Format a value for LaTeX table."""
    if pd.isna(v):
        return "--"
    try:
        if float(v).is_integer():
            return str(int(float(v)))
    except Exception:
        pass
    try:
        fv = float(v)
        return f"{fv:.2f}"
    except Exception:
        return str(v)


def generate_benchmark_table_transposed(summary_csv_path: str, output_folder: str = "."):
    """
    Generate a transposed LaTeX table with benchmarks as rows.
    
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
    
    # Read overall summary for "Total" row
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
            
            for other_bench in benchmark_order:
                if other_bench == 'Total':
                    continue
                # Find the formula info file for this benchmark
                raw_name = other_bench.replace("MCC", "") if other_bench.startswith("MCC") else other_bench
                if raw_name == "Rers":
                    raw_name = "ParallelRers2019Ctl"
                elif raw_name == "RersInd":
                    raw_name = "Rers2019Ind"
                info_file = formula_info_folder / f"info_per_file_{raw_name}.csv"
                
                if info_file.exists():
                    info_df = pd.read_csv(info_file)
                    if not info_df.empty:
                        total_props += info_df['NumProperties'].sum()
                        total_size += (info_df['TotalSize']).sum()
                        total_complexity += (info_df['AvgAtomicComplexity'] * info_df['NumProperties']).sum()
                        count += info_df['NumProperties'].sum()
            
            if count > 0:
                all_data['Total']['AvgSize'] = total_size / count
                all_data['Total']['AvgAtomicComplexity'] = total_complexity / count
        else:
            # Find the formula info file for this benchmark
            raw_name = bench_name.replace("MCC", "") if bench_name.startswith("MCC") else bench_name
            if raw_name == "Rers":
                raw_name = "ParallelRers2019Ctl"
            elif raw_name == "RersInd":
                raw_name = "Rers2019Ind"
            info_file = formula_info_folder / f"info_per_file_{raw_name}.csv"
            
            if info_file.exists():
                info_df = pd.read_csv(info_file)
                if not info_df.empty:
                    # Compute weighted averages
                    total_props = info_df['NumProperties'].sum()
                    all_data[bench_name]['AvgSize'] = (info_df['TotalSize']).sum() / total_props
                    all_data[bench_name]['AvgAtomicComplexity'] = \
                        (info_df['AvgAtomicComplexity'] * info_df['NumProperties']).sum() / total_props
    
    # Start building LaTeX table (TRANSPOSED)
    out = []
    out.append('\\begin{table*}[t]')
    out.append('\\centering')
    out.append('\\caption{Analysis Metrics by Benchmark Set (Transposed)}\\label{tab:benchmark_metrics_transposed}')
    
    # Column specification: benchmark name + one column per metric
    n_metrics = len(METRICS)
    col_spec = 'l ' + ' '.join(['r'] * n_metrics)
    out.append(f"\\begin{{tabular}}{{{col_spec}}}")
    out.append('\\toprule')
    
    # Header row with metric names
    header = ['\\textbf{Benchmark}'] + [f'\\textbf{{{label}}}' for label, _ in METRICS]
    out.append(' & '.join(header) + ' \\\\')
    out.append('\\midrule')
    
    # Add rows for each benchmark
    for bench in benchmark_order:
        cells = [f'\\textbf{{{bench}}}']
        bench_data = all_data.get(bench, {})
        
        for label, metric_key in METRICS:
            if metric_key in bench_data:
                cells.append(fmt_val(bench_data[metric_key]))
            else:
                cells.append("--")
        
        out.append(' & '.join(cells) + ' \\\\')
    
    # Add the "Highest PRP (%)" row
    out.append('\\midrule')
    
    # Find the highest reduction value across all benchmarks
    highest_reduction_value = 0
    for bench in benchmark_order:
        if bench == 'Total':
            continue
        bench_data = all_data.get(bench, {})
        if "Highest Reduction" in bench_data:
            try:
                val = float(bench_data["Highest Reduction"])
                if val > highest_reduction_value:
                    highest_reduction_value = val
            except (ValueError, TypeError):
                pass
    
    # Create row
    cells = ['\\textbf{Highest PRP (\\%)}']
    for label, metric_key in METRICS:
        if metric_key == "Average reduction (%)":
            # This column shows the highest reduction values
            cells.append(f'\\textbf{{{fmt_val(highest_reduction_value)}}}')
        else:
            cells.append('--')
    out.append(' & '.join(cells) + ' \\\\')
    
    # Add the "Lowest Avg. Time (s)" row
    time_metric = "Average refinement time (s)"
    overall_best_time = float('inf')
    for bench in benchmark_order:
        if bench == 'Total':
            continue
        bench_data = all_data.get(bench, {})
        if time_metric in bench_data:
            try:
                val = float(bench_data[time_metric])
                if val < overall_best_time:
                    overall_best_time = val
            except (ValueError, TypeError):
                pass
    
    # Create row
    cells = ['\\textbf{Lowest Avg. Time (s)}']
    for label, metric_key in METRICS:
        if metric_key == time_metric:
            # This column shows the lowest time
            cells.append(f'\\textbf{{{fmt_val(overall_best_time)}}}')
        else:
            cells.append('--')
    out.append(' & '.join(cells) + ' \\\\')
    
    out.append('\\bottomrule')
    out.append('\\end{tabular}')
    out.append('\\end{table*}')
    
    # Write to file
    output_path = output_path_obj / "benchmark_table_transposed.tex"
    with open(output_path, "w") as f:
        f.write('\n'.join(out))
    
    print(f"LaTeX table (transposed) written to: {output_path}")


if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("Usage: python generate_table4.py <summary_csv_path> [output_folder]")
        sys.exit(1)
    
    csv_path = Path(sys.argv[1])
    output_folder = sys.argv[2] if len(sys.argv) > 2 else "."
    
    generate_benchmark_table_transposed(csv_path, output_folder)
