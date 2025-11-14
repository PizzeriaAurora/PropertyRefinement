"""
Generate a LaTeX table with grouped column headers.

Top header: MCC (spanning year columns) | RERS (spanning 2 columns)
Second header: 2018, 2019, 2020, ... | Acad. | Ind.

Usage:
  from Analysis.generate_table3 import generate_benchmark_table_v2
  generate_benchmark_table_v2(summary_csv_path, output_folder)
"""

from pathlib import Path
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import shutil

from .utils import save_fig_helper



METRICS = [
    ("Total Properties", "Total number of properties"),
    ("Specification Files", "Total number of benchmarks"),
    ("Total Refinements", "Total refinements"),
    ("Avg. PRP (\\%)", "Average reduction (%)"),
    ("Avg. Refinement Time (s)", "Average refinement time (s)"),
    ("Zero-\\% Benchmarks", "Percentage Zero Properties Removed"),
    ("PRP (Non-Zero Cases) (\\%) ", "Average reduction (%) - Non-Zero Only"),
    #("Avg. Refinement Time (Zero Cases)", "Average refinement time for zero properties removed"),
    ("Avg. Formula Length", "AvgSize"),
    ("Avg. Atomic Complexity", "AvgAtomicComplexity"),
    ("Average Memory (MB)", "Memory MB"),
    #("ETT", "Transitive Elimination"),
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


def generate_benchmark_table_v2(summary_csv_path: str, output_folder: str = "."):
    """
    Generate a LaTeX table with grouped column headers.
    
    Args:
        summary_csv_path: Path to the overall_summary.csv file
        output_folder: Directory to save the output table and where summary/ subfolder exists
    """
    output_path_obj = Path(output_folder)
    summary_folder = output_path_obj / "summary"
    
    # Find all individual benchmark summary files
    benchmark_files = sorted(summary_folder.glob("*_summary.csv"))
    
    # Separate MCC years and RERS benchmarks
    mcc_benchmarks = []
    rers_benchmarks = []
    all_data = {}
    benchmark_order = []
    benchmark_order.append('Total')
    # Read each benchmark summary
    for bench_file in benchmark_files:
        bench_name = bench_file.stem.replace("_summary", "")
        
        # Read benchmark summary CSV
        bench_df = pd.read_csv(bench_file)
        bench_metrics = {}
        for _, row in bench_df.iterrows():
            bench_metrics[row['Metric']] = row['Value']
        
        # Categorize benchmarks
        if bench_name.isdigit() and len(bench_name) == 4:
            # MCC year
            mcc_benchmarks.append((bench_name, bench_metrics))
        elif bench_name == "ParallelRers2019Ctl":
            rers_benchmarks.append(("Acad.", bench_metrics))
        elif bench_name == "Rers2019Ind":
            rers_benchmarks.append(("Ind.", bench_metrics))
        
        all_data[bench_name] = bench_metrics
        benchmark_order.append(bench_name)
    
    # Sort MCC benchmarks by year
    mcc_benchmarks.sort(key=lambda x: x[0])
    
    # Load formula info for each benchmark
    formula_info_folder = Path("assets/formula_info")
    
    for bench_name in all_data.keys():
        info_file = formula_info_folder / f"info_per_file_{bench_name}.csv"
        
        if info_file.exists():
            info_df = pd.read_csv(info_file)
            if not info_df.empty:
                total_props = info_df['NumProperties'].sum()
                if total_props > 0:
                    all_data[bench_name]['AvgSize'] = (info_df['TotalSize']).sum() / total_props
                    all_data[bench_name]['AvgAtomicComplexity'] = \
                        (info_df['AvgAtomicComplexity'] * info_df['NumProperties']).sum() / total_props

    # Include average of all the benchmarks
    all_data['Total'] = {}
    for metric in METRICS:
        label, key = metric
        if label in ["Total Properties","Specification Files", "Total Refinements" ]:
            all_data['Total'][key] = sum(float(all_data[bench].get(key, 0)) for bench in benchmark_order)
        else:
            all_data['Total'][key] = sum(float(all_data[bench].get(key, 0)) for bench in benchmark_order) / len(benchmark_order)

    # Start building LaTeX table
    out = []
    out.append('\\begin{table*}[t]')
    out.append('\\centering')
    out.append('\\caption{Analysis Metrics by Benchmark Set}\\label{tab:benchmark_metrics_grouped}')
    
    # Column specification
    n_mcc = len(mcc_benchmarks)
    n_rers = len(rers_benchmarks)
    col_spec = 'l |c |' + ' '.join(['c'] * (n_mcc))
    col_spec += '| ' + ' '.join(['c'] * n_rers)
    out.append(f"\\begin{{tabular}}{{{col_spec}}}")
    out.append('\\toprule')
    
    # Top header row with multicolumn
    top_header = ['\\multirow{2}{*}{\\textbf{Metric}}']
    top_header.append('\\multirow{2}{*}{\\textbf{Total}}')
    if n_mcc > 0:
        top_header.append(f'\\multicolumn{{{n_mcc}}}{{c|}}{{\\textbf{{MCC}}}}')
    if n_rers > 0:
        top_header.append(f'\\multicolumn{{{n_rers}}}{{c}}{{\\textbf{{RERS}}}}')
    out.append(' & '.join(top_header) + ' \\\\')
    
    # Second header row with individual years/benchmarks
    # Empty cell for the metric column (handled by multirow)
    second_header = ['&']
    
    # Add MCC years
    for year, _ in mcc_benchmarks:
        second_header.append(f'\\textbf{{{year}}}')
    
    # Add RERS benchmarks
    for name, _ in rers_benchmarks:
        second_header.append(f'\\textbf{{{name}}}')
    
    out.append(' & '.join(second_header) + ' \\\\')
    out.append('\\midrule')
    
    # Add rows for each metric
    for label, metric_key in METRICS:
        cells = [label]
        
        # Add Total column
        if metric_key in all_data['Total']:
            cells.append(fmt_val(all_data['Total'][metric_key]))

        # Add MCC values
        for year, bench_data in mcc_benchmarks:
            if metric_key in bench_data:
                cells.append(fmt_val(bench_data[metric_key]))
            else:
                cells.append("--")
        
        # Add RERS values
        for name, bench_data in rers_benchmarks:
            if metric_key in bench_data:
                cells.append(fmt_val(bench_data[metric_key]))
            else:
                cells.append("--")
        
        out.append(' & '.join(cells) + ' \\\\')
    
    # Add row for highest PRP reduction per benchmark
    #out.append('\\midrule')
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
     # Create new row for average time per property 
    all_data['Total']["Average refinement time (ms)"] = 0
    for bench in benchmark_order:
        if bench == 'Total':
            continue
        bench_data = all_data.get(bench, {})
        if "Average refinement time (ms)" in bench_data and "Total number of properties" in bench_data:
            val = float(bench_data["Average refinement time (ms)"]) / float(bench_data["Total number of properties"])
            all_data['Total']["Average refinement time (ms)"] += val 
    all_data['Total']["Average refinement time (ms)"] /= (len(benchmark_order)-1)
    cells = ["Average Time per Property Pair (ms)"]
    for bench in benchmark_order:
        if bench == 'Total':
            cells.append('--')
        else:
            bench_data = all_data.get(bench, {})
            val = float(bench_data["Average refinement time (ms)"]) / float(bench_data["Total number of properties"])
            cells.append(fmt_val(val))
                
    
    #
    out.append(' & '.join(cells) + ' \\\\')

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
                        cells.append(fmt_val(val))
                    else:
                        cells.append(fmt_val(val))
                except (ValueError, TypeError):
                    cells.append('--')
            else:
                cells.append('--')

    out.append(' & '.join(cells) + ' \\\\')
    
    # Add row for lowest refinement time
    time_metric = "Average refinement time (s)"
    
    # Find overall lowest time value
    overall_best_time = float('inf')
    for bench_data in [bd for _, bd in mcc_benchmarks] + [bd for _, bd in rers_benchmarks]:
        if time_metric in bench_data:
            try:
                val = float(bench_data[time_metric])
                if val < overall_best_time:
                    overall_best_time = val
            except (ValueError, TypeError):
                pass
    
   
    out.append('\\bottomrule')
    out.append('\\end{tabular}')
    out.append('\\end{table*}')
    
    # Write to file
    output_path = output_path_obj / "benchmark_table_grouped.tex"
    with open(output_path, "w") as f:
        f.write('\n'.join(out))
    
    print(f"LaTeX table (grouped) written to: {output_path}")
    
    # Generate the aggregated breakdown plot using the same data source
    create_averagetime_breakdown_per_category_aggregated(all_data, output_folder)


def create_averagetime_breakdown_per_category_aggregated(all_data: dict, output_folder: str) -> None:
    """
    Create a bar plot breaking down average times and memory by reduction category.
    Uses benchmark-level aggregation (same methodology as tables) - for paper.
    Shows refinement time and memory usage.
    
    Args:
        all_data: Dictionary of benchmark data (same as used for table generation)
        output_folder: Directory to save the plot
    """
    print("Creating aggregated average time breakdown per category plot...")
    try:
        # Filter benchmarks into categories based on reduction percentage
        categories = {
            'Average': [],
            '0%': [],
            '0-25%': [],
            '25-50%': [],
            '>50%': []
        }
        
        # Categorize each benchmark by its average reduction percentage
        for bench_name, bench_metrics in all_data.items():
            if bench_name == 'Total':
                continue
            
            # Convert to float to handle string values from CSV
            try:
                reduction_pct = float(bench_metrics.get('Average reduction (%)', 0))
                refinement_time = float(bench_metrics.get('Average refinement time (s)', 0))
                memory = float(bench_metrics.get('Memory MB', 0))
            except Exception as e:
                print(f"Skipping benchmark {bench_name} due to data error: {e}")
            
            # Add to Average category
            categories['Average'].append({'time': refinement_time, 'memory': memory})
            
            # Categorize by reduction percentage
            if reduction_pct == 0:
                categories['0%'].append({'time': refinement_time, 'memory': memory})
            elif 0 < reduction_pct < 25:
                categories['0-25%'].append({'time': refinement_time, 'memory': memory})
            elif 25 <= reduction_pct <= 50:
                categories['25-50%'].append({'time': refinement_time, 'memory': memory})
            elif reduction_pct > 50:
                categories['>50%'].append({'time': refinement_time, 'memory': memory})
        
        # Calculate average time and memory for each category
        category_data = {}
        for cat_name, benchmarks in categories.items():
            if len(benchmarks) > 0:
                avg_time = sum(b['time'] for b in benchmarks) / len(benchmarks)
                avg_memory = sum(b['memory'] for b in benchmarks) / len(benchmarks)
                category_data[cat_name] = {
                    'refinement_time': avg_time,
                    'memory': avg_memory
                }
            else:
                category_data[cat_name] = {
                    'refinement_time': 0,
                    'memory': 0
                }
        
        # Create the plot with dual y-axes
        fig, ax1 = plt.subplots(figsize=(3.2, 2.5))
        
        # Prepare data for plotting
        categories_list = list(category_data.keys())
        x_pos = np.arange(len(categories_list))
        
        # Extract values
        refinement_times = [category_data[cat]['refinement_time'] for cat in categories_list]
        memory_usage = [category_data[cat]['memory'] for cat in categories_list]
        
        # Set bar width
        bar_width = 0.35
        
        # Plot memory on first y-axis (left)
        bars1 = ax1.bar(x_pos - bar_width/2, memory_usage, bar_width, 
                       color='darkgray', label='Memory (MB)', alpha=0.8)
        ax1.set_xlabel('Property Reduction Percentage', fontsize=8, labelpad=1)
        ax1.set_ylabel('Memory (MB)', fontsize=8, labelpad=1, color='darkgray')
        ax1.tick_params(axis='y', labelcolor='darkgray', labelsize=8, pad=0)
        ax1.tick_params(axis='x', labelsize=8, pad=1)
        ax1.set_xticks(x_pos)
        ax1.set_xticklabels(categories_list, fontsize=8)
        
        # Create second y-axis (right) for time
        ax2 = ax1.twinx()
        bars2 = ax2.bar(x_pos + bar_width/2, refinement_times, bar_width,
                       color='gray', hatch='///', label='Refinement Time (s)', alpha=0.7)
        ax2.set_ylabel('Refinement Time (s)', fontsize=8, labelpad=1, color='gray')
        ax2.tick_params(axis='y', labelcolor='gray', labelsize=8, pad=0)
        
        # Add legends
        lines1, labels1 = ax1.get_legend_handles_labels()
        lines2, labels2 = ax2.get_legend_handles_labels()
        ax1.legend(lines1 + lines2, labels1 + labels2, fontsize=7, loc='upper left')
        
        # Add grid on left axis
        ax1.grid(True, alpha=0.3, axis='y')
        ax1.set_axisbelow(True)
        
        fig.tight_layout()
        print("Saving aggregated average time breakdown plot... in "+output_folder)
        save_fig_helper('average_time_breakdown_per_category_aggregated', output_folder)
        
        ## Copy to paper_stuff folder
        #import shutil
        #paper_folder = Path(output_folder).parent / 'paper_stuff'
        #paper_folder.mkdir(exist_ok=True)
        #
        ## Copy PGF version if it exists
        #pgf_file = Path(output_folder) / 'PGF' / 'average_time_breakdown_per_category_aggregated.pgf'
        #if pgf_file.exists():
        #    shutil.copy(pgf_file, paper_folder / 'average_time_breakdown_per_category_aggregated.pgf')
        #    print(f"Copied aggregated breakdown plot to {paper_folder}")
        
    except Exception as e:
        print(f"Error creating aggregated timing breakdown plot: {e}")
        import traceback
        traceback.print_exc()
        return







if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("Usage: python generate_table3.py <summary_csv_path> [output_folder]")
        sys.exit(1)
    
    csv_path = Path(sys.argv[1])
    output_folder = sys.argv[2] if len(sys.argv) > 2 else "."
    
    generate_benchmark_table_v2(csv_path, output_folder)
