import os
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import math
import warnings
from typing import Dict, List, Tuple
import glob
from pathlib import Path
from tqdm import tqdm

from .utils import save_fig_helper, categorize_benchmarks

# Suppress noisy numpy warnings (polyfit RankWarning message, and invalid value RuntimeWarning)
with warnings.catch_warnings():
    # numpy does not always expose a RankWarning symbol; filter by message instead
    warnings.filterwarnings('ignore', message='Polyfit may be poorly conditioned')
    warnings.simplefilter('ignore', RuntimeWarning)

textwidth_in = 6.75
figsize=(textwidth_in, textwidth_in * 0.6)
markers = ['o', 's', '^', 'D', 'v', 'x']
cmap = plt.get_cmap('tab20')
colors = [cmap(i) for i in range(cmap.N)]

def get_valid_mem(df):
    return  df[
            (df['Refinement_Time_s'] > 0) & (df['Refinement_Time_s'] < 10e12) &
            (df['AvgSize'] > 0) & 
            (df['AvgAtomicComplexity'] > 0)
        ].copy()


def create_reduction_distribution_plot(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create a histogram showing the distribution of property reduction percentages.
    """
    plt.figure(figsize=(10, 6))
    
    # Create histogram with grayscale
    n, bins, patches = plt.hist(df['Reduction_Percentage'], bins=20, alpha=0.7, 
                               color='lightgray', edgecolor='black', density=False)
    
    # Add statistical lines
    mean_reduction = df['Reduction_Percentage'].mean()
    median_reduction = df['Reduction_Percentage'].median()
    
    plt.axvline(mean_reduction, color='black', linestyle='--', linewidth=2, 
               label=f'Mean: {mean_reduction:.1f}%')
    plt.axvline(median_reduction, color='black', linestyle='-', linewidth=2, 
               label=f'Median: {median_reduction:.1f}%')
    
    # Add quartile information
    q25 = df['Reduction_Percentage'].quantile(0.25)
    q75 = df['Reduction_Percentage'].quantile(0.75)
    plt.axvline(q25, color='gray', linestyle=':', alpha=0.7, 
               label=f'Q1: {q25:.1f}%')
    plt.axvline(q75, color='gray', linestyle=':', alpha=0.7, 
               label=f'Q3: {q75:.1f}%')

    plt.xlabel('Property Reduction Percentage (%)', fontsize=8, labelpad=1)
    plt.ylabel('Number of Benchmarks', fontsize=8, labelpad=1)
    plt.legend(fontsize=8)
    plt.grid(True, alpha=0.3)
    plt.tick_params(axis='x', which='major', pad=1)          # controls spacing
    plt.tick_params(axis='y', which='major', pad=0)
    plt.xticks(fontsize=8)   # controls font size of x-tick labels
    plt.yticks(fontsize=8)   # same for y
    
    # Add statistics text box
    total_benchmarks = len(df)
    significant_reduction = len(df[df['Reduction_Percentage'] >= 25])
    high_reduction = len(df[df['Reduction_Percentage'] >= 50])
    
    stats_text = f"""Key Statistics:
Total Benchmarks: {total_benchmarks}
≥25% Reduction: {significant_reduction} ({significant_reduction/total_benchmarks*100:.1f}%)
≥50% Reduction: {high_reduction} ({high_reduction/total_benchmarks*100:.1f}%)
Max Reduction: {df['Reduction_Percentage'].max():.1f}%"""
    
    plt.text(0.7, 0.98, stats_text, transform=plt.gca().transAxes, 
            fontsize=10, verticalalignment='top', horizontalalignment='right',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    
    plt.tight_layout()
    save_fig_helper('property_reduction_distribution', output_folder)


def create_properties_vs_size_plot(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create scatter plot showing properties eliminated vs benchmark size.
    """
    plt.figure(figsize=(10, 6))
    
    # Create scatter plot with different markers for different categories
    
    
    categories = df['Category'].unique()
    for i, category in enumerate(categories):
        if pd.isna(category):
            continue
        cat_data = df[df['Category'] == category]
        plt.scatter(cat_data['Total_Properties'], cat_data['Properties_Eliminated'], 
                   marker=markers[i % len(markers)], 
                   color=colors[i % len(colors)],
                   s=80, alpha=0.7, 
                   label=f'{category} (n={len(cat_data)})')
    
    # Add trend line
    valid_mask = (df['Total_Properties'] > 0) & (df['Properties_Eliminated'] >= 0)
    if valid_mask.sum() > 1:
        # Suppress RankWarning and RuntimeWarning from poorly conditioned polyfit
        with warnings.catch_warnings():
            #warnings.simplefilter('ignore', np.RankWarning)
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df['Total_Properties'][valid_mask], 
                          df['Properties_Eliminated'][valid_mask], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df['Total_Properties'].min(), df['Total_Properties'].max(), 100)
            plt.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.2f})')
    
    plt.xlabel('Original Property Count')
    plt.ylabel('Properties Eliminated')
    #plt.yscale("log")
    plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left')
    plt.grid(True, alpha=0.3)
    
    # Add correlation coefficient
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr = df['Total_Properties'].corr(df['Properties_Eliminated'])
    plt.text(0.02, 0.98, f'Correlation: {corr:.3f}', 
            transform=plt.gca().transAxes, fontsize=10, 
            verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    
    plt.tight_layout()
    save_fig_helper('properties_eliminated_vs_size', output_folder)



def create_cumulative_reduction_plot(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create a cumulative plot showing total properties eliminated across benchmarks.
    """
    plt.figure(figsize=(10, 6))
    
    # Sort by reduction percentage (descending)
    df_sorted = df.sort_values('Reduction_Percentage', ascending=False).reset_index(drop=True)
    
    # Calculate cumulative properties eliminated
    cumulative_eliminated = df_sorted['Properties_Eliminated'].cumsum()
    total_original = df['Total_Properties'].sum()
    
    # Create main plot
    plt.plot(range(len(df_sorted)), cumulative_eliminated, 
            linewidth=3, color='black', marker='o', markersize=4, markevery=5)
    
    # Fill area under curve
    plt.fill_between(range(len(df_sorted)), cumulative_eliminated, 
                    alpha=0.3, color='lightgray')
    
    # Add key milestone markers
    milestones = [0.25, 0.5, 0.75]
    for milestone in milestones:
        target_props = total_original * milestone
        if cumulative_eliminated.iloc[-1] >= target_props:
            # Find where we cross this threshold
            cross_idx = (cumulative_eliminated >= target_props).idxmax()
            plt.axhline(y=target_props, color='gray', linestyle='--', alpha=0.7)
            plt.axvline(x=cross_idx, color='gray', linestyle='--', alpha=0.7)
            plt.text(cross_idx + 2, target_props, f'{milestone*100:.0f}% of total\n({cross_idx+1} benchmarks)', 
                    fontsize=9, verticalalignment='bottom')
    
    plt.xlabel('Benchmarks (Ordered by Reduction Rate)')
    plt.ylabel('Cumulative Properties Eliminated')
    plt.grid(True, alpha=0.3)
    
    # Add final statistics
    total_eliminated = cumulative_eliminated.iloc[-1]
    overall_reduction = (total_eliminated / total_original) * 100
    
    plt.text(0.02, 0.98, f'Total Properties Eliminated: {total_eliminated:,}\n'
                        f'Overall Reduction: {overall_reduction:.1f}%\n'
                        f'Original Total: {total_original:,}', 
            transform=plt.gca().transAxes, fontsize=10, 
            verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    
    plt.tight_layout()
    save_fig_helper('cumulative_properties_eliminated', output_folder)


def create_category_reduction_histogram(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create histogram showing average reduction by benchmark category.
    """
    # Calculate average reduction by category
    category_stats = df.groupby('Category').agg({
        'Reduction_Percentage': ['mean', 'std', 'count'],
        'Properties_Eliminated': 'sum',
        'Total_Properties': 'sum'
    }).round(2)

    #print(category_stats)
    
    # Flatten column names
    category_stats.columns = ['_'.join(col).strip() for col in category_stats.columns]
    category_stats = category_stats.reset_index()
    
    # Sort by average reduction
    category_stats = category_stats.sort_values('Reduction_Percentage_mean', ascending=True)
    
    plt.figure(figsize=(2.8, 2.5))
    
    # Create horizontal bar chart with grayscale
    bars = plt.barh(range(len(category_stats)), category_stats['Reduction_Percentage_mean'], 
                   color='lightgray', edgecolor='black', alpha=0.8)
    
    # Add error bars if std is available
    if 'Reduction_Percentage_std' in category_stats.columns:
        plt.errorbar(category_stats['Reduction_Percentage_mean'], range(len(category_stats)),
                    xerr=category_stats['Reduction_Percentage_std'], 
                    fmt='none', color='black', capsize=5, alpha=0.7)
    
    # Customize y-axis
    plt.yticks(range(len(category_stats)), 
              [f"{cat}\n(n={int(count)})" for cat, count in 
               zip(category_stats['Category'], category_stats['Reduction_Percentage_count'])])
    
    plt.xlabel('Average PRP')
    #plt.ylabel('Benchmark Category')
    plt.grid(True, alpha=0.3, axis='x')
    
    # Add value labels on bars
    for i, (bar, value, std) in enumerate(zip(bars, category_stats['Reduction_Percentage_mean'], 
                                             category_stats.get('Reduction_Percentage_std', [0]*len(bars)))):
        width = bar.get_width()
        plt.text(width + 1, bar.get_y() + bar.get_height()/2, 
                f'{value:.1f}%\n±{std:.1f}', 
                ha='left', va='center', fontsize=9)
    
    # Add overall statistics
    overall_mean = df['Reduction_Percentage'].mean()
    #plt.axvline(overall_mean, color='black', linestyle='--', linewidth=2, 
    #           label=f'Overall Mean: {overall_mean:.1f}%', alpha=0.7)
    #plt.legend()
    
    plt.tight_layout()
    save_fig_helper('category_reduction_histogram', output_folder)





def create_averagetime_breakdown_per_category(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create a bar plot breaking down average times by reduction category.
    """
    try:

        # Calculate average times for each category
        categories = {
            'Average': df,
            '0%': df[df['Reduction_Percentage'] ==0],
            '0-25%': df[(df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] < 25)],
            '25-50%': df[(df['Reduction_Percentage'] >= 25) & (df['Reduction_Percentage'] <= 50)],
            '>50%': df[df['Reduction_Percentage'] > 50]
        }
        
        # Calculate metrics for each category
        category_data = {}
        for cat_name, cat_data in categories.items():
            if len(cat_data) > 0:
                category_data[cat_name] = {
                    'refinement_time': cat_data['Refinement_Time_ms'].mean()/1000,
                    'total_time': cat_data['Total_Time_ms'].mean()/1000,
                    'count': len(cat_data)
                }
        
        # Create the plot
        plt.figure(figsize=(2.8, 2.5))
        
        # Prepare data for plotting
        categories_list = list(category_data.keys())
        x_pos = np.arange(len(categories_list))
        convert = 1
        # Extract values
        refinement_times = [category_data[cat]['refinement_time']/convert  for cat in categories_list]
        total_times = [category_data[cat]['total_time']/convert for cat in categories_list]
        
        # Calculate combined optimized + analysis overhead
        #combined_times = [opt + ana for opt, ana in zip(optimized_times, analysis_times)]
        
        # Set bar width
        bar_width = 0.35
        
        # Create bars
        bars1 = plt.bar(x_pos - bar_width/2, total_times, bar_width, 
                       color='darkgray', label='Total', alpha=0.8)
        
        # Create stacked bars for optimized + analysis overhead
        bars2 = plt.bar(x_pos + bar_width/2, refinement_times, bar_width,
                       color='gray', hatch='///',  label='Refinement \n Analysis', alpha=0.7)
        #bars3 = plt.bar(x_pos + bar_width/2, analysis_times, bar_width,
        #               bottom=optimized_times, color='black', 
        #               label='Refinement \n Analysis', alpha=0.8)
        
        # Customize the plot
        plt.xlabel('Property Reduction Percentage', fontsize=8, labelpad=1)
        plt.ylabel('Average Time (seconds)', fontsize=8, labelpad=1)
        plt.ylim(0,6)
        plt.xticks(x_pos, categories_list, fontsize=8)
        plt.yticks(fontsize=8)
        def percent_formatter_old(x, pos):
            import math
            return f'{x/1000:.0f}'
            #if x == 0:
            #    return '0'
            ## Calculate the exponent
            #exponent = int(math.floor(math.log10(abs(x))))
            ## Format as 10^exponent
            #return f'$10^{{{exponent}}}$'
        #from matplotlib.ticker import ScalarFormatter
        #formatter = ScalarFormatter(useMathText=True)
        #formatter.set_scientific(True)
        #formatter.set_powerlimits((0, 0))  # Force scientific notation for all values
        #plt.gca().yaxis.set_major_formatter(percent_formatter_old)
        #
        ##input()
        #offset_text = plt.gca().yaxis.get_offset_text()
 # inter#pret x,y in axes coords
        #offset_text.set_position((0.02, 0.1))   # (x,y) in axes coords
        #-0.14,
        #r"$\times10^3$"
        #plt.gca().text(0.02, 0.97, r"$\times1000$",
        #transform=plt.gca().transAxes,
        #ha="left", va="top", fontsize=8)

        plt.legend(fontsize=7, loc='upper left')
        
        # Add grid
        plt.grid(True, alpha=0.3, axis='y')
        
        
        plt.tick_params(axis='x', which='major', pad=1)
        plt.tick_params(axis='y', which='major', pad=0)
        
        # Adjust layout to accommodate annotations
        plt.ylim(0, max(max(refinement_times), max(total_times)) * 1.25)
        
        plt.tight_layout()
        
        save_fig_helper('average_time_breakdown_per_category', output_folder)
        
        # Print summary statistics
       
        
    except Exception as e:
        print(f"Error creating timing breakdown plot: {e}")
        import traceback
        traceback.print_exc()
        return


def create_complexity_time_plot(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create scatter plot showing relationship between formula complexity (length and atoms) and refinement time.
    Uses dual y-axis to show both metrics on the same plot.
    """
    try:
        # Check if complexity columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-time plot: Formula info not available")
            return
        
        # Filter valid data (non-zero time)
        valid_df = df[(df['Refinement_Time_ms'] > 0) & 
                      (df['AvgSize'].notna()) & 
                      (df['AvgAtomicComplexity'].notna())].copy()
        
        if len(valid_df) == 0:
            print("No valid data for complexity-time plot")
            return
        
        # Convert time to seconds
        valid_df['Refinement_Time_s'] = valid_df['Refinement_Time_ms'] / 1000
        
        # Create figure with two y-axes
        fig, ax1 = plt.subplots(figsize=(12, 6))
        ax2 = ax1.twinx()
        
        # Sort by formula length for better visualization
        valid_df = valid_df.sort_values('AvgSize')
        
        # Plot formula length vs time (primary axis)
        color1 = 'tab:blue'
        scatter1 = ax1.scatter(valid_df['AvgSize'], valid_df['Refinement_Time_s'],
                              alpha=0.5, s=50, color=color1, marker='o',
                              label='Time vs Length')
        ax1.set_xlabel('Average Formula Length', fontsize=10)
        ax1.set_ylabel('Refinement Time (s)', color=color1, fontsize=10)
        ax1.tick_params(axis='y', labelcolor=color1)
        ax1.set_yscale('log')
        ax1.grid(True, alpha=0.3, which='both')
        
        # Plot atomic complexity vs time (secondary axis)
        color2 = 'tab:red'
        scatter2 = ax2.scatter(valid_df['AvgAtomicComplexity'], valid_df['Refinement_Time_s'],
                              alpha=0.5, s=50, color=color2, marker='^',
                              label='Time vs Atomic Complexity')
        ax2.set_xlabel('Average Atomic Complexity', fontsize=10)
        ax2.set_ylabel('Refinement Time (s)', color=color2, fontsize=10)
        ax2.tick_params(axis='y', labelcolor=color2)
        ax2.set_yscale('log')
        
        # Add combined legend
        lines1, labels1 = ax1.get_legend_handles_labels()
        lines2, labels2 = ax2.get_legend_handles_labels()
        ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left', fontsize=9)
        
        plt.title('Refinement Time vs Formula Complexity', fontsize=12, pad=15)
        fig.tight_layout()
        save_fig_helper('complexity_vs_time', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-time plot: {e}")
        import traceback
        traceback.print_exc()


def create_complexity_memory_plot(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create scatter plot showing relationship between formula complexity (length and atoms) and memory usage.
    Uses dual y-axis to show both metrics on the same plot.
    """
    try:
        # Check if complexity and memory columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-memory plot: Formula info not available")
            return
        if ' Refinement_Memory_kB' not in df.columns:
            print("Skipping complexity-memory plot: Memory data not available")
            return
        
        # Filter valid data (non-zero memory)
        valid_df = df.copy()
        if len(valid_df) == 0:
            print("No valid data for complexity-memory plot")
            return
        
        # Convert memory to MB
        valid_df['Refinement_Memory_MB'] = valid_df[' Refinement_Memory_kB'] / 1024
        
        # Create figure with two y-axes
        fig, ax1 = plt.subplots(figsize=(12, 6))
        ax2 = ax1.twinx()
        
        # Sort by formula length for better visualization
        valid_df = valid_df.sort_values('AvgSize')
        
        # Plot formula length vs memory (primary axis)
        color1 = 'tab:green'
        scatter1 = ax1.scatter(valid_df['AvgSize'], valid_df['Refinement_Memory_MB'],
                              alpha=0.5, s=50, color=color1, marker='s',
                              label='Memory vs Length')
        ax1.set_xlabel('Average Formula Length', fontsize=10)
        ax1.set_ylabel('Refinement Memory (MB)', color=color1, fontsize=10)
        ax1.tick_params(axis='y', labelcolor=color1)
        ax1.set_yscale('log')
        ax1.grid(True, alpha=0.3, which='both')
        
        # Plot atomic complexity vs memory (secondary axis)
        color2 = 'tab:orange'
        scatter2 = ax2.scatter(valid_df['AvgAtomicComplexity'], valid_df['Refinement_Memory_MB'],
                              alpha=0.5, s=50, color=color2, marker='D',
                              label='Memory vs Atomic Complexity')
        ax2.set_xlabel('Average Atomic Complexity', fontsize=10)
        ax2.set_ylabel('Refinement Memory (MB)', color=color2, fontsize=10)
        ax2.tick_params(axis='y', labelcolor=color2)
        ax2.set_yscale('log')
        
        # Add combined legend
        lines1, labels1 = ax1.get_legend_handles_labels()
        lines2, labels2 = ax2.get_legend_handles_labels()
        ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left', fontsize=9)
        
        plt.title('Refinement Memory vs Formula Complexity', fontsize=12, pad=15)
        fig.tight_layout()
        save_fig_helper('complexity_vs_memory', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-memory plot: {e}")
        import traceback
        traceback.print_exc()


def create_complexity_time_hexbin(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create hexbin plots showing relationship between formula complexity and refinement time.
    Creates two subplots: one for length vs time, one for atomic complexity vs time.
    Hexagons are colored by average time in that region.
    """
    try:
        # Check if complexity and time columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-time hexbin: Formula info not available")
            return
        if 'Refinement_Time_s' not in df.columns:
            print("Skipping complexity-time hexbin: Time data not available")
            return
        
        # Filter valid data (non-zero time)
        valid_df = df[
            (df['Refinement_Time_s'] > 0) & 
            (df['AvgSize'] > 0) & 
            (df['AvgAtomicComplexity'] > 0)
        ].copy()
        
        if len(valid_df) < 10:
            print(f"Not enough valid data for complexity-time hexbin plot: {len(valid_df)} points")
            return
        
        # Create figure with two subplots
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        # Plot 1: Formula Length vs Time
        hb1 = ax1.hexbin(valid_df['AvgSize'], valid_df['Refinement_Time_s'],
                        gridsize=25, cmap='YlOrRd', mincnt=1,
                        xscale='linear', yscale='log', reduce_C_function=np.mean)
        ax1.set_xlabel('Average Formula Length', fontsize=11)
        ax1.set_ylabel('Refinement Time (s)', fontsize=11)
        ax1.set_title('Time vs Formula Length', fontsize=12)
        ax1.grid(True, alpha=0.3, which='both')
        cb1 = fig.colorbar(hb1, ax=ax1, label='Avg Time (s)')
        
        # Plot 2: Atomic Complexity vs Time
        hb2 = ax2.hexbin(valid_df['AvgAtomicComplexity'], valid_df['Refinement_Time_s'],
                        gridsize=25, cmap='YlOrRd', mincnt=1,
                        xscale='linear', yscale='log', reduce_C_function=np.mean)
        ax2.set_xlabel('Average Atomic Complexity', fontsize=11)
        ax2.set_ylabel('Refinement Time (s)', fontsize=11)
        ax2.set_title('Time vs Atomic Complexity', fontsize=12)
        ax2.grid(True, alpha=0.3, which='both')
        cb2 = fig.colorbar(hb2, ax=ax2, label='Avg Time (s)')
        
        plt.suptitle('Refinement Time vs Formula Complexity (Hexbin)', fontsize=14, y=1.02)
        fig.tight_layout()
        save_fig_helper('complexity_vs_time_hexbin', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-time hexbin plot: {e}")
        import traceback
        traceback.print_exc()


def create_complexity_memory_hexbin(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create hexbin plots showing relationship between formula complexity and memory usage.
    Creates two subplots: one for length vs memory, one for atomic complexity vs memory.
    Hexagons are colored by average memory in that region.
    """
    try:
        # Check if complexity and memory columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-memory hexbin: Formula info not available")
            return
        if ' Refinement_Memory_kB' not in df.columns:
            print("Skipping complexity-memory hexbin: Memory data not available")
            return
        
        # Filter valid data (non-zero memory)
        valid_df = df[
            (df[' Refinement_Memory_kB'] > 0) & 
            (df['AvgSize'] > 0) & 
            (df['AvgAtomicComplexity'] > 0)
        ].copy()
        
        if len(valid_df) < 10:
            print(f"Not enough valid data for complexity-memory hexbin plot: {len(valid_df)} points")
            return
        
        # Convert memory to MB
        valid_df['Refinement_Memory_MB'] = valid_df[' Refinement_Memory_kB'] / 1024
        
        # Create figure with two subplots
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(16, 6))
        
        # Plot 1: Formula Length vs Memory
        hb1 = ax1.hexbin(valid_df['AvgSize'], valid_df['Refinement_Memory_MB'],
                        gridsize=25, cmap='Greens', mincnt=1,
                        xscale='linear', yscale='log', reduce_C_function=np.mean)
        ax1.set_xlabel('Average Formula Length', fontsize=11)
        ax1.set_ylabel('Refinement Memory (MB)', fontsize=11)
        ax1.set_title('Memory vs Formula Length', fontsize=12)
        ax1.grid(True, alpha=0.3, which='both')
        cb1 = fig.colorbar(hb1, ax=ax1, label='Avg Memory (MB)')
        
        # Plot 2: Atomic Complexity vs Memory
        hb2 = ax2.hexbin(valid_df['AvgAtomicComplexity'], valid_df['Refinement_Memory_MB'],
                        gridsize=25, cmap='Greens', mincnt=1,
                        xscale='linear', yscale='log', reduce_C_function=np.mean)
        ax2.set_xlabel('Average Atomic Complexity', fontsize=11)
        ax2.set_ylabel('Refinement Memory (MB)', fontsize=11)
        ax2.set_title('Memory vs Atomic Complexity', fontsize=12)
        ax2.grid(True, alpha=0.3, which='both')
        cb2 = fig.colorbar(hb2, ax=ax2, label='Avg Memory (MB)')
        
        plt.suptitle('Refinement Memory vs Formula Complexity (Hexbin)', fontsize=14, y=1.02)
        fig.tight_layout()
        save_fig_helper('complexity_vs_memory_hexbin', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-memory hexbin plot: {e}")
        import traceback
        traceback.print_exc()


def create_complexity_time_contour(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create contour plot showing relationship between formula length, atomic complexity, and time.
    X-axis: Formula Length, Y-axis: Atomic Complexity, Colors: Time levels.
    """
    try:
        # Check if complexity and time columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-time contour: Formula info not available")
            return
        if 'Refinement_Time_s' not in df.columns:
            print("Skipping complexity-time contour: Time data not available")
            return
        
        # Filter valid data
        valid_df = df[
            (df['Refinement_Time_s'] > 0) & 
            (df['AvgSize'] > 0) & 
            (df['AvgAtomicComplexity'] > 0)
        ].copy()
        
        if len(valid_df) < 20:
            print(f"Not enough valid data for complexity-time contour plot: {len(valid_df)} points")
            return
        
        # Create grid for interpolation
        from scipy.interpolate import griddata
        
        x = valid_df['AvgSize'].values
        y = valid_df['AvgAtomicComplexity'].values
        z = valid_df['Refinement_Time_s'].values
        
        # Create regular grid
        xi = np.linspace(x.min(), x.max(), 100)
        yi = np.linspace(y.min(), y.max(), 100)
        xi_grid, yi_grid = np.meshgrid(xi, yi)
        
        # Interpolate Z values on the grid
        zi = griddata((x, y), z, (xi_grid, yi_grid), method='cubic', fill_value=np.nan)
        
        # Create contour plot
        fig, ax = plt.subplots(figsize=(12, 9))
        
        # Filled contour plot
        contourf = ax.contourf(xi_grid, yi_grid, zi, levels=20, cmap='viridis', alpha=0.8)
        
        # Add contour lines
        contour = ax.contour(xi_grid, yi_grid, zi, levels=10, colors='black', 
                            linewidths=0.5, alpha=0.4)
        ax.clabel(contour, inline=True, fontsize=8, fmt='%.1f s')
        
        # Add scatter points
        scatter = ax.scatter(x, y, c=z, cmap='viridis', s=30, alpha=0.6, 
                           edgecolors='black', linewidths=0.5)
        
        ax.set_xlabel('Average Formula Length', fontsize=11)
        ax.set_ylabel('Average Atomic Complexity', fontsize=11)
        ax.set_title('Refinement Time vs Formula Complexity (Contour)', fontsize=12)
        ax.grid(True, alpha=0.3)
        
        # Add colorbar
        cbar = fig.colorbar(contourf, ax=ax, label='Refinement Time (s)')
        
        fig.tight_layout()
        save_fig_helper('complexity_vs_time_contour', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-time contour plot: {e}")
        import traceback
        traceback.print_exc()


def create_complexity_memory_contour(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create contour plot showing relationship between formula length, atomic complexity, and memory.
    X-axis: Formula Length, Y-axis: Atomic Complexity, Colors: Memory levels.
    """
    try:
        # Check if complexity and memory columns exist
        if 'AvgSize' not in df.columns or 'AvgAtomicComplexity' not in df.columns:
            print("Skipping complexity-memory contour: Formula info not available")
            return
        if ' Refinement_Memory_kB' not in df.columns:
            print("Skipping complexity-memory contour: Memory data not available")
            return
        
        # Filter valid data
        valid_df = df[
            (df[' Refinement_Memory_kB'] > 0) & 
            (df['AvgSize'] > 0) & 
            (df['AvgAtomicComplexity'] > 0)
        ].copy()
        
        if len(valid_df) < 20:
            print(f"Not enough valid data for complexity-memory contour plot: {len(valid_df)} points")
            return
        
        # Convert memory to MB
        valid_df['Refinement_Memory_MB'] = valid_df[' Refinement_Memory_kB'] / 1024
        
        # Create grid for interpolation
        from scipy.interpolate import griddata
        
        x = valid_df['AvgSize'].values
        y = valid_df['AvgAtomicComplexity'].values
        z = valid_df['Refinement_Memory_MB'].values
        
        # Create regular grid
        xi = np.linspace(x.min(), x.max(), 100)
        yi = np.linspace(y.min(), y.max(), 100)
        xi_grid, yi_grid = np.meshgrid(xi, yi)
        
        # Interpolate Z values on the grid
        zi = griddata((x, y), z, (xi_grid, yi_grid), method='cubic', fill_value=np.nan)
        
        # Create contour plot
        fig, ax = plt.subplots(figsize=(12, 9))
        
        # Filled contour plot
        contourf = ax.contourf(xi_grid, yi_grid, zi, levels=20, cmap='plasma', alpha=0.8)
        
        # Add contour lines
        contour = ax.contour(xi_grid, yi_grid, zi, levels=10, colors='black', 
                            linewidths=0.5, alpha=0.4)
        ax.clabel(contour, inline=True, fontsize=8, fmt='%.1f MB')
        
        # Add scatter points
        scatter = ax.scatter(x, y, c=z, cmap='plasma', s=30, alpha=0.6, 
                           edgecolors='black', linewidths=0.5)
        
        ax.set_xlabel('Average Formula Length', fontsize=11)
        ax.set_ylabel('Average Atomic Complexity', fontsize=11)
        ax.set_title('Refinement Memory vs Formula Complexity (Contour)', fontsize=12)
        ax.grid(True, alpha=0.3)
        
        # Add colorbar
        cbar = fig.colorbar(contourf, ax=ax, label='Refinement Memory (MB)')
        
        fig.tight_layout()
        save_fig_helper('complexity_vs_memory_contour', output_folder)
        
    except Exception as e:
        print(f"Error creating complexity-memory contour plot: {e}")
        import traceback
        traceback.print_exc()



def create_average_memory_plot_by_category(df: pd.DataFrame, output_folder: str) -> None:
    """
    Create a bar plot with two y-axes: memory (MB) on the left, time (s) on the right.
    Both share the same scale so bar heights are directly comparable.
    """
    try:
        # Define categories
        categories = {
            'Average': df,
            '0%': df[df['Reduction_Percentage'] == 0],
            '0-25%': df[(df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] < 25)],
            '25-50%': df[(df['Reduction_Percentage'] >= 25) & (df['Reduction_Percentage'] <= 50)],
            '>50%': df[df['Reduction_Percentage'] > 50]
        }

        # Compute averages
        category_data = {}
        for cat_name, cat_data in categories.items():
            if len(cat_data) > 0:
                category_data[cat_name] = {
                    'memory': cat_data[' Refinement_Memory_kB'].mean() / 1024,  # MB
                    'time': cat_data['Total_Time_ms'].mean() / 1000,             # seconds
                    'count': len(cat_data)
                }

        categories_list = list(category_data.keys())
        x_pos = np.arange(len(categories_list))

        memories = [category_data[cat]['memory'] for cat in categories_list]
        times = [category_data[cat]['time'] for cat in categories_list]

        # Build the figure and axes
        fig, ax1 = plt.subplots(figsize=(3.4, 1.8))
        ax2 = ax1.twinx()

        bar_width = 0.35

        # To make bars visually comparable, we use the same height scale:
        # Both plotted as-is (not normalized). Then we align ax2’s tick labels via transformation.
        max_mem = max(memories)
        max_time = max(times)

        # Compute linear transform parameters between memory and time
        scale = max_mem / max_time if max_time != 0 else 1

        # Plot bars
        bars_mem = ax1.bar(x_pos - bar_width/2, memories, bar_width,
                           color='gray', hatch='///', label='Memory (MB)', alpha=0.7)
        bars_time = ax1.bar(x_pos + bar_width/2, [t * scale for t in times], bar_width,
                            color='black', label='Time (s)', alpha=0.6)

        # Axis setup (left)
        ax1.set_xlabel('Property Reduction Percentage', fontsize=8, labelpad=1)
        ax1.set_ylabel('Memory (MB)', fontsize=8, labelpad=2)
        ax1.set_xticks(x_pos)
        ax1.set_xticklabels(categories_list, fontsize=8)
        ax1.tick_params(axis='x', which='major', pad=1)
        ax1.tick_params(axis='y', which='major', pad=0)
        ax1.grid(True, alpha=0.3, axis='y')

        # Axis setup (right): same y-limits, but rescaled tick labels
        ax1_ylim = ax1.get_ylim()
        ax2.set_ylim(ax1_ylim[0] / scale, ax1_ylim[1] / scale)
        ax2.set_ylabel('Time (s)', fontsize=8, labelpad=2)
        ax2.tick_params(axis='y', which='major', pad=0)

        # Combine legends
        handles1, labels1 = ax1.get_legend_handles_labels()
        ax1.legend(handles1, labels1, fontsize=7, loc='upper left')

        plt.tight_layout()
        save_fig_helper('average_memory_and_time_dualaxis', output_folder)

    except Exception as e:
        print(f"Error creating dual-axis memory/time plot: {e}")
        import traceback
        traceback.print_exc()
        return


function_list = [
    create_reduction_distribution_plot,
    create_properties_vs_size_plot,
    create_cumulative_reduction_plot,
    create_category_reduction_histogram,
    create_averagetime_breakdown_per_category,
    create_complexity_time_plot,
    create_complexity_memory_plot,
    #create_complexity_time_hexbin,
    #create_complexity_memory_hexbin,
    #create_complexity_time_contour,
    #create_complexity_memory_contour,
    create_average_memory_plot_by_category
]

def create_single_analysis(df, output_folder):
    "Create all plots for a single analysis. MAKE SURE THE OUTPUT FOLDER EXISTS"
    # Create all plots
    for func in function_list:
        print(f"Creating plot: {func.__name__}")
        func(df, output_folder)
    
    