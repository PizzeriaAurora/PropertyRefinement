
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

FIG_SIZE = (3.7, 2)


# Suppress noisy numpy warnings (polyfit RankWarning message, and invalid value RuntimeWarning)
with warnings.catch_warnings():
    # numpy does not always expose a RankWarning symbol; filter by message instead
    warnings.filterwarnings('ignore', message='Polyfit may be poorly conditioned')
    warnings.simplefilter('ignore', RuntimeWarning)
markers = ['o', 's', '^', 'D', 'v', 'x']
cmap = plt.get_cmap('tab20')
colors = [cmap(i) for i in range(cmap.N)]

def _create_correlation_plot_per_year(df_year_stats: pd.DataFrame, metric_column: str, 
                                      metric_label: str, output_folder: str, 
                                      plot_name: str) -> None:
    """
    Internal function to create correlation plot between formula size and a metric per year.
    
    Args:
        df_year_stats: DataFrame with columns ['Year', 'AvgSize', metric_column]
        metric_column: Name of the column containing the metric to correlate
        metric_label: Label for the y-axis
        output_folder: Output directory for the plot
        plot_name: Name of the plot file (without extension)
    """
    plt.figure(figsize=FIG_SIZE)
    
    # Create scatter plot
    plt.scatter(df_year_stats['AvgSize'], df_year_stats[metric_column], 
               marker='o', s=150, alpha=0.7, color='darkgray', edgecolor='black', linewidth=1.5)
    
    # Annotate each point with the year
    for _, row in df_year_stats.iterrows():
        plt.annotate(str(row['Year']), 
                    (row['AvgSize'], row[metric_column]),
                    textcoords="offset points", xytext=(0,10), 
                    ha='center', fontsize=9)
    
    # Add trend line if we have enough points
    if len(df_year_stats) > 1:
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df_year_stats['AvgSize'], df_year_stats[metric_column], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df_year_stats['AvgSize'].min(), 
                                 df_year_stats['AvgSize'].max(), 100)
            plt.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.2f})')
    
    # Add correlation coefficient
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr = df_year_stats['AvgSize'].corr(df_year_stats[metric_column])
    
    plt.xlabel('Average Property Size per File', fontsize=10)
    plt.ylabel(metric_label, fontsize=10)
    plt.grid(True, alpha=0.3)
    plt.legend(fontsize=9)
    
    # Add correlation text
    #plt.text(0.05, 0.95, f'Correlation: {corr:.3f}', 
    #        transform=plt.gca().transAxes, fontsize=10, 
    #        verticalalignment='top',
    #        bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    print(f'Correlation (Avg Size vs {metric_label}): {corr:.3f}')
    plt.tight_layout()
    save_fig_helper(plot_name, output_folder)


def _create_correlation_plot_per_file(df_files: pd.DataFrame, metric_column: str,
                                      metric_label: str, output_folder: str,
                                      plot_name: str, log_scale: bool = False) -> None:
    """
    Internal function to create correlation plot between formula size and a metric per file.
    
    Args:
        df_files: DataFrame with columns ['AvgSize', metric_column, 'Year'] (optional)
        metric_column: Name of the column containing the metric to correlate
        metric_label: Label for the y-axis
        output_folder: Output directory for the plot
        plot_name: Name of the plot file (without extension)
        log_scale: Whether to use log scale for y-axis
    """
    plt.figure(figsize=FIG_SIZE)
    
    # If we have year information, color by year
    if 'Year' in df_files.columns:
        years = df_files['Year'].unique()
        for i, year in enumerate(sorted(years)):
            year_data = df_files[df_files['Year'] == year]
            plt.scatter(year_data['AvgSize'], year_data[metric_column],
                       marker=markers[i % len(markers)],
                       color=colors[i % len(colors)],
                       s=15, alpha=0.6, label=f'{year}')
    else:
        plt.scatter(df_files['AvgSize'], df_files[metric_column],
                   marker='o', s=15, alpha=0.6, color='gray')
    
    # Add trend line
    valid_mask = (df_files['AvgSize'] > 0) & (df_files[metric_column] >= 0)
    if valid_mask.sum() > 1:
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df_files['AvgSize'][valid_mask], 
                          df_files[metric_column][valid_mask], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df_files['AvgSize'].min(), 
                                 df_files['AvgSize'].max(), 100)
            plt.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.3f})')
    
    # Add correlation coefficient
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr = df_files['AvgSize'].corr(df_files[metric_column])

    plt.xlabel('Average Property Size per File', fontsize=10)
    plt.ylabel(metric_label, fontsize=10)
    
    if log_scale:
        plt.yscale('log')
    
    plt.grid(True, alpha=0.3)
    
    if 'Year' in df_files.columns:
        plt.legend(bbox_to_anchor=(1.05, 1), loc='upper right', fontsize=8)
    # else:
    #     #plt.legend(fontsize=9,loc='upper right')
    #     continue

    # Add correlation text
    plt.text(0.05, 0.95, f'Correlation: {corr:.3f}       Slope : {z[0]:.3f}', 
            transform=plt.gca().transAxes, fontsize=10, 
            verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    print(f'Correlation (Atomic Complexity vs {metric_label}): {corr:.3f}')
    plt.tight_layout()
    save_fig_helper(plot_name, output_folder)


def create_year_time_correlation_plots(df: pd.DataFrame, formula_info_folder: str, 
                                       output_folder: str) -> None:
    """
    Create correlation plots between average formula size and processing time per year.
    
    Args:
        df: Combined results DataFrame with Year and timing information
        formula_info_folder: Path to folder containing overall_info.csv
        output_folder: Output directory for plots
    """
    # Load formula size information per year
    overall_info_path = os.path.join(formula_info_folder, 'overall_info.csv')
    if not os.path.exists(overall_info_path):
        print(f"Warning: {overall_info_path} not found. Skipping year correlation plots.")
        return
    
    df_formula_info = pd.read_csv(overall_info_path)
    df_formula_info.columns = df_formula_info.columns.str.strip()
    
    # Calculate average time per year
    df_year_time = df.groupby('Year').agg({
        'Total_Time_ms': 'mean',
        'Refinement_Time_ms': 'mean',
        ' Refinement_Memory_kB': 'mean'
    }).reset_index()
    
    # Convert time to seconds and memory to MB
    df_year_time['Total_Time_s'] = df_year_time['Total_Time_ms'] / 1000
    df_year_time['Refinement_Time_s'] = df_year_time['Refinement_Time_ms'] / 1000
    df_year_time['Refinement_Memory_MB'] = df_year_time[' Refinement_Memory_kB'] / 1024
    
    # Extract year from folder name (e.g., "MCC2018" -> 2018)
    df_year_time['Year'] = df_year_time['Year'].astype(str)
    df_formula_info['Folder'] = df_formula_info['Folder'].astype(str)
    
    # Merge with formula size information
    df_merged = pd.merge(df_year_time, df_formula_info, 
                        left_on='Year', right_on='Folder', how='inner')
    
    # Create plot for total time
    _create_correlation_plot_per_year(
        df_merged, 'Total_Time_s', 
        'Average Total Time (s)', 
        output_folder, 
        'correlation_year_formula_size_vs_total_time'
    )
    
    # Create plot for refinement time
    _create_correlation_plot_per_year(
        df_merged, 'Refinement_Time_s',
        'Average Refinement Time (s)',
        output_folder,
        'correlation_year_formula_size_vs_refinement_time'
    )
    
    # Create plot for memory
    _create_correlation_plot_per_year(
        df_merged, 'Refinement_Memory_MB',
        'Average Memory (MB)',
        output_folder,
        'correlation_year_formula_size_vs_memory'
    )


def create_year_refinement_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                            output_folder: str) -> None:
    """
    Create correlation plots between average formula size and refinement metrics per year.
    
    Args:
        df: Combined results DataFrame with Year and refinement information
        formula_info_folder: Path to folder containing overall_info.csv
        output_folder: Output directory for plots
    """
    # Load formula size information per year
    overall_info_path = os.path.join(formula_info_folder, 'overall_info.csv')
    if not os.path.exists(overall_info_path):
        print(f"Warning: {overall_info_path} not found. Skipping year correlation plots.")
        return
    
    df_formula_info = pd.read_csv(overall_info_path)
    df_formula_info.columns = df_formula_info.columns.str.strip()
    
    # Calculate average refinements per year
    df_year_refinements = df.groupby('Year').agg({
        'Total_Refinements': 'mean',
        'Equivalence_Classes': 'mean'
    }).reset_index()
    
    # Extract year from folder name
    df_year_refinements['Year'] = df_year_refinements['Year'].str.extract(r'(\d{4})').astype(str)
    df_formula_info['Folder'] = df_formula_info['Folder'].astype(str)
    
    # Merge with formula size information
    df_merged = pd.merge(df_year_refinements, df_formula_info,
                        left_on='Year', right_on='Folder', how='inner')
    
    # Create plot for total refinements
    _create_correlation_plot_per_year(
        df_merged, 'Total_Refinements',
        'Average Total Refinements',
        output_folder,
        'correlation_year_formula_size_vs_total_refinements'
    )
    
    # Create plot for equivalence classes
    _create_correlation_plot_per_year(
        df_merged, 'Equivalence_Classes',
        'Average Equivalence Classes',
        output_folder,
        'correlation_year_formula_size_vs_equivalence_classes'
    )


def create_year_property_reduction_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                                     output_folder: str) -> None:
    """
    Create correlation plots between average formula size and property reduction metrics per year.
    
    Args:
        df: Combined results DataFrame with Year and property reduction information
        formula_info_folder: Path to folder containing overall_info.csv
        output_folder: Output directory for plots
    """
    # Load formula size information per year
    overall_info_path = os.path.join(formula_info_folder, 'overall_info.csv')
    if not os.path.exists(overall_info_path):
        print(f"Warning: {overall_info_path} not found. Skipping year correlation plots.")
        return
    
    df_formula_info = pd.read_csv(overall_info_path)
    df_formula_info.columns = df_formula_info.columns.str.strip()
    
    # Calculate average property reduction per year
    df_year_reduction = df.groupby('Year').agg({
        'Properties_Eliminated': 'mean',
        'Reduction_Percentage': 'mean'
    }).reset_index()
    
    # Extract year from folder name
    df_year_reduction['Year'] = df_year_reduction['Year'].str.extract(r'(\d{4})').astype(str)
    df_formula_info['Folder'] = df_formula_info['Folder'].astype(str)
    
    # Merge with formula size information
    df_merged = pd.merge(df_year_reduction, df_formula_info,
                        left_on='Year', right_on='Folder', how='inner')
    
    # Create plot for properties eliminated
    _create_correlation_plot_per_year(
        df_merged, 'Properties_Eliminated',
        'Average Properties Eliminated',
        output_folder,
        'correlation_year_formula_size_vs_properties_eliminated'
    )
    
    # Create plot for PRP
    _create_correlation_plot_per_year(
        df_merged, 'Reduction_Percentage',
        'Average PRP (%)',
        output_folder,
        'correlation_year_formula_size_vs_reduction_percentage'
    )


def create_file_time_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                      output_folder: str) -> None:
    """
    Create correlation plots between formula size and processing time per file.
    
    Args:
        df: Combined results DataFrame with file-level timing information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping file correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    


    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Convert time to seconds and memory to MB
    df_merged['Total_Time_s'] = df_merged['Total_Time_ms'] / 1000
    df_merged['Refinement_Time_s'] = df_merged['Refinement_Time_ms'] / 1000
    df_merged['Refinement_Memory_MB'] = df_merged[' Refinement_Memory_kB'] / 1024
    
    # Create plot for total time
    _create_correlation_plot_per_file(
        df_merged, 'Total_Time_s',
        'Total Time (s)',
        output_folder,
        'correlation_file_formula_size_vs_total_time',
        log_scale=True
    )
    
    # Create plot for refinement time
    _create_correlation_plot_per_file(
        df_merged, 'Refinement_Time_s',
        'Refinement Time (s)',
        output_folder,
        'correlation_file_formula_size_vs_refinement_time',
        log_scale=True
    )
    
    # Create plot for memory
    _create_correlation_plot_per_file(
        df_merged, 'Refinement_Memory_MB',
        'Memory (MB)',
        output_folder,
        'correlation_file_formula_size_vs_memory',
        log_scale=True
    )


def create_file_refinement_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                            output_folder: str) -> None:
    """
    Create correlation plots between formula size and refinement metrics per file.
    
    Args:
        df: Combined results DataFrame with file-level refinement information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping file correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Create plot for total refinements
    _create_correlation_plot_per_file(
        df_merged, 'Total_Refinements',
        'Total Refinements',
        output_folder,
        'correlation_file_formula_size_vs_total_refinements'
    )
    
    # Create plot for equivalence classes
    _create_correlation_plot_per_file(
        df_merged, 'Equivalence_Classes',
        'Equivalence Classes',
        output_folder,
        'correlation_file_formula_size_vs_equivalence_classes'
    )


def create_file_property_reduction_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                                    output_folder: str) -> None:
    """
    Create correlation plots between formula size and property reduction metrics per file.
    
    Args:
        df: Combined results DataFrame with file-level property reduction information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping file correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Create plot for properties eliminated
    _create_correlation_plot_per_file(
        df_merged, 'Properties_Eliminated',
        'Properties Eliminated',
        output_folder,
        'correlation_file_formula_size_vs_properties_eliminated'
    )
    
    # Create plot for PRP
    _create_correlation_plot_per_file(
        df_merged, 'Reduction_Percentage',
        'PRP (%)',
        output_folder,
        'correlation_file_formula_size_vs_reduction_percentage'
    )


def _create_atomic_correlation_plot_per_file(df_files: pd.DataFrame, metric_column: str,
                                             metric_label: str, output_folder: str,
                                             plot_name: str, log_scale: bool = False) -> None:
    """
    Internal function to create correlation plot between atomic complexity and a metric per file.
    
    Args:
        df_files: DataFrame with columns ['AvgAtomicComplexity', metric_column, 'Year'] (optional)
        metric_column: Name of the column containing the metric to correlate
        metric_label: Label for the y-axis
        output_folder: Output directory for the plot
        plot_name: Name of the plot file (without extension)
        log_scale: Whether to use log scale for y-axis
    """
    plt.figure(figsize=FIG_SIZE)
    
    # If we have year information, color by year
    if 'Year' in df_files.columns:
        years = df_files['Year'].unique()
        for i, year in enumerate(sorted(years)):
            year_data = df_files[df_files['Year'] == year]
            plt.scatter(year_data['AvgAtomicComplexity'], year_data[metric_column],
                       marker=markers[i % len(markers)],
                       color=colors[i % len(colors)],
                       s=15, alpha=0.6, label=f'{year}')
    else:
        plt.scatter(df_files['AvgAtomicComplexity'], df_files[metric_column],
                   marker='o', s=15, alpha=0.6, color='gray')
    
    # Add trend line
    valid_mask = (df_files['AvgAtomicComplexity'] > 0) & (df_files[metric_column] >= 0)
    if valid_mask.sum() > 1:
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df_files['AvgAtomicComplexity'][valid_mask], 
                          df_files[metric_column][valid_mask], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df_files['AvgAtomicComplexity'].min(), 
                                 df_files['AvgAtomicComplexity'].max(), 100)
            plt.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.3f})')
    
    # Add correlation coefficient
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr = df_files['AvgAtomicComplexity'].corr(df_files[metric_column])
    
    plt.xlabel('Average Atomic Complexity per File', fontsize=10)
    plt.ylabel(metric_label, fontsize=10)
    
    if log_scale:
        plt.yscale('log')
    
    plt.grid(True, alpha=0.3)
    
    if 'Year' in df_files.columns:
        plt.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=8)
    #else:
    #    plt.legend(fontsize=9, loc='upper right')
    
    # Add correlation text
    plt.text(0.05, 0.95, f'Correlation: {corr:.3f}       Slope : {z[0]:.3f}', 
            verticalalignment='top',
            transform=plt.gca().transAxes, fontsize=10, 
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    print(f'Correlation (Atomic Complexity vs {metric_label}): {corr:.3f}')
    plt.tight_layout()
    save_fig_helper(plot_name, output_folder)


def create_file_atomic_time_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                              output_folder: str) -> None:
    """
    Create correlation plots between atomic complexity and processing time per file.
    
    Args:
        df: Combined results DataFrame with file-level timing information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping atomic complexity correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Convert time to seconds and memory to MB
    df_merged['Total_Time_s'] = df_merged['Total_Time_ms'] / 1000
    df_merged['Refinement_Time_s'] = df_merged['Refinement_Time_ms'] / 1000
    df_merged['Refinement_Memory_MB'] = df_merged[' Refinement_Memory_kB'] / 1024
    
    # Create plot for total time
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Total_Time_s',
        'Total Time (s)',
        output_folder,
        'correlation_file_atomic_complexity_vs_total_time',
        log_scale=True
    )
    
    # Create plot for refinement time
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Refinement_Time_s',
        'Refinement Time (s)',
        output_folder,
        'correlation_file_atomic_complexity_vs_refinement_time',
        log_scale=True
    )
    
    # Create plot for memory
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Refinement_Memory_MB',
        'Memory (MB)',
        output_folder,
        'correlation_file_atomic_complexity_vs_memory',
        log_scale=True
    )


def create_file_atomic_refinement_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                                    output_folder: str) -> None:
    """
    Create correlation plots between atomic complexity and refinement metrics per file.
    
    Args:
        df: Combined results DataFrame with file-level refinement information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping atomic complexity correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Create plot for total refinements
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Total_Refinements',
        'Total Refinements',
        output_folder,
        'correlation_file_atomic_complexity_vs_total_refinements'
    )
    
    # Create plot for equivalence classes
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Equivalence_Classes',
        'Equivalence Classes',
        output_folder,
        'correlation_file_atomic_complexity_vs_equivalence_classes'
    )


def create_file_atomic_property_reduction_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                                            output_folder: str) -> None:
    """
    Create correlation plots between atomic complexity and property reduction metrics per file.
    
    Args:
        df: Combined results DataFrame with file-level property reduction information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping atomic complexity correlation plots.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')
    
    # Create plot for properties eliminated
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Properties_Eliminated',
        'Properties Eliminated',
        output_folder,
        'correlation_file_atomic_complexity_vs_properties_eliminated'
    )
    
    # Create plot for PRP
    _create_atomic_correlation_plot_per_file(
        df_merged, 'Reduction_Percentage',
        'PRP (%)',
        output_folder,
        'correlation_file_atomic_complexity_vs_reduction_percentage'
    )


def create_file_dualaxis_atomic_complexity_time_memory(df: pd.DataFrame, formula_info_folder: str,
                                                       output_folder: str) -> None:
    """
    Create a per-file dual-axis time-series-like plot showing memory (left) and time (right)
    against average atomic complexity. No scatter points; plot smoothed central trajectory
    (rolling mean) with a shaded confidence band (mean +/- std) computed from nearby points.

    Args:
        df: Combined results DataFrame with file-level timing information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []

    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)

    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)

    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping dual-axis atomic complexity plot.")
        return

    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)

    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')

    # Convert units
    df_merged['Total_Time_s'] = df_merged['Total_Time_ms'] / 1000
    df_merged['Refinement_Memory_MB'] = df_merged[' Refinement_Memory_kB'] / 1024

    # Prepare x and y
    df_plot = df_merged[['AvgAtomicComplexity', 'Total_Time_s', 'Refinement_Memory_MB']].dropna()
    if df_plot.empty:
        print('No data available for dual-axis atomic complexity plot.')
        return

    df_plot = df_plot.sort_values('AvgAtomicComplexity')
    x = df_plot['AvgAtomicComplexity'].values
    time_y = df_plot['Total_Time_s'].values
    mem_y = df_plot['Refinement_Memory_MB'].values

    n = len(df_plot)
    window = max(3, int(max(3, n * 0.2)))

    # Compute rolling mean and std on the ordered series
    s_time = pd.Series(time_y)
    s_mem = pd.Series(mem_y)
    time_mean = s_time.rolling(window, center=True, min_periods=1).mean().values
    time_std = s_time.rolling(window, center=True, min_periods=1).std().fillna(0).values
    mem_mean = s_mem.rolling(window, center=True, min_periods=1).mean().values
    mem_std = s_mem.rolling(window, center=True, min_periods=1).std().fillna(0).values

    fig, ax1 = plt.subplots(figsize=FIG_SIZE)
    ax2 = ax1.twinx()

    # Plot central trajectories
    l1, = ax1.plot(x, mem_mean, color='gray', linewidth=2, label='Memory (MB)')
    l2, = ax2.plot(x, time_mean, color='black', linewidth=2, linestyle='--', marker='x',
                   markersize=6, markeredgewidth=1.5, label='Time (s)')

    # Shaded confidence bands (mean +/- std)
    ax1.fill_between(x, mem_mean - mem_std, mem_mean + mem_std, color='gray', alpha=0.2)
    ax2.fill_between(x, time_mean - time_std, time_mean + time_std, color='black', alpha=0.08)

    ax1.set_xlabel('Average Atomic Complexity per File', fontsize=10)
    ax1.set_ylabel('Memory (MB)', fontsize=10, color='gray')
    ax1.tick_params(axis='y', labelcolor='gray')
    ax1.grid(True, alpha=0.3)

    ax2.set_ylabel('Time (s)', fontsize=10, color='black')
    ax2.tick_params(axis='y', labelcolor='black')

    # Legend
    ax1.legend([l1, l2], [l1.get_label(), l2.get_label()], fontsize=9, loc='upper left')

    plt.tight_layout()
    save_fig_helper('correlation_file_atomic_complexity_memory_time_dualaxis', output_folder)
    print('Created per-file dual-axis plot: Atomic Complexity vs Memory/Time')


def create_file_dualaxis_formula_size_time_memory(df: pd.DataFrame, formula_info_folder: str,
                                                  output_folder: str) -> None:
    """
    Create a per-file dual-axis time-series-like plot showing memory (left) and time (right)
    against average formula size. No scatter points; plot smoothed central trajectory
    (rolling mean) with a shaded confidence band (mean +/- std) computed from nearby points.
    """
    # Collect all file-level formula information
    all_files_data = []

    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)

    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)

    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping dual-axis formula size plot.")
        return

    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)

    # Merge with results data
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner')

    # Convert units
    df_merged['Total_Time_s'] = df_merged['Total_Time_ms'] / 1000
    df_merged['Refinement_Memory_MB'] = df_merged[' Refinement_Memory_kB'] / 1024

    # Prepare x and y
    df_plot = df_merged[['AvgSize', 'Total_Time_s', 'Refinement_Memory_MB']].dropna()
    if df_plot.empty:
        print('No data available for dual-axis formula size plot.')
        return

    df_plot = df_plot.sort_values('AvgSize')
    x = df_plot['AvgSize'].values
    time_y = df_plot['Total_Time_s'].values
    mem_y = df_plot['Refinement_Memory_MB'].values

    n = len(df_plot)
    window = max(3, int(max(3, n * 0.2)))

    s_time = pd.Series(time_y)
    s_mem = pd.Series(mem_y)
    time_mean = s_time.rolling(window, center=True, min_periods=1).mean().values
    time_std = s_time.rolling(window, center=True, min_periods=1).std().fillna(0).values
    mem_mean = s_mem.rolling(window, center=True, min_periods=1).mean().values
    mem_std = s_mem.rolling(window, center=True, min_periods=1).std().fillna(0).values

    fig, ax1 = plt.subplots(figsize=FIG_SIZE)
    ax2 = ax1.twinx()

    l1, = ax1.plot(x, mem_mean, color='gray', linewidth=2, label='Memory (MB)')
    l2, = ax2.plot(x, time_mean, color='black', linewidth=2, linestyle='--', marker='x',
                   markersize=6, markeredgewidth=1.5, label='Time (s)')

    ax1.fill_between(x, mem_mean - mem_std, mem_mean + mem_std, color='gray', alpha=0.2)
    ax2.fill_between(x, time_mean - time_std, time_mean + time_std, color='black', alpha=0.08)

    ax1.set_xlabel('Average Formula Size per File', fontsize=10)
    ax1.set_ylabel('Memory (MB)', fontsize=10, color='gray')
    ax1.tick_params(axis='y', labelcolor='gray')
    ax1.grid(True, alpha=0.3)

    ax2.set_ylabel('Time (s)', fontsize=10, color='black')
    ax2.tick_params(axis='y', labelcolor='black')

    ax1.legend([l1, l2], [l1.get_label(), l2.get_label()], fontsize=9, loc='upper left')

    plt.tight_layout()
    save_fig_helper('correlation_file_formula_size_memory_time_dualaxis', output_folder)
    print('Created per-file dual-axis plot: Formula Size vs Memory/Time')


def create_all_correlation_plots(df: pd.DataFrame, formula_info_folder: str,
                                output_folder: str) -> None:
    """
    Wrapper function to create all correlation plots (year-based and file-based).
    
    Args:
        df: Combined results DataFrame
        formula_info_folder: Path to folder containing formula size information
        output_folder: Output directory for plots
    """
    print("Creating year-based correlation plots...")
    #remove "/" from output folder name
    if(output_folder.endswith("/")):
        output_folder = output_folder[:-1]
    output_folder = output_folder + "/FormulaSizeCorrelationPlots"
    os.makedirs(output_folder, exist_ok=True)
    # Year-based plots
    print("  - Time correlation plots")
    create_year_time_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Refinement correlation plots")
    create_year_refinement_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Property reduction correlation plots")
    create_year_property_reduction_correlation_plots(df, formula_info_folder, output_folder)
    
    print("\nCreating file-based correlation plots...")
    
    # File-based plots (formula size)
    print("  - Time correlation plots")
    create_file_time_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Refinement correlation plots")
    create_file_refinement_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Property reduction correlation plots")
    create_file_property_reduction_correlation_plots(df, formula_info_folder, output_folder)
    
    # File-based plots (atomic complexity)
    print("  - Atomic complexity vs time correlation plots")
    create_file_atomic_time_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Atomic complexity vs refinement correlation plots")
    create_file_atomic_refinement_correlation_plots(df, formula_info_folder, output_folder)
    
    print("  - Atomic complexity vs property reduction correlation plots")
    create_file_atomic_property_reduction_correlation_plots(df, formula_info_folder, output_folder)
    
    # Dual-axis plots
    print("  - Dual-axis: Atomic Complexity vs Memory/Time (per file)")
    create_file_dualaxis_atomic_complexity_time_memory(df, formula_info_folder, output_folder)
    
    print("  - Dual-axis: Formula Size vs Memory/Time (per file)")
    create_file_dualaxis_formula_size_time_memory(df, formula_info_folder, output_folder)
    
    # Combined PRP comparison plot
    print("  - Combined PRP vs complexity metrics")
    create_prp_complexity_comparison_plot(df, formula_info_folder, output_folder)


def create_prp_complexity_comparison_plot(df: pd.DataFrame, formula_info_folder: str,
                                         output_folder: str) -> None:
    """
    Create a combined plot with 2 subplots comparing PRP (Average reduction %) 
    against formula size (top) and atomic complexity (bottom).
    
    Args:
        df: Combined results DataFrame with file-level property reduction information
        formula_info_folder: Path to folder containing info_per_file_{year}.csv files
        output_folder: Output directory for plots
    """
    # Collect all file-level formula information
    all_files_data = []
    
    # Extract file name without extension and year
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)
    
    for year in df['Year_Num'].unique():
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year}.csv')
        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info['Year'] = year
            all_files_data.append(df_info)
    
    if not all_files_data:
        print("Warning: No per-file formula info found. Skipping PRP comparison plot.")
        return
    
    df_all_formula_info = pd.concat(all_files_data, ignore_index=True)
    
    # Merge with results data (use suffixes to avoid column conflicts)
    df_merged = pd.merge(df, df_all_formula_info,
                        left_on=['FileName', 'Year_Num'],
                        right_on=['File', 'Year'],
                        how='inner',
                        suffixes=('', '_formula'))
    
    # Create figure with 2 subplots (vertical layout)
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 12))
    
    # Get years for coloring (use Year_Num which is guaranteed to exist from df)
    years = sorted(df_merged['Year_Num'].unique())
    
    # Top subplot: PRP vs Formula Size
    for i, year in enumerate(years):
        year_data = df_merged[df_merged['Year_Num'] == year]
        ax1.scatter(year_data['AvgSize'], year_data['Reduction_Percentage'],
                   marker=markers[i % len(markers)],
                   color=colors[i % len(colors)],
                   s=15, alpha=0.6, label=f'{year}')
    
    # Add trend line for formula size
    valid_mask = (df_merged['AvgSize'] > 0) & (df_merged['Reduction_Percentage'] >= 0)
    if valid_mask.sum() > 1:
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df_merged['AvgSize'][valid_mask], 
                          df_merged['Reduction_Percentage'][valid_mask], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df_merged['AvgSize'].min(), 
                                 df_merged['AvgSize'].max(), 100)
            ax1.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.3f})')
    
    # Add correlation coefficient for formula size
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr1 = df_merged['AvgSize'].corr(df_merged['Reduction_Percentage'])
    
    ax1.set_xlabel('Average Formula Size', fontsize=11)
    ax1.set_ylabel('PRP - Average Reduction (%)', fontsize=11)
    ax1.set_title('PRP vs Formula Size', fontsize=12, fontweight='bold')
    ax1.grid(True, alpha=0.3)
    ax1.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=8)
    
    # Add correlation text
    ax1.text(0.05, 0.95, f'Correlation: {corr1:.3f}', 
            transform=ax1.transAxes, fontsize=10, 
            verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    
    # Bottom subplot: PRP vs Atomic Complexity
    for i, year in enumerate(years):
        year_data = df_merged[df_merged['Year_Num'] == year]
        ax2.scatter(year_data['AvgAtomicComplexity'], year_data['Reduction_Percentage'],
                   marker=markers[i % len(markers)],
                   color=colors[i % len(colors)],
                   s=15, alpha=0.6, label=f'{year}')
    
    # Add trend line for atomic complexity
    valid_mask = (df_merged['AvgAtomicComplexity'] > 0) & (df_merged['Reduction_Percentage'] >= 0)
    if valid_mask.sum() > 1:
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', RuntimeWarning)
            z = np.polyfit(df_merged['AvgAtomicComplexity'][valid_mask], 
                          df_merged['Reduction_Percentage'][valid_mask], 1)
            p = np.poly1d(z)
            x_trend = np.linspace(df_merged['AvgAtomicComplexity'].min(), 
                                 df_merged['AvgAtomicComplexity'].max(), 100)
            ax2.plot(x_trend, p(x_trend), 'k--', alpha=0.8, linewidth=2, 
                    label=f'Trend (slope: {z[0]:.3f})')
    
    # Add correlation coefficient for atomic complexity
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', RuntimeWarning)
        corr2 = df_merged['AvgAtomicComplexity'].corr(df_merged['Reduction_Percentage'])
    
    ax2.set_xlabel('Average Atomic Complexity per File', fontsize=11)
    ax2.set_ylabel('PRP - Average Reduction (%)', fontsize=11)
    ax2.set_title('PRP vs Atomic Complexity', fontsize=12, fontweight='bold')
    ax2.grid(True, alpha=0.3)
    ax2.legend(bbox_to_anchor=(1.05, 1), loc='upper left', fontsize=8)
    
    # Add correlation text
    ax2.text(0.05, 0.95, f'Correlation: {corr2:.3f}', 
            transform=ax2.transAxes, fontsize=10, 
            verticalalignment='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    
    plt.suptitle('PRP Reduction vs Complexity Metrics', fontsize=14, fontweight='bold', y=0.995)
    plt.tight_layout()
    save_fig_helper('prp_vs_complexity_comparison', output_folder)


def create_file_dualaxis_atomic_complexity_time_memory(df: pd.DataFrame,
                                                        formula_info_folder: str,
                                                        output_folder: str) -> None:
    import numpy as np
    import pandas as pd
    import matplotlib.pyplot as plt

    # Prepare base data (same as before)
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)

    all_files_data = []
    years = df['Year'].unique()

    for year in years:
        year_num = year.replace('MCC', '').replace('ParallelRers', '').replace('Rers', '').replace('Ind', '').replace('Ctl', '')
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year_num}.csv')

        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info.columns = df_info.columns.str.strip()
            df_info['Year'] = year
            all_files_data.append(df_info)

    if not all_files_data:
        print("Warning: No file-level formula info found. Skipping.")
        return

    df_info = pd.concat(all_files_data, ignore_index=True)
    dfm = pd.merge(df, df_info,
                   left_on=['FileName','Year'],
                   right_on=['File','Year'],
                   how='inner')

    # Convert units
    dfm['Total_Time_s'] = dfm['Total_Time_ms'] / 1000
    dfm['Refinement_Memory_MB'] = dfm[' Refinement_Memory_kB'] / 1024

    # Sort by x variable
    dfm = dfm.sort_values('AvgAtomicComplexity')

    # ---- Create trajectory: bin by x and aggregate ----
    bin_count = 30  # smoothness control
    dfm['bin'] = pd.qcut(dfm['AvgAtomicComplexity'], q=bin_count, duplicates='drop')

    grouped = dfm.groupby('bin').agg(
        x=('AvgAtomicComplexity', 'mean'),
        mem_mean=('Refinement_Memory_MB', 'mean'),
        mem_min=('Refinement_Memory_MB', 'min'),
        mem_max=('Refinement_Memory_MB', 'max'),
        time_mean=('Total_Time_s', 'mean'),
        time_min=('Total_Time_s', 'min'),
        time_max=('Total_Time_s', 'max')
    ).dropna()

    # ---- Plot ----
    fig, ax1 = plt.subplots(figsize=FIG_SIZE)
    ax2 = ax1.twinx()

    # Memory trajectory (left axis)
    ax1.plot(grouped['x'], grouped['mem_mean'], color='gray', linewidth=1.8)
    ax1.fill_between(grouped['x'], grouped['mem_min'], grouped['mem_max'],
                     color='lightgray', alpha=0.4)

    # Time trajectory (right axis)
    ax2.plot(grouped['x'], grouped['time_mean'], color='black', linewidth=1.8)
    ax2.fill_between(grouped['x'], grouped['time_min'], grouped['time_max'],
                     color='lightgray', alpha=0.4)

    ax1.set_xlabel("Average Atomic Complexity per File")
    ax1.set_ylabel("Memory (MB)", color='gray')
    ax2.set_ylabel("Time (s)", color='black')

    ax1.tick_params(axis='y', colors='gray')
    ax2.tick_params(axis='y', colors='black')

    ax1.grid(True, alpha=0.3)

    plt.tight_layout()
    save_fig_helper("trajectory_atomic_complexity_time_memory", output_folder)
    print("Created trajectory + shaded region plot (atomic complexity)")

def create_file_dualaxis_formula_size_time_memory(df: pd.DataFrame,
                                                   formula_info_folder: str,
                                                   output_folder: str) -> None:
    import numpy as np
    import pandas as pd
    import matplotlib.pyplot as plt

    # Prepare data
    df['FileName'] = df['Input'].str.replace('.txt', '')
    df['Year_Num'] = df['Year'].str.extract(r'(\d{4})').astype(int)

    all_files_data = []
    years = df['Year'].unique()

    for year in years:
        year_num = year.replace('MCC', '').replace('ParallelRers', '').replace('Rers', '').replace('Ind', '').replace('Ctl', '')
        info_file = os.path.join(formula_info_folder, f'info_per_file_{year_num}.csv')

        if os.path.exists(info_file):
            df_info = pd.read_csv(info_file)
            df_info.columns = df_info.columns.str.strip()
            df_info['Year'] = year
            all_files_data.append(df_info)

    if not all_files_data:
        print("Warning: No file-level formula info found. Skipping.")
        return

    df_info = pd.concat(all_files_data, ignore_index=True)
    dfm = pd.merge(df, df_info,
                   left_on=['FileName','Year'],
                   right_on=['File','Year'],
                   how='inner')

    dfm['Total_Time_s'] = dfm['Total_Time_ms'] / 1000
    dfm['Refinement_Memory_MB'] = dfm[' Refinement_Memory_kB'] / 1024

    dfm = dfm.sort_values('AvgSize')

    # ---- Create trajectory: bin by size ----
    bin_count = 30
    dfm['bin'] = pd.qcut(dfm['AvgSize'], q=bin_count, duplicates='drop')

    grouped = dfm.groupby('bin').agg(
        x=('AvgSize', 'mean'),
        mem_mean=('Refinement_Memory_MB', 'mean'),
        mem_min=('Refinement_Memory_MB', 'min'),
        mem_max=('Refinement_Memory_MB', 'max'),
        time_mean=('Total_Time_s', 'mean'),
        time_min=('Total_Time_s', 'min'),
        time_max=('Total_Time_s', 'max')
    ).dropna()

    # ---- Plot ----
    fig, ax1 = plt.subplots(figsize=FIG_SIZE)
    ax2 = ax1.twinx()

    # Memory
    ax1.plot(grouped['x'], grouped['mem_mean'], color='gray', linewidth=1.8)
    ax1.fill_between(grouped['x'], grouped['mem_min'], grouped['mem_max'],
                     color='lightgray', alpha=0.4)

    # Time
    ax2.plot(grouped['x'], grouped['time_mean'], color='black', linewidth=1.8)
    ax2.fill_between(grouped['x'], grouped['time_min'], grouped['time_max'],
                     color='lightgray', alpha=0.4)

    ax1.set_xlabel("Average Formula Size per File")
    ax1.set_ylabel("Memory (MB)", color='gray')
    ax2.set_ylabel("Time (s)", color='black')

    ax1.tick_params(axis='y', colors='gray')
    ax2.tick_params(axis='y', colors='black')

    ax1.grid(True, alpha=0.3)

    plt.tight_layout()
    save_fig_helper("trajectory_formula_size_time_memory", output_folder)
    print("Created trajectory + shaded region plot (formula size)")
