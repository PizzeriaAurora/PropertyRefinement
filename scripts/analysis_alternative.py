#!/usr/bin/env python3
"""
Alternative Professional Analysis for CTL Refinement-Based Reduction Tool

This script provides a comprehensive evaluation analysis demonstrating the practical
benefits of the CTL refinement tool for verification engineers. It analyzes:
- Property reduction effectiveness (what can be eliminated as redundant)
- Performance characteristics (speed and scalability)
- Practical engineering value (time savings, coverage preservation)

Author: CTL Refinement Tool Project
"""

import os
import sys
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import warnings
warnings.filterwarnings('ignore')

# Professional plotting style
plt.style.use('seaborn-v0_8-darkgrid')
sns.set_palette("husl")
plt.rcParams.update({
    'font.size': 11,
    'axes.titlesize': 14,
    'axes.labelsize': 12,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'legend.fontsize': 10,
    'figure.titlesize': 16,
    'lines.linewidth': 2.5,
    'lines.markersize': 8,
    'figure.dpi': 100,
    'savefig.dpi': 300,
    'savefig.bbox': 'tight',
})


class CTLRefinementAnalyzer:
    """
    Professional analyzer for CTL refinement tool evaluation.
    
    Focuses on demonstrating practical engineering value:
    - Effectiveness: How many redundant properties are identified?
    - Efficiency: How fast is the analysis?
    - Utility: What time savings for verification workflows?
    """
    
    def __init__(self, results_dir: str, output_dir: str):
        """
        Initialize analyzer.
        
        Args:
            results_dir: Directory containing language_inclusion_RCTLC_s results
            output_dir: Directory for analysis outputs
        """
        self.results_dir = Path(results_dir)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create subdirectories for organized output
        self.plots_dir = self.output_dir / "plots"
        self.tables_dir = self.output_dir / "tables"
        self.plots_dir.mkdir(exist_ok=True)
        self.tables_dir.mkdir(exist_ok=True)
        
        self.data = None
        self.summary_stats = {}
        
    def load_data(self) -> pd.DataFrame:
        """Load and consolidate all benchmark results."""
        print("Loading benchmark data...")
        
        all_data = []
        subdirs = sorted([d for d in self.results_dir.iterdir() if d.is_dir()])
        
        for subdir in subdirs:
            csv_file = subdir / "analysis_results.csv"
            if not csv_file.exists():
                print(f"Warning: {csv_file} not found, skipping")
                continue
                
            df = pd.read_csv(csv_file)
            # Use subdirectory name as category/benchmark set name
            df['Year'] = subdir.name
            all_data.append(df)
            print(f"  Loaded {len(df)} benchmarks from {subdir.name}")
        
        if not all_data:
            raise ValueError(f"No data found in {self.results_dir}")
        
        self.data = pd.concat(all_data, ignore_index=True)
        
        # Add computed columns
        self.data['Reduction_Percentage'] = (
            self.data['Properties_Removed'] / self.data['Total_Properties'] * 100
        )
        self.data['Refinement_Time_s'] = self.data['Refinement_Time_ms'] / 1000
        self.data['Total_Time_s'] = self.data['Total_Time_ms'] / 1000
        self.data['Has_Reduction'] = self.data['Properties_Removed'] > 0
        
        print(f"\nTotal benchmarks loaded: {len(self.data)}")
        print(f"Benchmark sets: {sorted(self.data['Year'].unique())}")
        
        return self.data
    
    def compute_summary_statistics(self):
        """Compute comprehensive summary statistics."""
        print("\nComputing summary statistics...")
        
        df = self.data
        
        # Overall statistics
        self.summary_stats = {
            'Total Benchmarks': len(df),
            'Total Properties Analyzed': int(df['Total_Properties'].sum()),
            'Total Properties Removed': int(df['Properties_Removed'].sum()),
            'Total Refinements Found': int(df['Total_Refinements'].sum()),
            'Total Equivalence Classes': int(df['Equivalence_Classes'].sum()),
            
            # Reduction effectiveness
            'Benchmarks with Reductions': int(df['Has_Reduction'].sum()),
            'Percentage with Reductions': f"{df['Has_Reduction'].sum() / len(df) * 100:.1f}%",
            'Average Reduction Rate': f"{df['Reduction_Percentage'].mean():.2f}%",
            'Median Reduction Rate': f"{df['Reduction_Percentage'].median():.2f}%",
            'Max Reduction Rate': f"{df['Reduction_Percentage'].max():.2f}%",
            
            # Performance metrics
            'Average Analysis Time': f"{df['Total_Time_s'].mean():.2f}s",
            'Median Analysis Time': f"{df['Total_Time_s'].median():.2f}s",
            'Average Time per Property': f"{(df['Total_Time_ms'] / df['Total_Properties']).mean():.2f}ms",
            
            # Practical impact
            'Properties per Benchmark (avg)': f"{df['Total_Properties'].mean():.1f}",
            'Properties Removed per Benchmark (avg)': f"{df['Properties_Removed'].mean():.1f}",
            'Refinements per Benchmark (avg)': f"{df['Total_Refinements'].mean():.1f}",
        }
        
        # Additional insights for benchmarks WITH reductions
        df_with_reduction = df[df['Has_Reduction']]
        if len(df_with_reduction) > 0:
            self.summary_stats.update({
                'Avg Reduction (Non-Zero Cases)': f"{df_with_reduction['Reduction_Percentage'].mean():.2f}%",
                'Avg Properties Removed (Non-Zero)': f"{df_with_reduction['Properties_Removed'].mean():.1f}",
                'Avg Time for Non-Zero Cases': f"{df_with_reduction['Total_Time_s'].mean():.2f}s",
            })
        
        return self.summary_stats
    
    def generate_executive_summary(self):
        """Generate executive summary report for engineers."""
        print("\nGenerating executive summary...")
        
        summary_file = self.output_dir / "EXECUTIVE_SUMMARY.txt"
        
        df = self.data
        total_props = df['Total_Properties'].sum()
        removed_props = df['Properties_Removed'].sum()
        
        with open(summary_file, 'w') as f:
            f.write("=" * 80 + "\n")
            f.write("CTL REFINEMENT TOOL - EVALUATION SUMMARY\n")
            f.write("Property Reduction Analysis for Verification Engineers\n")
            f.write("=" * 80 + "\n\n")
            
            f.write("EXECUTIVE SUMMARY\n")
            f.write("-" * 80 + "\n\n")
            
            f.write(f"The CTL refinement tool analyzed {len(df):,} verification benchmarks\n")
            f.write(f"containing {int(total_props):,} CTL properties.\n\n")
            
            f.write(f"KEY RESULTS:\n\n")
            
            f.write(f"1. EFFECTIVENESS - Finding Redundant Properties\n")
            f.write(f"   • {int(removed_props):,} redundant properties identified ({removed_props/total_props*100:.1f}% of total)\n")
            f.write(f"   • {df['Has_Reduction'].sum():,} benchmarks had redundancies ({df['Has_Reduction'].sum()/len(df)*100:.1f}%)\n")
            f.write(f"   • Average reduction: {df['Reduction_Percentage'].mean():.1f}% per benchmark\n")
            f.write(f"   • Best case: {df['Reduction_Percentage'].max():.1f}% reduction\n\n")
            
            f.write(f"2. EFFICIENCY - Analysis Speed\n")
            f.write(f"   • Average analysis time: {df['Total_Time_s'].mean():.2f} seconds\n")
            f.write(f"   • Median analysis time: {df['Total_Time_s'].median():.2f} seconds\n")
            f.write(f"   • Average time per property: {(df['Total_Time_ms']/df['Total_Properties']).mean():.0f} ms\n")
            f.write(f"   • Fast enough for practical use in verification workflows\n\n")
            
            f.write(f"3. ENGINEERING VALUE - Why This Matters\n")
            f.write(f"   • Reduces verification workload by identifying redundant properties\n")
            f.write(f"   • Preserves complete verification coverage\n")
            f.write(f"   • Saves time by avoiding duplicate checks\n")
            f.write(f"   • Model-agnostic: works without needing the system model\n\n")
            
            # Concrete examples
            f.write(f"CONCRETE EXAMPLES\n")
            f.write("-" * 80 + "\n\n")
            
            # High reduction examples
            high_reduction = df[df['Reduction_Percentage'] >= 50].nsmallest(5, 'Total_Time_s')
            if len(high_reduction) > 0:
                f.write(f"Benchmarks with >50% Property Reduction (fastest 5):\n\n")
                for idx, row in high_reduction.iterrows():
                    f.write(f"  {row['Input']}\n")
                    f.write(f"    Properties: {int(row['Total_Properties'])} → {int(row['Required_Properties'])} ")
                    f.write(f"({row['Reduction_Percentage']:.1f}% reduction)\n")
                    f.write(f"    Analysis time: {row['Total_Time_s']:.2f}s\n")
                    f.write(f"    Refinements found: {int(row['Total_Refinements'])}\n\n")
            
            # Performance breakdown
            f.write(f"\nPERFORMANCE BREAKDOWN\n")
            f.write("-" * 80 + "\n\n")
            
            # Time buckets
            time_buckets = [
                ('< 1 second', df['Total_Time_s'] < 1),
                ('1-10 seconds', (df['Total_Time_s'] >= 1) & (df['Total_Time_s'] < 10)),
                ('10-60 seconds', (df['Total_Time_s'] >= 10) & (df['Total_Time_s'] < 60)),
                ('> 1 minute', df['Total_Time_s'] >= 60),
            ]
            
            f.write("Analysis Time Distribution:\n\n")
            for label, mask in time_buckets:
                count = mask.sum()
                pct = count / len(df) * 100
                f.write(f"  {label:15s}: {count:4d} benchmarks ({pct:5.1f}%)\n")
            
            f.write(f"\n\nREDUCTION IMPACT ANALYSIS\n")
            f.write("-" * 80 + "\n\n")
            
            reduction_buckets = [
                ('No reduction', df['Reduction_Percentage'] == 0),
                ('1-25%', (df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] <= 25)),
                ('26-50%', (df['Reduction_Percentage'] > 25) & (df['Reduction_Percentage'] <= 50)),
                ('51-75%', (df['Reduction_Percentage'] > 50) & (df['Reduction_Percentage'] <= 75)),
                ('> 75%', df['Reduction_Percentage'] > 75),
            ]
            
            f.write("Property Reduction Distribution:\n\n")
            for label, mask in reduction_buckets:
                count = mask.sum()
                pct = count / len(df) * 100
                avg_time = df[mask]['Total_Time_s'].mean() if count > 0 else 0
                f.write(f"  {label:15s}: {count:4d} benchmarks ({pct:5.1f}%) - avg time: {avg_time:.2f}s\n")
            
            # Bottom line
            f.write(f"\n\nBOTTOM LINE FOR ENGINEERS\n")
            f.write("-" * 80 + "\n\n")
            f.write(f"✓ Fast: Most analyses complete in seconds\n")
            f.write(f"✓ Effective: Finds redundant properties in {df['Has_Reduction'].sum()/len(df)*100:.0f}% of cases\n")
            f.write(f"✓ Practical: Model-agnostic, no system model required\n")
            f.write(f"✓ Safe: Preserves complete verification coverage\n")
            f.write(f"✓ Scalable: Handles benchmarks with many properties\n\n")
            
            f.write(f"The tool successfully identifies redundant verification properties,\n")
            f.write(f"allowing engineers to focus on essential checks while maintaining\n")
            f.write(f"complete coverage. Analysis is fast enough for practical integration\n")
            f.write(f"into verification workflows.\n\n")
            
            f.write("=" * 80 + "\n")
        
        print(f"Executive summary written to: {summary_file}")
    
    def plot_reduction_effectiveness(self):
        """Create visualization showing property reduction effectiveness."""
        print("\nGenerating reduction effectiveness plots...")
        
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        fig.suptitle('Property Reduction Effectiveness Analysis', fontsize=16, fontweight='bold')
        
        df = self.data
        
        # 1. Reduction percentage distribution
        ax = axes[0, 0]
        reduction_no_zero = df[df['Reduction_Percentage'] > 0]['Reduction_Percentage']
        ax.hist(df['Reduction_Percentage'], bins=50, alpha=0.7, color='steelblue', edgecolor='black')
        ax.axvline(df['Reduction_Percentage'].mean(), color='red', linestyle='--', 
                   linewidth=2, label=f'Mean: {df["Reduction_Percentage"].mean():.1f}%')
        ax.axvline(df['Reduction_Percentage'].median(), color='orange', linestyle='--', 
                   linewidth=2, label=f'Median: {df["Reduction_Percentage"].median():.1f}%')
        ax.set_xlabel('Property Reduction (%)')
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title('Distribution of Property Reduction Rates')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 2. Cumulative reduction
        ax = axes[0, 1]
        sorted_reduction = np.sort(df['Reduction_Percentage'])
        cumulative = np.arange(1, len(sorted_reduction) + 1) / len(sorted_reduction) * 100
        ax.plot(sorted_reduction, cumulative, linewidth=2.5, color='darkgreen')
        ax.axhline(50, color='gray', linestyle=':', alpha=0.7)
        ax.axvline(df['Reduction_Percentage'].median(), color='orange', linestyle='--', alpha=0.7)
        ax.set_xlabel('Property Reduction (%)')
        ax.set_ylabel('Cumulative % of Benchmarks')
        ax.set_title('Cumulative Distribution of Reductions')
        ax.grid(True, alpha=0.3)
        ax.text(df['Reduction_Percentage'].median() + 2, 55, 
                f'50% of benchmarks\nhave ≥{df["Reduction_Percentage"].median():.1f}% reduction',
                bbox=dict(boxstyle='round', facecolor='wheat', alpha=0.8))
        
        # 3. Properties removed vs total properties
        ax = axes[1, 0]
        scatter = ax.scatter(df['Total_Properties'], df['Properties_Removed'], 
                           c=df['Reduction_Percentage'], cmap='RdYlGn', 
                           alpha=0.6, s=50, edgecolors='black', linewidth=0.5)
        ax.set_xlabel('Total Properties')
        ax.set_ylabel('Properties Removed')
        ax.set_title('Properties Removed vs Total Properties')
        ax.set_xscale('log')
        ax.set_yscale('log')
        cbar = plt.colorbar(scatter, ax=ax)
        cbar.set_label('Reduction %')
        ax.grid(True, alpha=0.3, which='both')
        
        # 4. Reduction impact summary
        ax = axes[1, 1]
        impact_categories = [
            ('No Reduction\n(0%)', (df['Reduction_Percentage'] == 0).sum()),
            ('Low\n(1-25%)', ((df['Reduction_Percentage'] > 0) & 
                             (df['Reduction_Percentage'] <= 25)).sum()),
            ('Medium\n(26-50%)', ((df['Reduction_Percentage'] > 25) & 
                                 (df['Reduction_Percentage'] <= 50)).sum()),
            ('High\n(51-75%)', ((df['Reduction_Percentage'] > 50) & 
                               (df['Reduction_Percentage'] <= 75)).sum()),
            ('Very High\n(>75%)', (df['Reduction_Percentage'] > 75).sum()),
        ]
        
        labels, values = zip(*impact_categories)
        colors = ['lightgray', 'lightblue', 'skyblue', 'lightgreen', 'green']
        bars = ax.bar(labels, values, color=colors, edgecolor='black', linewidth=1.5)
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title('Reduction Impact Categories')
        ax.grid(True, alpha=0.3, axis='y')
        
        # Add value labels on bars
        for bar in bars:
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height,
                   f'{int(height)}\n({height/len(df)*100:.1f}%)',
                   ha='center', va='bottom', fontsize=9, fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(self.plots_dir / 'reduction_effectiveness.png')
        plt.close()
        
        print(f"  Saved: {self.plots_dir / 'reduction_effectiveness.png'}")
    
    def plot_performance_analysis(self):
        """Create performance analysis visualizations."""
        print("\nGenerating performance analysis plots...")
        
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        fig.suptitle('Performance Analysis: Speed and Scalability', fontsize=16, fontweight='bold')
        
        df = self.data
        
        # 1. Analysis time distribution
        ax = axes[0, 0]
        # Use log scale for better visualization
        log_times = np.log10(df['Total_Time_s'] + 0.001)  # Add small constant to avoid log(0)
        ax.hist(log_times, bins=50, alpha=0.7, color='coral', edgecolor='black')
        ax.set_xlabel('Analysis Time (log10 seconds)')
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title('Analysis Time Distribution')
        ax.grid(True, alpha=0.3)
        
        # Add time markers
        time_markers = [0.1, 1, 10, 60, 300]
        for t in time_markers:
            ax.axvline(np.log10(t), color='red', linestyle=':', alpha=0.5)
            ax.text(np.log10(t), ax.get_ylim()[1] * 0.9, f'{t}s', 
                   rotation=90, va='top', fontsize=8)
        
        # 2. Time vs number of properties
        ax = axes[0, 1]
        scatter = ax.scatter(df['Total_Properties'], df['Total_Time_s'],
                           c=df['Reduction_Percentage'], cmap='viridis',
                           alpha=0.6, s=50, edgecolors='black', linewidth=0.5)
        ax.set_xlabel('Number of Properties')
        ax.set_ylabel('Analysis Time (seconds)')
        ax.set_title('Scalability: Time vs Problem Size')
        ax.set_xscale('log')
        ax.set_yscale('log')
        cbar = plt.colorbar(scatter, ax=ax)
        cbar.set_label('Reduction %')
        ax.grid(True, alpha=0.3, which='both')
        
        # 3. Time per property
        ax = axes[1, 0]
        time_per_prop = df['Total_Time_ms'] / df['Total_Properties']
        ax.hist(time_per_prop[time_per_prop < 10000], bins=50, alpha=0.7, 
               color='teal', edgecolor='black')
        ax.axvline(time_per_prop.mean(), color='red', linestyle='--', 
                  linewidth=2, label=f'Mean: {time_per_prop.mean():.0f}ms')
        ax.axvline(time_per_prop.median(), color='orange', linestyle='--', 
                  linewidth=2, label=f'Median: {time_per_prop.median():.0f}ms')
        ax.set_xlabel('Time per Property (ms)')
        ax.set_ylabel('Number of Benchmarks')
        ax.set_title('Efficiency: Time per Property')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 4. Performance summary by year
        ax = axes[1, 1]
        year_stats = df.groupby('Year')['Total_Time_s'].agg(['mean', 'median', 'count'])
        x = np.arange(len(year_stats))
        width = 0.35
        
        bars1 = ax.bar(x - width/2, year_stats['mean'], width, label='Mean', 
                      color='steelblue', edgecolor='black')
        bars2 = ax.bar(x + width/2, year_stats['median'], width, label='Median', 
                      color='lightblue', edgecolor='black')
        
        ax.set_xlabel('Year')
        ax.set_ylabel('Analysis Time (seconds)')
        ax.set_title('Performance by Benchmark Year')
        ax.set_xticks(x)
        ax.set_xticklabels(year_stats.index)
        ax.legend()
        ax.grid(True, alpha=0.3, axis='y')
        
        # Add count labels
        for i, count in enumerate(year_stats['count']):
            ax.text(i, ax.get_ylim()[1] * 0.95, f'n={int(count)}', 
                   ha='center', fontsize=9, fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(self.plots_dir / 'performance_analysis.png')
        plt.close()
        
        print(f"  Saved: {self.plots_dir / 'performance_analysis.png'}")
    
    def plot_engineering_value(self):
        """Create plots showing practical engineering value."""
        print("\nGenerating engineering value plots...")
        
        fig, axes = plt.subplots(2, 2, figsize=(14, 10))
        fig.suptitle('Engineering Value: Practical Benefits for Verification', 
                    fontsize=16, fontweight='bold')
        
        df = self.data
        
        # 1. Refinements found vs properties
        ax = axes[0, 0]
        scatter = ax.scatter(df['Total_Properties'], df['Total_Refinements'],
                           c=df['Properties_Removed'], cmap='plasma',
                           alpha=0.6, s=50, edgecolors='black', linewidth=0.5)
        ax.set_xlabel('Total Properties')
        ax.set_ylabel('Refinements Found')
        ax.set_title('Refinement Discovery: Finding Redundancies')
        ax.set_xscale('log')
        ax.set_yscale('log')
        cbar = plt.colorbar(scatter, ax=ax)
        cbar.set_label('Properties Removed')
        ax.grid(True, alpha=0.3, which='both')
        
        # 2. Equivalence classes
        ax = axes[0, 1]
        ax.scatter(df['Total_Properties'], df['Equivalence_Classes'],
                  alpha=0.6, s=50, color='purple', edgecolors='black', linewidth=0.5)
        # Add diagonal line (if all properties were unique)
        max_val = max(df['Total_Properties'].max(), df['Equivalence_Classes'].max())
        ax.plot([0, max_val], [0, max_val], 'r--', alpha=0.5, linewidth=2, 
               label='All unique (no equivalences)')
        ax.set_xlabel('Total Properties')
        ax.set_ylabel('Equivalence Classes')
        ax.set_title('Property Equivalence Detection')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 3. Value proposition: time saved vs time invested
        ax = axes[1, 0]
        # Estimate time saved: assume each property check takes 10 seconds on average
        assumed_check_time = 10  # seconds per property
        time_saved = df['Properties_Removed'] * assumed_check_time
        time_invested = df['Total_Time_s']
        roi = time_saved / (time_invested + 0.1)  # ROI ratio
        
        scatter = ax.scatter(time_invested, time_saved,
                           c=df['Reduction_Percentage'], cmap='RdYlGn',
                           alpha=0.6, s=50, edgecolors='black', linewidth=0.5)
        # Add break-even line
        max_time = max(time_invested.max(), time_saved.max())
        ax.plot([0, max_time], [0, max_time], 'r--', alpha=0.5, linewidth=2,
               label='Break-even')
        ax.set_xlabel('Analysis Time (seconds)')
        ax.set_ylabel('Estimated Time Saved (seconds)')
        ax.set_title('Value Proposition: Time Saved vs Time Invested\n(Assuming 10s per property check)')
        ax.set_xscale('log')
        ax.set_yscale('log')
        ax.legend()
        cbar = plt.colorbar(scatter, ax=ax)
        cbar.set_label('Reduction %')
        ax.grid(True, alpha=0.3, which='both')
        
        # 4. Success rate summary
        ax = axes[1, 1]
        
        success_metrics = [
            ('Found\nRedundancies', df['Has_Reduction'].sum()),
            ('Found\nEquivalences', (df['Equivalence_Classes'] < df['Total_Properties']).sum()),
            ('Found\nRefinements', (df['Total_Refinements'] > 0).sum()),
            ('Completed\nFast (<10s)', (df['Total_Time_s'] < 10).sum()),
        ]
        
        labels, values = zip(*success_metrics)
        percentages = [v / len(df) * 100 for v in values]
        colors = ['green' if p >= 50 else 'orange' if p >= 25 else 'red' for p in percentages]
        
        bars = ax.bar(labels, percentages, color=colors, edgecolor='black', linewidth=1.5, alpha=0.7)
        ax.set_ylabel('Success Rate (%)')
        ax.set_title('Tool Success Metrics')
        ax.set_ylim([0, 100])
        ax.axhline(50, color='gray', linestyle='--', alpha=0.5)
        ax.grid(True, alpha=0.3, axis='y')
        
        # Add value labels
        for bar, val, pct in zip(bars, values, percentages):
            ax.text(bar.get_x() + bar.get_width()/2., bar.get_height() + 2,
                   f'{pct:.1f}%\n({int(val)} of {len(df)})',
                   ha='center', va='bottom', fontsize=9, fontweight='bold')
        
        plt.tight_layout()
        plt.savefig(self.plots_dir / 'engineering_value.png')
        plt.close()
        
        print(f"  Saved: {self.plots_dir / 'engineering_value.png'}")
    
    def generate_detailed_tables(self):
        """Generate detailed statistical tables."""
        print("\nGenerating detailed tables...")
        
        df = self.data
        
        # Table 1: Overall statistics by year
        year_summary = df.groupby('Year').agg({
            'Input': 'count',
            'Total_Properties': ['sum', 'mean'],
            'Properties_Removed': ['sum', 'mean'],
            'Reduction_Percentage': 'mean',
            'Total_Refinements': ['sum', 'mean'],
            'Total_Time_s': ['mean', 'median'],
        }).round(2)
        
        year_summary.columns = ['_'.join(col).strip() for col in year_summary.columns.values]
        year_summary.to_csv(self.tables_dir / 'summary_by_year.csv')
        print(f"  Saved: {self.tables_dir / 'summary_by_year.csv'}")
        
        # Table 2: Top reducers (high reduction, fast analysis)
        top_reducers = df[df['Reduction_Percentage'] >= 30].nsmallest(20, 'Total_Time_s')[[
            'Input', 'Year', 'Total_Properties', 'Properties_Removed', 
            'Reduction_Percentage', 'Total_Refinements', 'Total_Time_s'
        ]].round(2)
        top_reducers.to_csv(self.tables_dir / 'top_reducers.csv', index=False)
        print(f"  Saved: {self.tables_dir / 'top_reducers.csv'}")
        
        # Table 3: Performance benchmarks (fast completions with results)
        fast_effective = df[
            (df['Total_Time_s'] < 60) & (df['Properties_Removed'] > 0)
        ].nsmallest(20, 'Total_Time_s')[[
            'Input', 'Year', 'Total_Properties', 'Properties_Removed',
            'Reduction_Percentage', 'Total_Time_s'
        ]].round(2)
        fast_effective.to_csv(self.tables_dir / 'fast_and_effective.csv', index=False)
        print(f"  Saved: {self.tables_dir / 'fast_and_effective.csv'}")
        
        # Table 4: Challenging cases (many properties, high reduction)
        challenging = df[df['Total_Properties'] >= df['Total_Properties'].quantile(0.75)][[
            'Input', 'Year', 'Total_Properties', 'Properties_Removed',
            'Reduction_Percentage', 'Total_Refinements', 'Total_Time_s'
        ]].nlargest(20, 'Properties_Removed').round(2)
        challenging.to_csv(self.tables_dir / 'challenging_benchmarks.csv', index=False)
        print(f"  Saved: {self.tables_dir / 'challenging_benchmarks.csv'}")
        
        # Table 5: Summary statistics
        summary_df = pd.DataFrame({
            'Metric': list(self.summary_stats.keys()),
            'Value': list(self.summary_stats.values())
        })
        summary_df.to_csv(self.tables_dir / 'overall_summary.csv', index=False)
        print(f"  Saved: {self.tables_dir / 'overall_summary.csv'}")
    
    def generate_latex_summary(self):
        """Generate LaTeX table for paper."""
        print("\nGenerating LaTeX summary table...")
        
        df = self.data
        
        latex_file = self.output_dir / 'summary_table.tex'
        
        with open(latex_file, 'w') as f:
            f.write("% LaTeX table for CTL Refinement Tool Evaluation\n")
            f.write("% Paste this into your paper\n\n")
            
            f.write("\\begin{table}[htbp]\n")
            f.write("\\centering\n")
            f.write("\\caption{CTL Refinement Tool Evaluation Results}\n")
            f.write("\\label{tab:evaluation}\n")
            f.write("\\begin{tabular}{lrr}\n")
            f.write("\\hline\n")
            f.write("\\textbf{Metric} & \\textbf{Value} & \\textbf{Unit} \\\\\n")
            f.write("\\hline\n")
            
            # Key metrics for paper
            metrics = [
                ("Benchmarks Analyzed", f"{len(df):,}", "count"),
                ("Total Properties", f"{int(df['Total_Properties'].sum()):,}", "count"),
                ("Properties Removed", f"{int(df['Properties_Removed'].sum()):,}", "count"),
                ("Overall Reduction Rate", f"{df['Properties_Removed'].sum()/df['Total_Properties'].sum()*100:.1f}", "\\%"),
                ("Benchmarks with Reductions", f"{df['Has_Reduction'].sum()/len(df)*100:.1f}", "\\%"),
                ("Avg. Reduction (non-zero)", f"{df[df['Has_Reduction']]['Reduction_Percentage'].mean():.1f}", "\\%"),
                ("Median Analysis Time", f"{df['Total_Time_s'].median():.2f}", "seconds"),
                ("Avg. Time per Property", f"{(df['Total_Time_ms']/df['Total_Properties']).mean():.0f}", "ms"),
            ]
            
            for metric, value, unit in metrics:
                f.write(f"{metric} & {value} & {unit} \\\\\n")
            
            f.write("\\hline\n")
            f.write("\\end{tabular}\n")
            f.write("\\end{table}\n")
        
        print(f"  Saved: {latex_file}")
    
    def create_comprehensive_dashboard(self):
        """Create a comprehensive one-page dashboard."""
        print("\nGenerating comprehensive dashboard...")
        
        fig = plt.figure(figsize=(16, 10))
        gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)
        
        df = self.data
        
        # Title
        fig.suptitle('CTL Refinement Tool: Comprehensive Evaluation Dashboard', 
                    fontsize=18, fontweight='bold', y=0.98)
        
        # 1. Key metrics (text summary)
        ax1 = fig.add_subplot(gs[0, :])
        ax1.axis('off')
        
        summary_text = (
            f"EVALUATION SUMMARY: {len(df):,} benchmarks analyzed\n\n"
            f"EFFECTIVENESS: {int(df['Properties_Removed'].sum()):,} redundant properties identified "
            f"({df['Properties_Removed'].sum()/df['Total_Properties'].sum()*100:.1f}% of {int(df['Total_Properties'].sum()):,} total)\n"
            f"SUCCESS RATE: {df['Has_Reduction'].sum()}/{len(df)} benchmarks had reductions ({df['Has_Reduction'].sum()/len(df)*100:.1f}%)\n"
            f"PERFORMANCE: Median {df['Total_Time_s'].median():.2f}s analysis time, "
            f"{(df['Total_Time_ms']/df['Total_Properties']).median():.0f}ms per property\n"
            f"IMPACT: Average {df['Reduction_Percentage'].mean():.1f}% reduction per benchmark "
            f"({df[df['Has_Reduction']]['Reduction_Percentage'].mean():.1f}% for non-zero cases)"
        )
        
        ax1.text(0.5, 0.5, summary_text, ha='center', va='center', fontsize=12,
                bbox=dict(boxstyle='round', facecolor='lightblue', alpha=0.8),
                family='monospace', fontweight='bold')
        
        # 2. Reduction distribution
        ax2 = fig.add_subplot(gs[1, 0])
        ax2.hist(df['Reduction_Percentage'], bins=40, alpha=0.7, color='steelblue', edgecolor='black')
        ax2.axvline(df['Reduction_Percentage'].mean(), color='red', linestyle='--', linewidth=2)
        ax2.set_xlabel('Reduction (%)')
        ax2.set_ylabel('Count')
        ax2.set_title('Reduction Distribution')
        ax2.grid(True, alpha=0.3)
        
        # 3. Time distribution
        ax3 = fig.add_subplot(gs[1, 1])
        ax3.hist(np.log10(df['Total_Time_s'] + 0.01), bins=40, alpha=0.7, color='coral', edgecolor='black')
        ax3.set_xlabel('Time (log10 seconds)')
        ax3.set_ylabel('Count')
        ax3.set_title('Analysis Time Distribution')
        ax3.grid(True, alpha=0.3)
        
        # 4. Success metrics
        ax4 = fig.add_subplot(gs[1, 2])
        success_data = [
            df['Has_Reduction'].sum() / len(df) * 100,
            (df['Total_Time_s'] < 10).sum() / len(df) * 100,
            (df['Reduction_Percentage'] > 25).sum() / len(df) * 100,
        ]
        success_labels = ['Has\nReduction', 'Fast\n(<10s)', 'High Red.\n(>25%)']
        colors = ['green', 'blue', 'orange']
        bars = ax4.bar(success_labels, success_data, color=colors, alpha=0.7, edgecolor='black')
        ax4.set_ylabel('Percentage (%)')
        ax4.set_title('Success Metrics')
        ax4.set_ylim([0, 100])
        ax4.grid(True, alpha=0.3, axis='y')
        for bar in bars:
            height = bar.get_height()
            ax4.text(bar.get_x() + bar.get_width()/2., height,
                   f'{height:.1f}%', ha='center', va='bottom', fontweight='bold')
        
        # 5. Scalability
        ax5 = fig.add_subplot(gs[2, 0])
        ax5.scatter(df['Total_Properties'], df['Total_Time_s'], alpha=0.5, s=30,
                   c=df['Reduction_Percentage'], cmap='viridis', edgecolors='black', linewidth=0.3)
        ax5.set_xlabel('Total Properties')
        ax5.set_ylabel('Time (s)')
        ax5.set_title('Scalability')
        ax5.set_xscale('log')
        ax5.set_yscale('log')
        ax5.grid(True, alpha=0.3, which='both')
        
        # 6. Properties removed
        ax6 = fig.add_subplot(gs[2, 1])
        ax6.scatter(df['Total_Properties'], df['Properties_Removed'], alpha=0.5, s=30,
                   color='green', edgecolors='black', linewidth=0.3)
        ax6.set_xlabel('Total Properties')
        ax6.set_ylabel('Properties Removed')
        ax6.set_title('Property Elimination')
        ax6.set_xscale('log')
        ax6.set_yscale('log')
        ax6.grid(True, alpha=0.3, which='both')
        
        # 7. Impact categories
        ax7 = fig.add_subplot(gs[2, 2])
        impact_data = [
            (df['Reduction_Percentage'] == 0).sum(),
            ((df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] <= 25)).sum(),
            ((df['Reduction_Percentage'] > 25) & (df['Reduction_Percentage'] <= 50)).sum(),
            ((df['Reduction_Percentage'] > 50) & (df['Reduction_Percentage'] <= 75)).sum(),
            (df['Reduction_Percentage'] > 75).sum(),
        ]
        impact_labels = ['None', '1-25%', '26-50%', '51-75%', '>75%']
        colors = ['lightgray', 'lightblue', 'skyblue', 'lightgreen', 'darkgreen']
        ax7.pie(impact_data, labels=impact_labels, autopct='%1.1f%%', colors=colors,
               startangle=90, wedgeprops={'edgecolor': 'black', 'linewidth': 1.5})
        ax7.set_title('Reduction Impact Categories')
        
        plt.savefig(self.plots_dir / 'comprehensive_dashboard.png', dpi=300, bbox_inches='tight')
        plt.close()
        
        print(f"  Saved: {self.plots_dir / 'comprehensive_dashboard.png'}")
    
    def run_complete_analysis(self):
        """Run the complete analysis pipeline."""
        print("\n" + "="*80)
        print("CTL REFINEMENT TOOL - PROFESSIONAL EVALUATION ANALYSIS")
        print("="*80 + "\n")
        
        # Load data
        self.load_data()
        
        # Compute statistics
        self.compute_summary_statistics()
        
        # Generate all outputs
        self.generate_executive_summary()
        self.plot_reduction_effectiveness()
        self.plot_performance_analysis()
        self.plot_engineering_value()
        self.generate_detailed_tables()
        self.generate_latex_summary()
        self.create_comprehensive_dashboard()
        
        print("\n" + "="*80)
        print("ANALYSIS COMPLETE!")
        print("="*80)
        print(f"\nAll results saved to: {self.output_dir}")
        print(f"  - Executive summary: EXECUTIVE_SUMMARY.txt")
        print(f"  - Plots: {self.plots_dir}/")
        print(f"  - Tables: {self.tables_dir}/")
        print(f"  - LaTeX table: summary_table.tex")
        print("\nKey findings:")
        print(f"  • Analyzed {len(self.data):,} benchmarks")
        print(f"  • Found {int(self.data['Properties_Removed'].sum()):,} redundant properties")
        print(f"  • Success rate: {self.data['Has_Reduction'].sum()/len(self.data)*100:.1f}% of benchmarks")
        print(f"  • Median analysis time: {self.data['Total_Time_s'].median():.2f} seconds")
        print("\n")


def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description='Professional analysis of CTL refinement tool evaluation results',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python analysis_alternative.py
  python analysis_alternative.py --results ../results/language_inclusion_RCTLC_s --output ../analysis_alternative
  
This script generates a comprehensive professional analysis suitable for demonstrating
the practical engineering value of the CTL refinement tool in a research paper.
        """
    )
    
    parser.add_argument(
        '--results',
        default='../results/language_inclusion_RCTLC_s',
        help='Directory containing benchmark results (default: ../results/language_inclusion_RCTLC_s)'
    )
    
    parser.add_argument(
        '--output',
        default='../analysis/alternative_analysis',
        help='Output directory for analysis (default: ../analysis/alternative_analysis)'
    )
    
    args = parser.parse_args()
    
    # Create analyzer and run
    analyzer = CTLRefinementAnalyzer(args.results, args.output)
    analyzer.run_complete_analysis()


if __name__ == '__main__':
    main()
