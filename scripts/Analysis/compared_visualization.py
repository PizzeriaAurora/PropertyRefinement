import os
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import math
from typing import Dict, List, Tuple
import glob
from pathlib import Path
from tqdm import tqdm


from .utils import save_fig_helper


FORCE_EQUAL = True
cmap = plt.get_cmap('Greys')
colors = [ "lightgray", "darkgray", "dimgray", "silver", "slategray", "lightslategray", "gainsboro", "dimgrey", "black"]

#use teh colors from a cmap different than grays
#cmap = plt.get_cmap('Set3')
#colors = [cmap(i) for i in range(cmap.N)]


# Suppress noisy numpy warnings (polyfit RankWarning message, and invalid value RuntimeWarning)
import warnings
with warnings.catch_warnings():
    warnings.filterwarnings('ignore', message='Polyfit may be poorly conditioned')
    warnings.simplefilter('ignore', RuntimeWarning)

def create_averagetime_breakdown_per_category(
        df_dictionary: Dict[str, pd.DataFrame],
        output_folder: str) -> None:
    """Create a plot showing the average time breakdown per category for multiple datasets.

    df_dictionary: mapping from dataset name to DataFrame
    """

    try:
        # Categories definitions
        categories_def = {
            'Average': lambda df: df,
            '0%': lambda df: df[df['Reduction_Percentage'] == 0],
            '0-25%': lambda df: df[(df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] < 25)],
            '25-50%': lambda df: df[(df['Reduction_Percentage'] >= 25) & (df['Reduction_Percentage'] <= 50)],
            '>50%': lambda df: df[df['Reduction_Percentage'] > 50]
        }

        # Compute metrics per dataset
        per_dataset_metrics = {}
        for name, df in df_dictionary.items():
            cat_metrics = {}
            for cat_name, selector in categories_def.items():
                cat_df = selector(df)
                if len(cat_df) > 0:
                    cat_metrics[cat_name] = {
                        'refinement_time': pd.to_numeric(cat_df['Refinement_Time_ms'], errors='coerce').mean() / 1000.0,
                        'total_time': pd.to_numeric(cat_df['Total_Time_ms'], errors='coerce').mean() / 1000.0,
                        'count': len(cat_df)
                    }
                else:
                    cat_metrics[cat_name] = {
                        'refinement_time': 0.0,
                        'total_time': 0.0,
                        'count': 0
                    }
            per_dataset_metrics[name] = cat_metrics

        categories_list = list(categories_def.keys())
        x_pos = np.arange(len(categories_list))

        # plotting
        plt.figure(figsize=(3.6, 2.8))

        num_datasets = len(df_dictionary)
        bar_width = 0.16
        # we plot two bars per dataset (total, refinement) so total slots = 2 * num_datasets
        total_slots = 2 * num_datasets
        base_offset = -((total_slots - 1) / 2.0) * bar_width

        

        all_max = 0.0
        for i, (name, metrics) in enumerate(per_dataset_metrics.items()):
            total_vals = [metrics[cat]['total_time'] for cat in categories_list]
            ref_vals = [metrics[cat]['refinement_time'] for cat in categories_list]
            all_max = max(all_max, max(total_vals + ref_vals))

            total_offset = base_offset + (2 * i) * bar_width
            ref_offset = total_offset + bar_width

            plt.bar(x_pos + total_offset, total_vals, bar_width,
                    color=colors[i % len(colors)], alpha=0.8, label=f"{name} \nTotal")
            plt.bar(x_pos + ref_offset, ref_vals, bar_width,
                    color=colors[i % len(colors)], hatch='///', alpha=0.7, label=f"{name}\n Refinement")

        plt.xlabel('Property Reduction Percentage', fontsize=8, labelpad=1)
        plt.ylabel('Average Time (seconds)', fontsize=8, labelpad=1)
        plt.xticks(x_pos, categories_list, fontsize=8)
        plt.yticks(fontsize=8)
        plt.ylim(0, max(1.0, all_max * 1.25))
        #make legend horizontal and outside of the graph
        plt.legend(fontsize=7, loc='upper left',  ncol=2, columnspacing=0.5)
        plt.grid(True, alpha=0.3, axis='y')
        #plt.tight_layout()
        save_fig_helper('average_time_breakdown_per_category', output_folder)

    except Exception as e:
        print(f"Error creating timing breakdown plot: {e}")
        import traceback
        traceback.print_exc()
        return


def create_averagetime_breakdown_per_category_only_ref__(
        df_dictionary: Dict[str, pd.DataFrame],
        output_folder: str, use_average = True, 
        bar_width = 0.16) -> None:
    """Create a plot showing the average time breakdown per category for multiple datasets.

    df_dictionary: mapping from dataset name to DataFrame
    """

    try:
        # Categories definitions
        categories_def = {
            '0%': lambda df: df[df['Reduction_Percentage'] == 0],
            '0-25%': lambda df: df[(df['Reduction_Percentage'] > 0) & (df['Reduction_Percentage'] < 25)],
            '25-50%': lambda df: df[(df['Reduction_Percentage'] >= 25) & (df['Reduction_Percentage'] <= 50)],
            '>50%': lambda df: df[df['Reduction_Percentage'] > 50]
        }
        if use_average:
            categories_def['Average'] = lambda df: df            

        # Compute metrics per dataset
        per_dataset_metrics = {}
        for name, df in df_dictionary.items():
            cat_metrics = {}
            for cat_name, selector in categories_def.items():
                cat_df = selector(df)
                if len(cat_df) > 0:
                    cat_metrics[cat_name] = {
                        'refinement_time': pd.to_numeric(cat_df['Refinement_Time_ms'], errors='coerce').mean() / 1000.0,
                        'total_time': pd.to_numeric(cat_df['Total_Time_ms'], errors='coerce').mean() / 1000.0,
                        'count': len(cat_df)
                    }
                else:
                    cat_metrics[cat_name] = {
                        'refinement_time': 0.0,
                        'total_time': 0.0,
                        'count': 0
                    }
            per_dataset_metrics[name] = cat_metrics

        categories_list = list(categories_def.keys())
        x_pos = np.arange(len(categories_list))

        # plotting
        plt.figure(figsize=(3.6, 2.8))

        num_datasets = len(df_dictionary)
        
        # we plot two bars per dataset (total, refinement) so total slots = 2 * num_datasets
        total_slots = 2 * num_datasets
        base_offset = -((total_slots - 1) / 2.0) * bar_width

        
        color_to_bar={}
        all_max = 0.0
        for i, (name, metrics) in enumerate(per_dataset_metrics.items()):
            total_vals = [metrics[cat]['total_time'] for cat in categories_list]
            ref_vals = [metrics[cat]['refinement_time'] for cat in categories_list]
            all_max = max(all_max, max(total_vals + ref_vals))

            total_offset = base_offset + ( i) * bar_width
            ref_offset = total_offset + bar_width
            if name.find('(P)') >=0:
                hatch='///'
                color = color_to_bar[name.replace('(P)', '').strip()] 

            else:
                hatch=""
                # remove (S) from name
                color_to_bar[name.replace('(S)', '').strip()] = colors[i % len(colors)]
                color = colors[i % len(colors)]

            #plt.bar(x_pos + total_offset, total_vals, bar_width,
            #        color=colors[i % len(colors)], alpha=0.8, label=f"{name} \nTotal")
            plt.bar(x_pos + ref_offset, ref_vals, bar_width,
                    color=color, hatch=hatch, alpha=0.7, label=f"{name}")

        plt.xlabel('Property Reduction Percentage', fontsize=8, labelpad=1)
        plt.ylabel('Average Time (seconds)', fontsize=8, labelpad=1)
        plt.xticks(x_pos, categories_list, fontsize=8)
        plt.yticks(fontsize=8)
        plt.ylim(0, max(1.0, all_max * 1.25))
        #make legend horizontal and outside of the graph
        plt.legend(fontsize=7, loc='upper left',  ncol=2, columnspacing=0.5)
        plt.grid(True, alpha=0.3, axis='y')
        #plt.tight_layout()
        save_fig_helper(f'average_time_breakdown_per_category_no_ref_{use_average}', output_folder)

    except Exception as e:
        print(f"Error creating timing breakdown plot: {e}")
        import traceback
        traceback.print_exc()
        return

def create_averagetime_breakdown_per_category_only_ref(
        df_dictionary: Dict[str, pd.DataFrame],
        output_folder: str) -> None:
    """Create a plot showing the average time breakdown per category for multiple datasets."""
    create_averagetime_breakdown_per_category_only_ref__(
        df_dictionary, output_folder)
    create_averagetime_breakdown_per_category_only_ref__(
        df_dictionary, output_folder, use_average = False)

def __create_histogram_horizontal_property_removed__(
                                df_dict: Dict[str, pd.DataFrame],
                                output_folder: str,
                                by: str = "Year",
                                force_equal = False,
                                remove_zero = True
                                ):
    """
    Create histogram showing average reduction by benchmark category for multiple datasets.

    df_dict: mapping from name -> DataFrame
    """

    if not isinstance(df_dict, dict):
        raise TypeError("Expected df_dict to be a dict of name->DataFrame")

    # Work on copies to avoid mutating callers' data
    working = {name: df.copy() for name, df in df_dict.items()}

    # Optionally restrict to common Years/Inputs across datasets
    if force_equal:
        common_years = None
        common_inputs = None
        for df in working.values():
            years = set(df['Year'].dropna().unique())
            inputs = set(df['Input'].dropna().unique())
            common_years = years if common_years is None else (common_years & years)
            common_inputs = inputs if common_inputs is None else (common_inputs & inputs)
        if common_years is None:
            common_years = set()
        if common_inputs is None:
            common_inputs = set()
        for name in list(working.keys()):
            if len(common_years) > 0:
                working[name] = working[name][working[name]['Year'].isin(common_years)]
            if len(common_inputs) > 0:
                working[name] = working[name][working[name]['Input'].isin(common_inputs)]

    # Optionally remove zero-removed properties
    if remove_zero:
        for name in list(working.keys()):
            working[name] = working[name][working[name]['Properties_Removed'] > 0]

    # Prepare grouped stats per dataset
    grouped_per_dataset = {}
    for name, df in working.items():
        if df.empty:
            grouped_per_dataset[name] = pd.DataFrame(columns=[by, 'Properties_Removed'])
            continue
        grouped = df.groupby(by).agg({
            'Properties_Removed': ['mean', 'std', 'count'],
            'Reduction_Percentage': 'mean',
        }).round(2)
        # flatten
        grouped.columns = ['_'.join(col).strip() for col in grouped.columns]
        grouped = grouped.reset_index()
        #grouped['Properties_Removed_mean'] = grouped['Properties_Removed_mean'] / 1000.0
        grouped_per_dataset[name] = grouped

    # determine ordered list of categories: preserve order from first dataset then append unseen
    names = list(grouped_per_dataset.keys())
    if len(names) == 0:
        print('No datasets provided')
        return
    base_categories = []
    for name in names:
        cats = grouped_per_dataset[name][by].tolist()
        for c in cats:
            if c not in base_categories:
                base_categories.append(c)

    if len(base_categories) == 0:
        print('No categories found to plot')
        return

    # prepare matrix of values aligned to base_categories
    values_matrix = []
    for name in names:
        g = grouped_per_dataset[name].set_index(by)
        vals = [float(g.at[c, 'Properties_Removed_mean']) if c in g.index else 0.0 for c in base_categories]
        values_matrix.append(vals)

    # plotting horizontal grouped bars
    plt.figure(figsize=(5, 3))
    bar_width = 0.8 / max(1, len(names))
    y_pos = np.arange(len(base_categories))
    offsets = [(i - (len(names)-1)/2.0) * bar_width for i in range(len(names))]

    for i, name in enumerate(names):
        plt.barh(y_pos + offsets[i], values_matrix[i], bar_width, label=name, color=colors[i % len(colors)], edgecolor='black', alpha=0.8)

    # compute average diff relative to first dataset
    first_vals = np.array(values_matrix[0], dtype=float)
    if len(names) > 1:
        other_means = np.mean(np.array(values_matrix[1:], dtype=float), axis=0)
        # avoid division by zero
        diffs = np.where(first_vals == 0, 0.0, abs(first_vals - other_means)) #/ first_vals * 100.0)
    else:
        diffs = np.zeros_like(first_vals)
    #(Avg. Diff={round(d,2)})
    plt.yticks(range(len(base_categories)), [f"{cat}" for cat, d in zip(base_categories, diffs)])
    plt.xlabel('Average Properties Removed')
    plt.grid(True, alpha=0.3, axis='x')

    # overall mean difference (first - average of others)
    if len(names) > 1:
        # Use the aggregated grouped_per_dataset which contains the 'Properties_Removed_mean' column
        mean_first = np.nanmean(grouped_per_dataset[names[0]]['Properties_Removed_mean'].values) if len(grouped_per_dataset[names[0]])>0 else 0.0
        mean_others = np.nanmean([np.nanmean(grouped_per_dataset[n]['Properties_Removed_mean'].values) if len(grouped_per_dataset[n])>0 else 0.0 for n in names[1:]])
        # overall mean difference in number of properties (no ms -> do not divide)
        #overall_mean = abs(mean_first - mean_others)
        #if not np.isnan(overall_mean):
        #    plt.axvline(overall_mean, color='black', linestyle='--', linewidth=2, label=f'Overall Avg Diff.: {overall_mean:.1f} properties', alpha=0.7)
        plt.legend()

    plt.tight_layout()
    save_fig_helper(f'prop_removed_{by.lower()}_{"no_zero" if remove_zero else "w_zero"}', output_folder)


def __create_histogram_horizontal_time_saved__(
                                df_dict: Dict[str, pd.DataFrame],
                                output_folder: str,
                                by: str = "Year",
                                force_equal = False,
                                remove_zero = True
                                ):
    """
    Create histogram showing average reduction by benchmark category for multiple datasets.

    df_dict: mapping from name -> DataFrame
    """

    if not isinstance(df_dict, dict):
        raise TypeError("Expected df_dict to be a dict of name->DataFrame")

    # Work on copies to avoid mutating callers' data
    working = {name: df.copy() for name, df in df_dict.items()}

    # Optionally restrict to common Years/Inputs across datasets
    if force_equal:
        common_years = None
        common_inputs = None
        for df in working.values():
            years = set(df['Year'].dropna().unique())
            inputs = set(df['Input'].dropna().unique())
            common_years = years if common_years is None else (common_years & years)
            common_inputs = inputs if common_inputs is None else (common_inputs & inputs)
        if common_years is None:
            common_years = set()
        if common_inputs is None:
            common_inputs = set()
        for name in list(working.keys()):
            if len(common_years) > 0:
                working[name] = working[name][working[name]['Year'].isin(common_years)]
            if len(common_inputs) > 0:
                working[name] = working[name][working[name]['Input'].isin(common_inputs)]

    # Optionally remove zero-removed properties
    if remove_zero:
        for name in list(working.keys()):
            working[name] = working[name][working[name]['Properties_Removed'] > 0]

    # Prepare grouped stats per dataset
    grouped_per_dataset = {}
    for name, df in working.items():
        if df.empty:
            grouped_per_dataset[name] = pd.DataFrame(columns=[by, 'Refinement_Time_s_mean'])
            continue
        grouped = df.groupby(by).agg({
            'Refinement_Time_ms': ['mean', 'std', 'count'],
            'Reduction_Percentage': 'mean',
        }).round(2)
        # flatten
        grouped.columns = ['_'.join(col).strip() for col in grouped.columns]
        grouped = grouped.reset_index()
        grouped['Refinement_Time_s_mean'] = grouped['Refinement_Time_ms_mean'] / 1000.0
        grouped_per_dataset[name] = grouped

    # determine ordered list of categories: preserve order from first dataset then append unseen
    names = list(grouped_per_dataset.keys())
    if len(names) == 0:
        print('No datasets provided')
        return
    base_categories = []
    for name in names:
        cats = grouped_per_dataset[name][by].tolist()
        for c in cats:
            if c not in base_categories:
                base_categories.append(c)

    if len(base_categories) == 0:
        print('No categories found to plot')
        return

    # prepare matrix of values aligned to base_categories
    values_matrix = []
    for name in names:
        g = grouped_per_dataset[name].set_index(by)
        vals = [float(g.at[c, 'Refinement_Time_s_mean']) if c in g.index else 0.0 for c in base_categories]
        values_matrix.append(vals)

    # plotting horizontal grouped bars
    plt.figure(figsize=(5, 3))
    bar_width = 0.8 / max(1, len(names))
    y_pos = np.arange(len(base_categories))
    offsets = [(i - (len(names)-1)/2.0) * bar_width for i in range(len(names))]

    for i, name in enumerate(names):
        plt.barh(y_pos + offsets[i], values_matrix[i], bar_width, label=name, color=colors[i % len(colors)], edgecolor='black', alpha=0.8)

    # compute average diff relative to first dataset
    first_vals = np.array(values_matrix[0], dtype=float)
    if len(names) > 1:
        other_means = np.mean(np.array(values_matrix[1:], dtype=float), axis=0)
        # avoid division by zero
        diffs = np.where(first_vals == 0, 0.0, abs(first_vals - other_means)) #/ first_vals * 100.0)
    else:
        diffs = np.zeros_like(first_vals)
    #\n(Avg. Diff={round(d,2)} s)
    plt.yticks(range(len(base_categories)), [f"{cat}" for cat, d in zip(base_categories, diffs)])
    plt.xlabel('Refinement Time (s)')
    plt.grid(True, alpha=0.3, axis='x')

    # overall mean difference (first - average of others)
    if len(names) > 1:
        #mean_first = np.nanmean(working[names[0]]['Refinement_Time_ms'].values) if len(working[names[0]])>0 else 0.0
        #mean_others = np.nanmean([np.nanmean(working[n]['Refinement_Time_ms'].values) if len(working[n])>0 else 0.0 for n in names[1:]])
        ##overall_mean = abs(mean_first - mean_others) / 1000.0
        ##if not np.isnan(overall_mean):
        #    plt.axvline(overall_mean, color='black', linestyle='--', linewidth=2, label=f'Overall Avg Diff.: {overall_mean:.1f} s', alpha=0.7)
        plt.legend()

    plt.tight_layout()
    save_fig_helper(f'time_comparison_{by.lower()}_{"no_zero" if remove_zero else "w_zero"}', output_folder)



def create_time_saved_histogram_year(df_dict: Dict[str, pd.DataFrame], output_folder: str) -> None:
    __create_histogram_horizontal_time_saved__(df_dict, output_folder, by="Year", force_equal=FORCE_EQUAL, remove_zero=False)
    __create_histogram_horizontal_time_saved__(df_dict, output_folder, by="Year", force_equal=FORCE_EQUAL, remove_zero=True)


def create_time_saved_histogram_category(df_dict: Dict[str, pd.DataFrame], output_folder: str) -> None:
    __create_histogram_horizontal_time_saved__(df_dict, output_folder, by="Category", force_equal=FORCE_EQUAL, remove_zero=False)
    __create_histogram_horizontal_time_saved__(df_dict, output_folder, by="Category", force_equal=FORCE_EQUAL, remove_zero=True)


def create_prop_removed_histogram_year(df_dict: Dict[str, pd.DataFrame], output_folder: str) -> None:
    __create_histogram_horizontal_property_removed__(df_dict, output_folder, by="Year", force_equal=FORCE_EQUAL, remove_zero=False)
    __create_histogram_horizontal_property_removed__(df_dict, output_folder, by="Year", force_equal=FORCE_EQUAL, remove_zero=True)
def create_prop_removed_histogram_category(df_dict: Dict[str, pd.DataFrame], output_folder: str) -> None:
    __create_histogram_horizontal_property_removed__(df_dict, output_folder, by="Category", force_equal=FORCE_EQUAL, remove_zero=False)
    __create_histogram_horizontal_property_removed__(df_dict, output_folder, by="Category", force_equal=FORCE_EQUAL, remove_zero=True)

function_list = [
    create_averagetime_breakdown_per_category,
    create_averagetime_breakdown_per_category_only_ref,
    create_time_saved_histogram_year,
    create_time_saved_histogram_category,
    create_prop_removed_histogram_year,
    create_prop_removed_histogram_category
]


def create_compared_analysis(df_dictionary: Dict[str, pd.DataFrame], output_folder: str):
    "Create all plots for a comparison. MAKE SURE THE OUTPUT FOLDER EXISTS"
    print("Creating compared analysis...")
    for func in function_list:
        func(df_dictionary, output_folder)
    
