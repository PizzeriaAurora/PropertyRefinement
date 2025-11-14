import os
import pandas as pd
import matplotlib.pyplot as plt

from typing import Dict, List

def save_fig_helper(name, output_folder, png_folder = "PNG", pgf_folder = "PGF"):

    png_output_folder = os.path.join(output_folder, png_folder)
    pgf_output_folder = os.path.join(output_folder, pgf_folder)
    os.makedirs(png_output_folder, exist_ok=True)
    os.makedirs(pgf_output_folder, exist_ok=True)
    png_file = os.path.join(png_output_folder, f'{name}.png')
    plt.savefig(png_file, 
               dpi=300, bbox_inches='tight')
    
    pgf_file = os.path.join(pgf_output_folder, f'{name}.pgf')
    plt.savefig(pgf_file, 
               dpi=300, bbox_inches='tight')
    plt.close()


def categorize_benchmarks(benchmark_names: List[str]) -> Dict[str, List[str]]:
    """
    Compact categorization for benchmarks.

    Goals:
    - Use a small set of categories (merge biological/domain examples into a single
      mc category).
    - Use a prefix-based fast path for common families and a keyword fallback.
    - Reduce the size of the 'Other' bucket while keeping categories meaningful
      for plotting and analysis.

    Returns a mapping from category name to list of benchmark filenames.
    """
    src = 'Resource Allocation'
    da = 'Distributed Algorithms'
    c = 'Concurrency'
    cp  = 'Comm. Protocols'
    mc = 'MC Applications'
    ae = 'Academic Examples'
    sp = 'Safety Protocols'
    categories = {
        c : [],
        cp: [],
        da: [],
        src: [],
        mc: [],
        ae : [],
        sp: [],
        'Other': []
    }

    # Prefix-based mapping for frequent datasets (fast path). Add entries as we
    # discover more families in the CSVs.
    prefix_map = {
        # Concurrency
        'philosophers': c,
        'philosophersdyn': c,
        'peterson': c,
        'lamportfastmutex': c,
        'dekker': c,
        'fischer': c,

        # Protocols / Communication
        'aslink': cp,
        'clientsandservers': cp,
        'clouddeployment': cp,
        'armcachecoherence': cp,
        'bart': cp,
        'tokenring': cp,

        # Distributed algorithms
        'neoelection': da,
        'raft': da,
        'referendum': da,

        # Scheduling and Resource Allocation
        'airplaneld': src,
        'autoflight': src,
        'bridgeandvehicles': src,
        'circulartrains': src,
        'resallocation': src,

    # Application / Benchmarks (merged biological + examples)
    'angiogenesis': mc,
    'circadianclock': mc,
    'mapk': mc,
    'polyorblf': mc,
    'polyorbnt': mc,
    'diffusion2d': mc,
    'dlcround': mc,
    'gppp': mc,
    'csrepetitions': mc,
    'businessprocesses': mc,
    'des': mc,
    'sharedmemory': mc,
    'smalloperatingsystem': mc,
    'dnawalker': mc,
    'refinewmg': mc,
    'cloudreconfiguration': mc,
    'bridge': mc,
    'discoverygpu': mc,
    'dlcflexbar': mc,
    'flexiblebarrier': mc,
    'sudoku': ae,
    'nqueens': ae,
    'triangulargrid': ae,
    'hexagonalgrid': ae,
    'noc3x3': ae,

    # Safety / protocol families
    'shieldiips': sp,
    'shieldiipt': sp,
    'shieldppps': sp,
    'shieldpppt': sp,
    'shieldrvs': sp,
    'shieldrvt': sp,

    # Additional mappings for frequent 'Other' families (mapped creatively)
    'robotmanipulation': mc,
    'fms': mc,
    'houseconstruction': mc,
    'joinfreemodules': mc,
    'permadmissibility': mc,
    'safebus': mc,
    'familyreunion': mc,
    'dlcshifumi': mc,
    'phasevariation': mc,
    'swimmingpool': mc,
    'drinkvendingmachine': mc,
    'echo': mc,
    'rers17pb113': mc,
    'rers17pb114': mc,
    'rers17pb115': mc,
    'doubleexponent': ae,
    'smarthome': mc,
    'erk': mc,
    'eratosthenes': ae,
    'hypertorusgrid': ae,
    'paramproductioncell': mc,
    'solitaire': ae,
    'neighborgrid': ae,
    'railroad': mc,
    'simpleloadbal': src,
    'squaregrid': ae,
    'viralepidemic': mc,
    'iotppurchase': mc,
    'egfr': mc,
    'hypercubegrid': ae,
    'dotandboxes': ae,
    'satellitememory': mc,
    'energybus': cp,
    'hospitaltriage': mc,
    'ibm319': mc,
    'ibm5964': mc,
    'ibm703': mc,
    'ibmb2s565s3960': mc,
    'multiwaysync': c,
    'pacemaker': mc,
    'planning': mc,
    'productioncell': mc,
    'ring': cp,
    'utahnoc': ae,
    'vasy2003': mc,
    'vehicularwifi': cp,
    'databasewithmutex': c,
    'rwmutex': c,
    'kanban': src,
    'globalresallocation': src,
    'tcpcondis': cp,
    'quasicertifprotocol': cp,
    }

    for name in benchmark_names:
        name_lower = str(name).lower()
        prefix = name_lower.split('-')[0]

        # Fast prefix mapping
        if prefix in prefix_map:
            categories[prefix_map[prefix]].append(name)
            continue

        # Keyword fallback mapping (compact)
        if any(k in name_lower for k in ['peterson', 'lamport', 'bakery', 'fischer', 'szymanski', 'mutex', 'philosopher']):
            categories[c].append(name)
        elif any(k in name_lower for k in ['protocol', 'aslink', 'brp', 'iprotocol', 'armcache', 'client', 'server', 'tcp', 'token']):
            categories[cp].append(name)
        elif any(k in name_lower for k in ['election', 'raft', 'referendum', 'consensus']):
            categories[da].append(name)
        elif any(k in name_lower for k in ['airplane', 'flight', 'train', 'bridge', 'scheduler', 'resalloc', 'parking', 'kanban', 'schedule']):
            categories[src].append(name)
        elif any(k in name_lower for k in ['bio', 'angio', 'circadian', 'mapk', 'dna', 'diffusion', 'gppp', 'des', 'businessprocess', 'cloud', 'discovery']):
            categories[mc].append(name)
        else:
            categories['Other'].append(name)

    return categories

