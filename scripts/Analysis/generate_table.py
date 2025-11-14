"""
Generate a LaTeX table from a compared_summary.csv file.

Usage:
  python scripts/Analysis/generate_latex_table.py path/to/compared_summary.csv > table.tex

The script uses the provided table template: for each base approach (e.g. "Lang. Incl.", "Simulation")
it creates two subcolumns: P (Parallel) and S (Serial). If a mode is missing, the table cell is filled with
\TBFILL{--}.

Metrics mapping (template row -> CSV metric name):
  Benchmarks Finished -> 'Benchmark Completed'
  PRP (%) -> 'Average reduction (%)'
  Total Refinement Found -> 'Total refinements'
  Avg. Refinement Time -> 'Average refinement time (s)'
  Zero-% Benchmarks -> 'Percentage Zero Properties Removed'
  ETT -> 'Transitive Elimination'
  Avg. ETT -> 'Average Transitive Eliminations'

"""

from pathlib import Path
import pandas as pd


METRICS = [
    ("Benchmarks Finished", "Benchmark Completed"),
    ("PRP (\\%)", "Average reduction (%)"),
    ("Total Refinement Found", "Total refinements"),
    ("Avg. Refinement Time", "Average refinement time (s)"),
    ("Zero-\\% Benchmarks", "Percentage Zero Properties Removed"),
    ("ETT", "Transitive Elimination"),
    ("Avg. ETT", "Average Transitive Eliminations"),
]


def fmt_val(v):
    if pd.isna(v):
        return r"\TBFILL{--}"
    # integers as ints
    try:
        if float(v).is_integer():
            return str(int(float(v)))
    except Exception:
        pass
    # otherwise round to 3 significant digits for readability
    try:
        fv = float(v)
        return f"{fv:.3f}"
    except Exception:
        return str(v)


def generate_overview_table(csv_path: Path, output_folder = "."):
    df = pd.read_csv(csv_path)
    # build groups from column names (skip Metric)
    cols = list(df.columns)
    if cols[0].lower() != 'metric':
        raise SystemExit('Expected first column to be Metric')

    approaches = cols[1:]
    groups = []  # list of base names in order
    # map: group -> {'P': colname or None, 'S': colname or None}
    mapping = {}
    for col in approaches:
        base = col.split('(')[0].strip()
        mode = None
        if 'Parallel' in col or "(P)" in col:
            mode = 'P'
        elif 'Serial' in col or "(S)" in col:
            mode = 'S'
        else:
            # attempt to detect P/S keywords
            if 'P' == col.strip()[-1:]:
                mode = 'P'
            elif 'S' == col.strip()[-1:]:
                mode = 'S'
        if base not in mapping:
            mapping[base] = {'P': None, 'S': None}
            groups.append(base)
        if mode:
            mapping[base][mode] = col

    # start writing LaTeX table using template-like header
    out = []
    out.append('\\begin{table}[t]')
    out.append('\\centering')
    out.append('\\caption{Overview Of the Analysis Metrics. ``P \'\' denotes parallel execution, while ``S\'\' denotes sequential execution.}\\label{tab:metrics}')
    # build top header with multicolumns
    n_groups = len(groups)
    # compute column format: p{3cm} then 2 columns per group
    col_spec = 'p{3cm} ' + ' '.join(['c c'] * n_groups)
    out.append(f"\\begin{{tabular}}{{{col_spec}}}")
    out.append('\\toprule')

    # first header row: Metric & multicolumn for each group
    first_row = ['\\multirow{3}{*}{\\textbf{Metric}}']
    for g in groups:
        first_row.append(f'\\multicolumn{{2}}{{c}}{{\\textbf{{{g}}}}} ')
    out.append(' & '.join(first_row) + ' \\\\')

    # second header row: empty metric column then group secondary line (empty here)
    second_row = ['']
    for g in groups:
        second_row.append('\\multicolumn{2}{c}{\\textbf{}} ')
    out.append(' & '.join(second_row) + ' \\\\')

    # midrules and P/S header
    out.append('\\cmidrule(lr){2-' + str(1 + 2*n_groups) + '}')
    # header P S row
    subrow = ['']
    for g in groups:
        subrow.extend(['& {P} & {S}'])
    # We need to produce a row that starts with empty cell then P & S repeated
    # Build explicitly
    sub_entries = ['']
    for g in groups:
        sub_entries.append('{P}')
        sub_entries.append('{S}')
    out.append(' & '.join(sub_entries) + ' \\\\')

    out.append('\\midrule')

    # build rows for each metric
    for label, csv_name in METRICS:
        # find the row in df
        row = df[df['Metric'] == csv_name]
        if row.empty:
            # fill with blanks
            cells = [r'\TBFILL{--}' for _ in range(2 * n_groups)]
        else:
            row = row.iloc[0]
            cells = []
            for g in groups:
                # P
                colP = mapping[g].get('P')
                if colP and colP in df.columns:
                    valP = row[colP] if colP in row else None
                else:
                    valP = None
                # S
                colS = mapping[g].get('S')
                if colS and colS in df.columns:
                    valS = row[colS] if colS in row else None
                else:
                    valS = None
                cells.append(fmt_val(valP) if valP is not None else r'\TBFILL{--}')
                cells.append(fmt_val(valS) if valS is not None else r'\TBFILL{--}')

        out.append(' & '.join([label] + cells) + ' \\\\')

    out.append('\\bottomrule')
    out.append('\\end{tabular}')
    out.append('\\end{table}')

    txt = '\n'.join(out)
    with open(Path(output_folder) / "overview_table.tex", "w") as f:
        f.write(txt)
