#!/usr/bin/env python3
import sys
from pathlib import Path
from Analysis import generate_overview_table

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: generate_latex_table.py path/to/compared_summary.csv')
        sys.exit(1)
    generate_overview_table(Path(sys.argv[1]))
