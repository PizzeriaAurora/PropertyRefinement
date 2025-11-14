"""Utility to parse log files and extract skipped-pairs counts.

Searches lines like:

[Transitive Closure] Skipped 6/240 pairs (2.5%)

and returns the left-hand integer (6) for each matching line.

Provides:
- parse_skipped_counts(path) -> List[int]
- simple CLI for quick runs
"""
from typing import List
import re
import sys

PATTERN = re.compile(r"\[Transitive Closure\]\s+Skipped\s+(\d+)\s*/\s*\d+\s+pairs")


def parse_skipped_counts(log_path: str) -> List[int]:
    """Read the given log file and return a list of skipped counts (integers).

    Args:
        log_path: path to the log file

    Returns:
        list of integers found in matching lines
    """
    counts: List[int] = []
    with open(log_path, "r", encoding="utf-8", errors="ignore") as fh:
        for line in fh:
            m = PATTERN.search(line)
            if m:
                try:
                    counts.append(int(m.group(1)))
                except ValueError:
                    # skip malformed numbers
                    continue
    return counts


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python parse_skipped_pairs.py <log-file>")
        sys.exit(2)
    path = sys.argv[1]
    counts = parse_skipped_counts(path)
    print(counts)
