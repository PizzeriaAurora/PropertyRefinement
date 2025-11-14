"""
CTL Formula Complexity Analysis Tool

This module provides comprehensive complexity metrics for CTL formulas
and analyzes the relationship between complexity and processing time.
The analyzer focuses on static syntactic metrics (operator counts,
path-quantifier counts, nesting depth, atomic propositions) and does
not attempt full CTL model checking or automata translation.
"""

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import os
import re
