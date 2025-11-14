# CTL Refinement-Based Reduction Tool

A high-performance C++ tool for analyzing CTL (Computation Tree Logic) formula refinement relationships using automata-theoretic techniques. In essence, the tool converts a formula into an equivalent alternating tree automaton and check if the automaton is empty. Refinement A -> B is checked by 
- Checking that A and B are not empty
- B & !A is not empty

## What the Tool Does

This tool analyzes sets of CTL formulas to:
- **Check if Formulas are satisfiable** : This is model agnostic. 
- **Detect refinement relationships**: Identify when one CTL formula semantically refine another
- **Remove redundant properties**: Detects redundant properties that are refined by stronger ones
- **Optimize verification workflows**: Reduce the number of properties that need to be checked without losing verification coverage
- **Generate refinement graphs**: Visualize the logical relationships between properties 

The core algorithm uses alternating Büchi tree automata and language inclusion checking to determine when the models satisfying one formula are a subset of those satisfying another.


## Using the Tool

### Command Line Options

```bash
./check_refinements [OPTIONS] <input_file_or_directory>
```

**Core Options:**
- `-o, --output <dir>`: Output directory (default: `output`)
- `-v, --verbose`: Detailed progress and timing information
- `-h, --help`: Show help message

**Analysis Methods:**
- `--use-full-language-inclusion`: Use precise language inclusion (default)
- `--use-ctl-sat`: Use CTLSAT solver for refinement checks (experimental)
- `--syntactic-only`: Use syntactic refinement checks only
- `--use-simulation`: Use fast but incomplete simulation-based refinement checks (experimental)
- `--parallel`: Enable parallel processing for multiple files
- `-j, --threads <n>`: Number of parallel threads
- `--no-transitive`: Disable transitive reduction optimization

**Output Options:**
- `--graphs`: Generate refinement graph visualizations (PNG files)
- `--csv <file>`: Export results to CSV format

### Input Format

The tool accepts:
1. **Single file**: Text file with one CTL formula per line
2. **Directory**: Processes all `.txt` files in the directory

**Example input file (`example.txt`):**
```
# Lines starting with # are comments
AG(request -> AF(grant))
AG((request & priority) -> AF(grant))
AG(grant -> AF(!grant))
EF(error)
AG(!error)
```

### Output Files

The tool generates several output files in the specified directory:

- **`refinement_analysis.txt`**: Detailed analysis report
- **`required_properties.txt`**: Minimal set of properties needed
- **`false_properties.txt`**: Properties that are always false (unsatisfiable)
- **`refinement_class_*.png`**: Visual graphs of refinement relationships
- **`info_per_property.csv`**: Performance metrics for each property
- **`results.csv`**: Summary statistics


##  Build & Run


### Build the Tool
```bash
# Clone the repository (if not already done)
git clone <repository-url>
cd RefinementBasedCTLReduction

# Build everything (this installs dependencies and compiles)
./setup.sh

# The executable will be created as: check_refinements
```

### Run a Quick Test
```bash
# Create a test file
echo -e "AG(p)\nAG(p & q)\nAF(r)" > test.txt

# Run the analysis
./check_refinements test.txt

# View results
ls output/
```

### If You Want to Run Benchmarks
```bash
# Full setup with benchmark dataset (downloads large files)
./setup.sh full

# Run benchmarks
./run_benchmarks.sh ./assets/benchmark/Dataset/Properties simulation parallel
```



## Quick Start Examples

### Example 1: Basic Property Analysis
Create a file `properties.txt` with CTL formulas:
```
AG(p -> AF(q))
AG(p -> AF(q & r))
AG(p)
AF(q)
```

Run the analysis:
```bash
./check_refinements properties.txt
```

**Result**: The tool will identify that `AG(p -> AF(q & r))` refines `AG(p -> AF(q))` (if p leads to q∧r, it also leads to q), so the weaker property can be removed.

### Example 2: Safety and Liveness Properties
Create `safety_liveness.txt`:
```
AG(safe)
AG(safe -> AF(ready))
AG(EF(critical))
AG(critical -> AF(!critical))
```

Run with detailed output:
```bash
./check_refinements safety_liveness.txt --verbose -o output_dir
```

**Result**: The tool analyzes temporal dependencies and removes any properties that are logically implied by others.

##  Using the Library in Your Code

You can embed the CTL analysis library directly in your C++ applications. Here's a simple example:

### Basic Library Usage

```cpp
#include "property.h"
#include "CTLautomaton.h"
#include <iostream>
#include <memory>

using namespace ctl;

int main() {
    // Create CTL properties from formula strings
    auto prop1 = std::make_shared<CTLProperty>("AG(p & q)");
    auto prop2 = std::make_shared<CTLProperty>("AG(p)");
    auto prop3 = std::make_shared<CTLProperty>("EF(r)");
    
    std::cout << "=== CTL Property Analysis Example ===\n\n";
    
    // Check if properties are satisfiable (non-empty)
    std::cout << "Checking satisfiability:\n";
    std::cout << "- AG(p & q) is " << (prop1->isEmpty() ? "UNSATISFIABLE" : "SATISFIABLE") << "\n";
    std::cout << "- AG(p) is " << (prop2->isEmpty() ? "UNSATISFIABLE" : "SATISFIABLE") << "\n";
    std::cout << "- EF(r) is " << (prop3->isEmpty() ? "UNSATISFIABLE" : "SATISFIABLE") << "\n\n";
    
    // Check refinement relationships using simulation
    std::cout << "Checking refinements using simulation:\n";
    bool refines_sim = prop1->automaton().simulates(prop2->automaton());
    std::cout << "- AG(p & q) simulates AG(p): " << (refines_sim ? "YES" : "NO") << "\n";
    
    bool refines_opposite = prop2->automaton().simulates(prop1->automaton());
    std::cout << "- AG(p) simulates AG(p & q): " << (refines_opposite ? "YES" : "NO") << "\n\n";
    
    // Check semantic refinement using language inclusion
    std::cout << "Checking semantic refinement:\n";
    bool semantic_refines = prop1->refines(*prop2, false, false); // not syntactic, not verbose
    std::cout << "- AG(p & q) semantically refines AG(p): " << (semantic_refines ? "YES" : "NO") << "\n";
    
    // Display automaton information
    std::cout << "\n=== Automaton Details ===\n";
    std::cout << "AG(p & q) automaton:\n" << prop1->automaton().toString() << "\n\n";
    std::cout << "AG(p) automaton:\n" << prop2->automaton().toString() << "\n";
    
    return 0;
}
```

### Compilation

To compile your program using the library:

```bash
# Assuming you built the project and want to link against it
g++ -std=c++17 -I./RefinementAnalysisTool/include \
    your_program.cpp \
    -L./RefinementAnalysisTool/build \
    -lctl_analysis \
    -lz3 \
    -o your_program
```

### Key Library Classes

- **`CTLProperty`**: Main class for CTL formulas with parsing and analysis capabilities
- **`CTLautomaton`**: Alternating Büchi tree automaton representation
- **`CTLFormula`**: Abstract syntax tree for CTL formulas
- **Methods**:
  - `isEmpty()`: Check if the formula is unsatisfiable
  - `simulates()`: Fast simulation-based refinement check
  - `refines()`: Complete semantic refinement check using language inclusion

##  Building the Tool
### Step 1: Get the Code
```bash
# If you haven't cloned yet
git clone <your-repository-url>
cd RefinementBasedCTLReduction
```

### Step 2: One-Command Build
```bash
# This does EVERYTHING - installs dependencies, downloads CTLSAT, compiles
./setup.sh
```

**What `./setup.sh` does:**
1. Installs system dependencies (build-essential, cmake, libz3-dev)
2. Downloads and builds CTLSAT dependency
3. Compiles the refinement analysis tool
4. Creates the executable `check_refinements`

### Step 3: Verify It Works
```bash
# Check the executable exists
ls -la check_refinements

# Run help to see options
./check_refinements --help
```

### If You Want Full Benchmarks
```bash
# Downloads large benchmark dataset and sets up everything
./setup.sh full
```

### Manual Build (if setup.sh fails)
```bash
# Install dependencies manually
sudo apt update
sudo apt install build-essential cmake libz3-dev git

# Build CTLSAT dependency
cd assets/extern/
git clone https://github.com/nicolaprezza/CTLSAT.git
cd CTLSAT
make
cp ctl-sat ../ctl-sat
cd ../../..

# Build the main tool
cd RefinementAnalysisTool
mkdir build && cd build
cmake ..
make -j$(nproc)
cp ./ctl_refine_tool ../../check_refinements
cd ../..
```


### Basic Build
```bash
./setup.sh
```

This will:
1. Install required system dependencies (Ubuntu/Debian)
2. Download and build the CTLSAT dependency
3. Compile the refinement analysis tool
4. Create the executable `check_refinements`

### Full Build with Benchmarks
If you want to run the benchmark suite:
```bash
./setup.sh full
```

This additionally:
- Downloads the benchmark dataset (large files)
- Sets up the complete testing environment
- Prepares benchmark scripts

Note, we also provide a zip file. Simply unzip it and make sure it is placed in benchark/ directory


## CTL Grammar (BNF)

The tool accepts CTL formulas in the following grammar:

```bnf
formula       ::= implication

implication   ::= or_expr ("->" or_expr)*

or_expr       ::= and_expr ("|" and_expr)*

and_expr      ::= unary_expr ("&" unary_expr)*

unary_expr    ::= "!" unary_expr
               |  temporal_expr
               |  primary

temporal_expr ::= path_quantifier temporal_op primary
               |  temporal_op primary

path_quantifier ::= "A" | "E"

temporal_op   ::= "X" | "F" | "G" | "U" | "W" | "R"

primary       ::= "(" formula ")"
               |  "true" | "false"
               |  atomic_prop
               |  comparison

atomic_prop   ::= IDENTIFIER

comparison    ::= IDENTIFIER comp_op (IDENTIFIER | NUMBER)

comp_op       ::= "==" | "!=" | "<" | ">" | "<=" | ">="

IDENTIFIER    ::= [a-zA-Z_][a-zA-Z0-9_]*

NUMBER        ::= [0-9]+
```

### Supported CTL Operators

**Path Quantifiers:**
- `A`: For all paths (universal)
- `E`: There exists a path (existential)

**Temporal Operators:**
- `X φ`: Next - φ holds in the next state
- `F φ`: Future/Finally - φ holds eventually
- `G φ`: Globally - φ holds always
- `U φ`: Until - φ holds until ψ
- `W φ`: Weak Until - φ holds until ψ or forever
- `R φ`: Release - φ holds until ψ

**Boolean Operators:**
- `&`: Conjunction (AND)
- `|`: Disjunction (OR)  
- `!`: Negation (NOT)
- `->`: Implication

**Standard Combinations:**
- `AF φ`: φ holds on all paths eventually
- `EF φ`: φ holds on some path eventually
- `AG φ`: φ holds on all paths always
- `EG φ`: φ holds on some path always
- `A φ U ψ`: On all paths, φ until ψ
- `E φ U ψ`: On some path, φ until ψ
- `E φ R ψ`: On some path, φ releases ψ
- `A φ R ψ`: On all paths, φ releases ψ

### Example Formulas

```ctl
AG(ready -> AF(processing))           # Safety: ready leads to processing
EF(AG(stable))                        # Liveness: eventually permanently stable
AG(EF(checkpoint))                    # Fairness: infinitely often checkpoint
A(request U (grant | timeout))        # Until: request until resolution
AG((critical1 & critical2) -> false)  # Mutual exclusion
```

## Running Benchmarks

The tool includes a comprehensive benchmark suite for evaluation:

```bash
./run_benchmarks.sh <folder> <analysis_mode> <execution_mode> [no_transitive]
```

### Parameters

1. **`<folder>`**: Path to benchmark directory containing `.txt` files
2. **`<analysis_mode>`**: Analysis method
   - `simulation`: Fast simulation-based analysis (default)
   - `language_inclusion`: Precise language inclusion checking
   - `ctl_sat`: Integration with CTLSAT solver (experimental)
3. **`<execution_mode>`**: Execution strategy
   - `serial`: Process files sequentially
   - `parallel`: Process files in parallel (faster)
4. **`[no_transitive]`**: Optional flag to disable transitive optimization

### Benchmark replication

Run simulation analysis on dataset:
```bash
./run_benchmarks.sh ./assets/benchmark/Dataset/Properties language_inclusion serial
```
Parallel it's not fully implemented yet and might create segmentation faults. 

Run single benchmark (as we ran them)
```bash
./check_refinements ./assets/benchmark/Dataset/Properties/2018 --use-full-language-inclusion --verbose -o results_language_inclusion_RCTLC_p/2018 --serial
```



### Benchmark Output

Results are stored in directories named `results_<mode>_RCTLC_<suffix>/`:
- Each input file gets its own subdirectory
- Comprehensive logs in `logs/` directory
- CSV summaries for statistical analysis
- Performance metrics and timing data

## Advanced Features

### Parallel Processing
The tool supports multi-threaded analysis for improved performance:
```bash
./check_refinements --parallel -j 8 large_dataset/
```

### Custom Output Formats
Export results in various formats:
```bash
./check_refinements properties.txt --csv results.csv --graphs -o analysis_output
```



## License

This tool is provided for research and educational purposes. 

