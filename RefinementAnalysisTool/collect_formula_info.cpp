


#include "formula_utils.h"
#include "utils.h"
#include "property.h"
#include "parser.h"
#include <fstream>


void printUsage()
{
    std::cout << "Usage: collect_formula_info <input> [output_dir]\n";
    std::cout << "Collects information about CTL formulas from the input.\n";
    std::cout << "Input can be either a single .txt file containing CTL formulas (one per line),\n";
    std::cout << "or a directory containing multiple .txt files.\n";
    std::cout << "If output_dir is not provided, 'formula_info' will be used.\n";
}

struct FolderStats {
    double avg_size = 0.0;
    double avg_atomic_complexity = 0.0;
    double avg_num_atoms = 0.0;
    double avg_simple_atoms = 0.0;
    double avg_comparison_atoms = 0.0;
    double avg_boolean_atoms = 0.0;
};

FolderStats analyze_folder(const std::string& input, const std::string& output_dir, const std::string& postfix)
{
    
     // Check if input exists
    if (!ctl::pathExists(input)) {
        std::cerr << "Error: Input path does not exist: " << input << "\n";
        return FolderStats{};
    }

    
    // Determine if input is a file or folder
    bool is_folder = ctl::isDirectory(input);
    std::vector<std::string> input_files;
    
    if (is_folder) {
        input_files = ctl::getTextFilesInDirectory(input);
        if (input_files.empty()) {
            std::cerr << "Error: No .txt files found in folder: " << input << "\n";
            return FolderStats{};
        }
    } else {
        // Single file
        input_files.push_back(input);
    }


    // In this folder, we create one output file called "info.csv"
    std::string output_file = ctl::joinPaths(output_dir, "info_per_file_" + postfix + ".csv");
    std::ofstream ofs(output_file);
    if (!ofs.is_open()) {
        std::cerr << "Error: Failed to open output file for writing: " << output_file << "\n";
        return FolderStats{};
    }

    // Write CSV header with new complexity metrics
    ofs << "File,NumProperties,TotalSize,AvgSize,AvgAtomicComplexity,AvgNumAtoms,AvgSimpleAtoms,AvgComparisonAtoms,AvgBooleanAtoms\n";
    
    int total_size = 0;
    double total_atomic_complexity = 0.0;
    double total_num_atoms = 0.0;
    double total_simple_atoms = 0.0;
    double total_comparison_atoms = 0.0;
    double total_boolean_atoms = 0.0;

    for (const auto& file : input_files) {
        auto properties = ctl::loadPropertiesFromFile(file);

        int total_size_per_file = 0;
        double total_atomic_complexity_per_file = 0.0;
        double total_num_atoms_per_file = 0.0;
        double total_simple_atoms_per_file = 0.0;
        double total_comparison_atoms_per_file = 0.0;
        double total_boolean_atoms_per_file = 0.0;
        
        for (const auto& prop_str : properties) {
            try {
                auto formula = ctl::formula_utils::preprocessFormula(*ctl::Parser::parseFormula(prop_str));
                auto property = ctl::CTLProperty::create(formula);
                total_size_per_file += property->size();
                
                // Get atomic propositions for counting (just variable names)
                auto simple_atoms = property->getAtomicPropositions();
                total_num_atoms_per_file += simple_atoms.size();
  
                // Get atomic propositions for complexity analysis (includes comparisons and boolean combos)
                auto atoms_for_analysis = ctl::formula_utils::getAtomicForAnalysis(*formula);
                
                // Analyze each atomic proposition for complexity
                int simple_count = 0;
                int comparison_count = 0;
                int boolean_count = 0;
                
                for (const auto& atom : atoms_for_analysis) {
                    // Check if atom contains comparison operators
                    bool has_comparison = (atom.find("<=") != std::string::npos ||
                                         atom.find(">=") != std::string::npos ||
                                         atom.find("==") != std::string::npos ||
                                         atom.find("!=") != std::string::npos ||
                                         atom.find('<') != std::string::npos ||
                                         atom.find('>') != std::string::npos);
                    
                    // Check if atom contains boolean combinations (& or |, not just negation)
                    bool has_boolean_combo = (atom.find('&') != std::string::npos ||
                                             atom.find('|') != std::string::npos);
                    
                    // Classify the atom
                    if (has_boolean_combo) {
                        // Complex boolean expression combining multiple atoms
                        boolean_count++;
                    } else if (has_comparison) {
                        // Comparison (including negated comparisons like !(x <= y))
                        comparison_count++;
                    } else {
                        // Simple atomic proposition (just a variable name, possibly negated)
                        simple_count++;
                    }
                }
                
                total_simple_atoms_per_file += simple_count;
                total_comparison_atoms_per_file += comparison_count;
                total_boolean_atoms_per_file += boolean_count;
                
                // Calculate atomic complexity score for this property
                // Simple atoms = 1 point, Comparisons = 2 points, Boolean combinations = 3 points
                double atomic_complexity = simple_count * 1.0 + comparison_count * 2.0 + boolean_count * 3.0;
                total_atomic_complexity_per_file += atomic_complexity;
                
            }
            catch (const std::exception& e) {
                std::cerr << "Warning: Failed to parse property '" << prop_str 
                          << "': " << e.what() << std::endl;
                continue;
            }
        }

        //write to CSV
        //file name is file - .txt
        std::string file_name = file;;
        if (file_name.size() >= 4 && file_name.substr(file_name.size() - 4) == ".txt") {
            file_name = file_name.substr(0, file_name.size() - 4);
            //remove path
            size_t pos = file_name.find_last_of("/\\");
            if (pos != std::string::npos) {
                file_name = file_name.substr(pos + 1);;
            }
        }
        
        double avg_size = properties.size() > 0 ? (double)total_size_per_file / properties.size() : 0.0;
        double avg_atomic_complexity = properties.size() > 0 ? total_atomic_complexity_per_file / properties.size() : 0.0;
        double avg_num_atoms = properties.size() != 0 ? total_num_atoms_per_file / properties.size() : 0.0;
        double avg_simple = properties.size() > 0 ? total_simple_atoms_per_file / properties.size() : 0.0;
        double avg_comparison = properties.size() > 0 ? total_comparison_atoms_per_file / properties.size() : 0.0;
        double avg_boolean = properties.size() > 0 ? total_boolean_atoms_per_file / properties.size() : 0.0;
        
        ofs << file_name << "," 
            << properties.size() << "," 
            << total_size_per_file << "," 
            << avg_size << ","
            << avg_atomic_complexity << ","
            << avg_num_atoms << ","
            << avg_simple << ","
            << avg_comparison << ","
            << avg_boolean << "\n";
            
        total_size += avg_size;
        total_atomic_complexity += avg_atomic_complexity;
        total_num_atoms += avg_num_atoms;
        total_simple_atoms += avg_simple;
        total_comparison_atoms += avg_comparison;
        total_boolean_atoms += avg_boolean;
    }
    
    // Calculate averages across all files and return
    size_t num_files = input_files.size();
    FolderStats stats;
    stats.avg_size = num_files > 0 ? total_size / num_files : 0.0;
    stats.avg_atomic_complexity = num_files > 0 ? total_atomic_complexity / num_files : 0.0;
    stats.avg_num_atoms = num_files > 0 ? total_num_atoms / num_files : 0.0;
    stats.avg_simple_atoms = num_files > 0 ? total_simple_atoms / num_files : 0.0;
    stats.avg_comparison_atoms = num_files > 0 ? total_comparison_atoms / num_files : 0.0;
    stats.avg_boolean_atoms = num_files > 0 ? total_boolean_atoms / num_files : 0.0;
    
    return stats;
}


int main(int argc, char* argv[]) {
    
    std::string input;
    std::string output_dir = "formula_info";

    if (argc < 2) {
        printUsage();
        return 1;
    }
    input = argv[1];
    if (argc >= 3) {
        output_dir = argv[2];
    }


    // Handle output directory
    if (ctl::pathExists(output_dir)) {
        if (ctl::isDirectory(output_dir)) {
            std::cout << "Warning: Output directory already exists: " << output_dir << "\n";
            std::cout << "         Existing files may be overwritten.\n";
        } else {
            std::cerr << "Error: Output path exists but is not a directory: " << output_dir << "\n";
            return -1;
        }
    } else {
        if (!ctl::createDirectory(output_dir)) {
            std::cerr << "Error: Failed to create output directory: " << output_dir << "\n";
            return -1;
        }
    }

    std::string overall_file = ctl::joinPaths(output_dir, "overall_info.csv");
    std::ofstream ofs_overall(overall_file);
    if (!ofs_overall.is_open()) {
        std::cerr << "Error: Failed to open output file for writing: " << overall_file << "\n";
        return -1;
    }
    //write header
    ofs_overall << "Folder,AvgSize,AvgAtomicComplexity,AvgNumAtoms,AvgONLYSimpleAtoms,AvgComparisonAtoms,AvgBooleanAtoms\n";



    // Determine if input is a file or folder
    bool is_folder = ctl::isDirectory(input);
    std::vector<std::string> input_directories;
    
    if (is_folder) {
        input_directories = ctl::getSubdirectoriesInDirectory(input);
        if (input_directories.empty()) {
            // No subdirectories, analyze the folder itself
            input_directories.push_back(input);
        }
    } else {
        // Single file
        input_directories.push_back(input);
    }


    
    


    for (int i=0; i < input_directories.size(); i++) {
        //postfix is the last part of the path
        std::string postfix = input_directories[i];
        size_t pos = postfix.find_last_of("/\\");
        if (pos != std::string::npos) {
            postfix = postfix.substr(pos + 1);;
        }
        FolderStats stats = analyze_folder(input_directories[i], output_dir, postfix);
        
        std::cout << postfix << ":\n";
        std::cout << "  Avg Size: " << stats.avg_size << "\n";
        std::cout << "  Avg Atomic Complexity: " << stats.avg_atomic_complexity << "\n";
        std::cout << "  Avg # Atoms: " << stats.avg_num_atoms << "\n";
        std::cout << "  Avg ONLY Simple Atoms: " << stats.avg_simple_atoms << "\n";
        std::cout << "  Avg Comparison Atoms: " << stats.avg_comparison_atoms << "\n";
        std::cout << "  Avg Boolean Atoms: " << stats.avg_boolean_atoms << "\n\n";
        
        ofs_overall << postfix << "," 
                    << stats.avg_size << ","
                    << stats.avg_atomic_complexity << ","
                    << stats.avg_num_atoms << ","
                    << stats.avg_simple_atoms << ","
                    << stats.avg_comparison_atoms << ","
                    << stats.avg_boolean_atoms << "\n";
    }
    


    return 0;
}