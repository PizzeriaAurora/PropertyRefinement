#include "utils.h"

namespace ctl{

        // Helper function to check if a path exists
    bool pathExists(const std::string& path) {
        struct stat info;
        return stat(path.c_str(), &info) == 0;
    }

    // Helper function to check if path is a directory
    bool isDirectory(const std::string& path) {
        struct stat info;
        if (stat(path.c_str(), &info) != 0) {
            return false;
        }
        return S_ISDIR(info.st_mode);
    }

    // Helper function to create directory
    bool createDirectory(const std::string& path) {
        return mkdir(path.c_str(), 0755) == 0;
    }

    // Helper function to get all .txt files in a directory
    std::vector<std::string> getTextFilesInDirectory(const std::string& dir_path) {
        std::vector<std::string> files;
        DIR* dir = opendir(dir_path.c_str());
        if (!dir) {
            return files;
        }
        
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            std::string filename = entry->d_name;
            if (filename.length() > 4 && filename.substr(filename.length() - 4) == ".txt") {
                files.push_back(dir_path + "/" + filename);
            }
        }
        closedir(dir);
        
        std::sort(files.begin(), files.end());
        return files;
    }

    // Helper function to write CSV results
    void writeCsvResults(const std::string& csv_path, 
                        const std::string& input_name,
                        const Analyzer::AnalysisResult& result,
                        long long total_time_ms,
                        bool append) {
        std::ofstream csv_file;
        if (append) {
            csv_file.open(csv_path, std::ios::app);
        } else {
            csv_file.open(csv_path);
            // Write header
            csv_file << "Input,Total_Properties,Equivalence_Classes,Total_Refinements,"
                    << "Required_Properties,Properties_Removed,TransitiveEliminations,"
                    << "Parsing_Time_ms,Equivalence_Time_ms,"
                    << "Refinement_Time_ms,Total_Time_ms,"
                    << "Total_Analysis_Memory_kB, Refinement_Memory_kB"
                    << "\n";
        }
        
        int properties_removed = result.total_properties - result.required_properties;
        
        csv_file << input_name << ","
                << result.total_properties << ","
                << result.equivalence_classes << ","
                << result.total_refinements << ","
                << result.required_properties << ","
                << properties_removed << ","
                << result.transitive_eliminated << ","
                << result.parsing_time.count() << ","
                << result.equivalence_time.count() << ","
                << result.refinement_time.count() << ","
                << total_time_ms << ","
                //<< result.peak_memory_kb << ","
                << result.total_analysis_memory_kb << ","
                << result.refinement_memory_kb
                << "\n";

        csv_file.close();
    }

    std::vector<std::string> loadPropertiesFromFile(const std::string& filename) {
        std::vector<std::string> properties;
        std::ifstream file(filename);
        
        if (!file.is_open()) {
            throw std::runtime_error("Cannot open file: " + filename);
        }
        
        std::string line;
        while (std::getline(file, line)) {
            // Trim whitespace
            line.erase(0, line.find_first_not_of(" \t\r\n"));
            line.erase(line.find_last_not_of(" \t\r\n") + 1);
            
            // Skip empty lines and comments
            if (!line.empty() && line[0] != '#' && line[0] != '/') {
                properties.push_back(line);
            }
        }
        
        return properties;
    }

    std::string joinPaths(const std::string& path1, const std::string& path2) {
        if (path1.empty()) return path2;
        if (path2.empty()) return path1;
        if (path1.back() == '/' || path1.back() == '\\') {
            return path1 + path2;
        } else {
            return path1 + "/" + path2;
        }
    }

    std::vector<std::string> getSubdirectoriesInDirectory(const std::string& dir_path) {
                //list all subdirectories
        std::vector<std::string> subdirs;
        DIR* dir = opendir(dir_path.c_str());
        if (!dir) {
            std::cerr << "Error: Failed to open input directory: " << dir_path << "\n";
            return subdirs;
        }
        struct dirent* entry;
        while ((entry = readdir(dir)) != nullptr) {
            std::string dirname = entry->d_name;
            if (dirname != "." && dirname != "..") {
                std::string full_path = ctl::joinPaths(dir_path, dirname);
                if (ctl::isDirectory(full_path)) {
                    subdirs.push_back(full_path);
                }
            }
        }
        closedir(dir);
        return subdirs;
    }

}