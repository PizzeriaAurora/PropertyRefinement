
#pragma once
#include <sys/stat.h>
#include <dirent.h>
#include <algorithm>
#include <string>
#include <fstream>
#include "analyzer.h"
namespace ctl
{
    // Helper function to check if a path exists
bool pathExists(const std::string& path);
// Helper function to check if path is a directory
bool isDirectory(const std::string& path) ;

// Helper function to create directory
bool createDirectory(const std::string& path);
// Helper function to get all .txt files in a directory
std::vector<std::string> getTextFilesInDirectory(const std::string& dir_path);

// Helper function to write CSV results
void writeCsvResults(const std::string& csv_path, 
                     const std::string& input_name,
                     const ctl::Analyzer::AnalysisResult& result,
                     long long total_time_ms,
                     bool append = false); 
std::vector<std::string> loadPropertiesFromFile(const std::string& filename);
std::string joinPaths(const std::string& path1, const std::string& path2);
std::vector<std::string> getSubdirectoriesInDirectory(const std::string& dir_path);
} // namespace ctl


