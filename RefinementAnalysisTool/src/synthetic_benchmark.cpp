#include "synthetic_benchmark.h"
#include <fstream>
#include <sstream>
#include <iostream>
#include <filesystem>
#include <cstdlib>
#include <algorithm>

namespace ctl {

SyntheticBenchmarkRunner::SyntheticBenchmarkRunner(const BenchmarkConfig& config)
    : config_(config) {}

BenchmarkResult SyntheticBenchmarkRunner::runBenchmark(int iteration_id) const {
    BenchmarkResult result;
    
    try {
        std::cout << "--- CTL Refinement Benchmark " << iteration_id << " ---\n";
        std::cout << "Model: " << config_.num_states << " states, " << config_.num_transitions << " transitions\n";
        std::cout << "Properties: " << (config_.base_props * (config_.refined_props + 1) * config_.num_classes) 
                  << " total (" << config_.base_props << " base, " << config_.refined_props << " refined)\n";
        std::cout << std::string(30, '-') << "\n";
        
        // Create output directories
        std::filesystem::create_directories(config_.output_dir);
        std::filesystem::create_directories(config_.output_dir + "/models");
        std::filesystem::create_directories(config_.output_dir + "/properties");
        std::filesystem::create_directories(config_.output_dir + "/refinement_results");
        
        // 1. Generate model
        std::cout << "[" << iteration_id << ":1/4] Generating model...\n";
        std::string model_file = generateModel(iteration_id);
        std::cout << "  -> Model saved to '" << model_file << "'\n";
        
        // 2. Generate properties
        std::cout << "[" << iteration_id << ":2/4] Generating properties...\n";
        std::vector<std::string> all_properties = generateProperties(iteration_id);
        
        std::string props_file = config_.output_dir + "/properties/benchmark_properties_" + 
                                std::to_string(iteration_id) + ".txt";
        std::ofstream props_out(props_file);
        for (const auto& prop : all_properties) {
            props_out << prop << "\n";
        }
        props_out.close();
        
        result.total_properties = all_properties.size();
        std::cout << "  -> " << all_properties.size() << " properties saved to '" << props_file << "'\n";
        
        // 3. Brute-force model checking
        std::cout << "[" << iteration_id << ":3/4] Running Scenario B: Brute-force (checking all properties)...\n";
        auto start_time = now();
        result.time_brute_force = runNuSMVCheck(model_file, all_properties, iteration_id);
        std::cout << "  -> Brute-force time: " << result.time_brute_force << " seconds\n";
        
        // 4. Analysis + refined model checking
        std::cout << "[" << iteration_id << ":4/4] Running Scenario A: Analysis + Refined Check...\n";
        
        // Run refinement analysis
        auto analysis_start = now();
        Analyzer analyzer(all_properties);
        analyzer.analyze();
        auto analysis_end = now();
        result.analysis_time = duration(analysis_start, analysis_end);
        
        // Get required properties
        auto required_props = analyzer.getRequiredProperties();
        result.required_properties = required_props.size();
        
        std::cout << "  -> Analysis found " << required_props.size() << " required properties.\n";
        std::cout << "  -> Analysis time: " << result.analysis_time << " seconds\n";
        
        // Save required properties
        std::string req_props_file = config_.output_dir + "/properties/required_properties_" + 
                                    std::to_string(iteration_id) + ".txt";
        std::ofstream req_out(req_props_file);
        for (const auto& prop : required_props) {
            req_out << prop->toString() << "\n";
        }
        req_out.close();
        
        // Convert required properties to strings
        std::vector<std::string> required_prop_strings;
        for (const auto& prop : required_props) {
            required_prop_strings.push_back(prop->toString());
        }
        
        // Model check refined set
        result.model_checking_time = runNuSMVCheck(model_file, required_prop_strings, iteration_id);
        std::cout << "  -> Model checking time for refined set: " << result.model_checking_time << " seconds\n";
        
        result.time_with_analysis = result.analysis_time + result.model_checking_time;
        std::cout << "  -> Total time with analysis: " << result.time_with_analysis << " seconds\n";
        
        // Calculate speedup
        if (result.time_with_analysis > 0) {
            result.speedup = result.time_brute_force / result.time_with_analysis;
        } else {
            result.speedup = std::numeric_limits<double>::infinity();
        }
        
        // Report results
        std::cout << "\n[4/4] --- BENCHMARK RESULTS ---\n";
        std::cout << "Time for Brute-Force (check all " << result.total_properties << " props): " 
                  << result.time_brute_force << " s\n";
        std::cout << "Time with refinement method (analyze + check " << result.required_properties << " props): " 
                  << result.time_with_analysis << " s\n";
        std::cout << std::string(30, '-') << "\n";
        
        if (result.time_with_analysis < result.time_brute_force) {
            std::cout << "CONCLUSION: The refinement method is FASTER by " 
                      << (result.time_brute_force - result.time_with_analysis) 
                      << " seconds (" << result.speedup << "x speedup).\n";
        } else {
            double slowdown = result.time_with_analysis / result.time_brute_force;
            std::cout << "CONCLUSION: Brute-force is FASTER by " 
                      << (result.time_with_analysis - result.time_brute_force) 
                      << " seconds (" << slowdown << "x slower).\n";
            result.speedup = -slowdown;
        }
        
    } catch (const std::exception& e) {
        result.status = "error";
        result.error_message = e.what();
        std::cerr << "Benchmark error: " << e.what() << "\n";
    }
    
    return result;
}

std::string SyntheticBenchmarkRunner::generateModel(int iteration_id) const {
    ModelConfig model_config;
    model_config.num_states = config_.num_states;
    model_config.num_transitions = config_.num_transitions;
    model_config.num_atomic_props = config_.num_atomic_props;
    model_config.chain_states = config_.chain_states;
    model_config.bit_width = config_.bit_width;
    model_config.seed = config_.seed + iteration_id;
    
    SyntheticModelGenerator generator(model_config);
    std::string model_content = generator.generateNuSMVModel();
    
    std::string model_file = config_.output_dir + "/models/benchmark_model_" + 
                            std::to_string(iteration_id) + ".smv";
    std::ofstream out(model_file);
    out << model_content;
    out.close();
    
    return model_file;
}

std::vector<std::string> SyntheticBenchmarkRunner::generateProperties(int iteration_id) const {
    std::vector<std::string> atomic_props;
    for (int i = 0; i < config_.num_atomic_props; ++i) {
        atomic_props.push_back("p_" + std::to_string(i));
    }
    
    GenerationConfig prop_config;
    prop_config.num_classes = config_.num_classes;
    prop_config.properties_per_class = config_.base_props * (config_.refined_props + 1);
    prop_config.max_depth = 3;
    prop_config.use_time_intervals = false;
    prop_config.seed = config_.seed + iteration_id * 1000;
    
    PropertyGenerator generator(prop_config);
    auto properties_by_class = generator.generateProperties();
    
    std::vector<std::string> all_properties;
    for (const auto& [class_id, properties] : properties_by_class) {
        for (const auto& prop : properties) {
            all_properties.push_back(prop->toString());
        }
    }
    
    return all_properties;
}

double SyntheticBenchmarkRunner::runNuSMVCheck(const std::string& model_file, 
                                               const std::vector<std::string>& properties, 
                                               int iteration_id) const {
    if (properties.empty()) {
        return 0.0;
    }
    
    // Create temporary model file with CTL specs
    std::string temp_model = config_.output_dir + "/temp_model_" + std::to_string(iteration_id) + ".smv";
    
    // Read original model
    std::ifstream model_in(model_file);
    std::stringstream model_content;
    model_content << model_in.rdbuf();
    model_in.close();
    
    // Add CTL specifications
    std::ofstream temp_out(temp_model);
    temp_out << model_content.str();
    temp_out << "\n-- CTL Specifications\n";
    for (const auto& prop : properties) {
        temp_out << "CTLSPEC " << prop << "\n";
    }
    temp_out.close();
    
    // Run NuSMV
    auto start_time = now();
    
    std::string command = config_.nusmv_path + " " + temp_model + " > /dev/null 2>&1";
    int result = std::system(command.c_str());
    
    auto end_time = now();
    
    // Clean up
    std::filesystem::remove(temp_model);
    
    return duration(start_time, end_time);
}

std::vector<BenchmarkResult> SyntheticBenchmarkRunner::runBenchmarkSuite(const std::string& input_csv) const {
    std::vector<BenchmarkResult> results;
    
    std::ifstream csv_file(input_csv);
    if (!csv_file.is_open()) {
        throw std::runtime_error("Cannot open input CSV file: " + input_csv);
    }
    
    std::string line;
    std::getline(csv_file, line); // Skip header
    
    int iteration = 0;
    while (std::getline(csv_file, line)) {
        // Parse CSV line (simplified - assumes fixed format)
        std::istringstream iss(line);
        std::string token;
        
        std::vector<std::string> tokens;
        while (std::getline(iss, token, ',')) {
            tokens.push_back(token);
        }
        
        if (tokens.size() >= 8) {
            BenchmarkConfig iter_config = config_;
            iter_config.num_states = std::stoi(tokens[0]);
            iter_config.num_transitions = std::stoi(tokens[1]);
            iter_config.num_atomic_props = std::stoi(tokens[2]);
            iter_config.base_props = std::stoi(tokens[3]);
            iter_config.refined_props = std::stoi(tokens[4]);
            iter_config.num_classes = std::stoi(tokens[5]);
            iter_config.chain_states = std::stoi(tokens[6]);
            iter_config.bit_width = std::stoi(tokens[7]);
            
            SyntheticBenchmarkRunner iter_runner(iter_config);
            BenchmarkResult result = iter_runner.runBenchmark(iteration);
            results.push_back(result);
        }
        
        iteration++;
    }
    
    return results;
}

void SyntheticBenchmarkRunner::saveResults(const std::vector<BenchmarkResult>& results, 
                                          const std::string& output_file) const {
    std::ofstream out(output_file);
    
    // Write header
    out << "time_brute_force,total_time_with_analysis,analysis_time,time_mc_refined,diff,total_properties,required_properties,status,error_message\n";
    
    // Write data
    for (const auto& result : results) {
        out << result.time_brute_force << ","
            << result.time_with_analysis << ","
            << result.analysis_time << ","
            << result.model_checking_time << ","
            << result.speedup << ","
            << result.total_properties << ","
            << result.required_properties << ","
            << result.status << ","
            << result.error_message << "\n";
    }
    
    out.close();
    std::cout << "Results saved to: " << output_file << "\n";
}

} // namespace ctl