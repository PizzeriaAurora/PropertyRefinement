#pragma once

#include "analyzer.h"
#include "property_generator.h"
#include "synthetic_model.h"
#include "ctl_sat.h"
#include <string>
#include <vector>
#include <chrono>

namespace ctl {

struct BenchmarkConfig {
    int num_states = 10;
    int num_transitions = 20;
    int num_atomic_props = 5;
    int base_props = 5;
    int refined_props = 3;
    int num_classes = 3;
    int chain_states = 3;
    int bit_width = 4;
    std::string nusmv_path = "NuSMV";
    std::string ctl_sat_path = "./extern/ctl-sat";
    std::string output_dir = "benchmark_results";
    unsigned int seed = 42;
};

struct BenchmarkResult {
    double time_brute_force = 0.0;
    double time_with_analysis = 0.0;
    double analysis_time = 0.0;
    double model_checking_time = 0.0;
    int total_properties = 0;
    int required_properties = 0;
    double speedup = 1.0;
    std::string status = "success";
    std::string error_message = "";
};

class SyntheticBenchmarkRunner {
private:
    BenchmarkConfig config_;
    
public:
    explicit SyntheticBenchmarkRunner(const BenchmarkConfig& config = BenchmarkConfig{});
    
    // Run a single benchmark iteration
    BenchmarkResult runBenchmark(int iteration_id) const;
    
    // Run multiple benchmark iterations from CSV input
    std::vector<BenchmarkResult> runBenchmarkSuite(const std::string& input_csv) const;
    
    // Save results to CSV
    void saveResults(const std::vector<BenchmarkResult>& results, const std::string& output_file) const;
    
private:
    // Helper methods
    std::string generateModel(int iteration_id) const;
    std::vector<std::string> generateProperties(int iteration_id) const;
    double runNuSMVCheck(const std::string& model_file, const std::vector<std::string>& properties, int iteration_id) const;
    double runCTLSATCheck(const std::vector<std::string>& properties) const;
    
    // Timing utilities
    using TimePoint = std::chrono::high_resolution_clock::time_point;
    TimePoint now() const { return std::chrono::high_resolution_clock::now(); }
    double duration(const TimePoint& start, const TimePoint& end) const {
        return std::chrono::duration<double>(end - start).count();
    }
};

} // namespace ctl