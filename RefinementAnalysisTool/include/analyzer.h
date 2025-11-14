#pragma once

#include "property.h"
#include "refinement_graph.h"
#include "union_find.h"
#include "ctl_sat.h"
#include "memory_tracker.h"

#include <vector>
#include <unordered_map>
#include <thread>
#include <future>
#include <functional>



namespace ctl {

// Forward declaration
class PropertyGenerator;



struct RefinementResult {
    bool refines;
    std::chrono::milliseconds time_taken;
    size_t property1_index;
    size_t property2_index;
    size_t memory_used_kb = 0;  // Memory delta during this check
};




// Transitive optimization statistics
struct TransitiveOptimizationStats {
    std::vector<size_t> eliminated_per_class;
    double optimization_ratio = 0.0;
    size_t total_eliminated = 0;
    size_t total_before_optimization = 0;
};

// Main analyzer class
class Analyzer {
public:
    struct AnalysisResult {
        size_t total_properties;
        size_t equivalence_classes;
        size_t total_refinements;
        size_t required_properties = 0;  // Properties with in-degree 0 (not refined by others)
        std::vector<RefinementGraph> class_graphs;
        std::vector<std::vector<std::shared_ptr<CTLProperty>>> equivalence_class_properties;
        std::chrono::milliseconds parsing_time;
        std::chrono::milliseconds equivalence_time;
        std::chrono::milliseconds refinement_time;
        std::chrono::milliseconds total_time;
        
        // Transitive optimization results
        size_t transitive_eliminated = 0;
        size_t false_properties = 0;

        size_t peak_memory_kb = 0;
        size_t refinement_memory_kb = 0;
        size_t total_analysis_memory_kb = 0;
    };
    
private:
    std::vector<std::shared_ptr<CTLProperty>> properties_;
    std::vector<std::vector<std::shared_ptr<CTLProperty>>> equivalence_classes_;
    std::vector<RefinementGraph> refinement_graphs_;
    std::vector<std::string> false_properties_strings_;
    std::vector<size_t> false_properties_index_;
    std::vector<RefinementResult> result_per_property_;

    size_t total_skipped_ = 0;
    // Configuration
    bool use_parallel_analysis_ = true;
    bool use_syntactic_refinement_ = true;
    bool use_full_language_inclusion_ = false;  // New option for product-based approach
    bool use_ctl_sat_ = false; // Use CTL-SAT for refinement checking
    std::shared_ptr<CTLSATInterface> ctl_sat_interface_;
    size_t threads_ = std::thread::hardware_concurrency();
    
public:
    // Constructors and Destructor
    explicit Analyzer(const std::vector<std::string>& property_strings);
    explicit Analyzer(const std::vector<std::shared_ptr<CTLProperty>>& properties);
    ~Analyzer();
    
    // Copy and move operations
    Analyzer(const Analyzer&) = delete;
    Analyzer& operator=(const Analyzer&) = delete;
    Analyzer(Analyzer&&) = default;
    Analyzer& operator=(Analyzer&&) = default;
    
    // Factory methods
    static Analyzer fromFile(const std::string& filename);
    static Analyzer fromPropertyGenerator(const PropertyGenerator& generator);
    
    // Configuration
    void setParallelAnalysis(bool enabled) { use_parallel_analysis_ = enabled; }
    void setSyntacticRefinement(bool enabled) { use_syntactic_refinement_ = enabled; }
    void setFullLanguageInclusion(bool enabled) { use_full_language_inclusion_ = enabled; }
    void setThreads(size_t threads) { threads_ = threads; }
    void setUseTransitiveOptimization(bool use_transitive);
    void setUseCTLSAT(bool use_ctl_sat) { 
        use_ctl_sat_ = use_ctl_sat; 
    }
    bool getUseCTLSAT() const { return use_ctl_sat_; }

    void createCTLSATInterface(const std::string& ctl_sat_path="./extern/ctl-sat") {
        ctl_sat_interface_ = std::make_shared<CTLSATInterface>(ctl_sat_path);
    }

    std::shared_ptr<CTLSATInterface> getCTLSATInterface() const {
        return ctl_sat_interface_;
    }

    // Main analysis methods
    AnalysisResult analyze();
    void buildEquivalenceClasses();
    void analyzeRefinements();
    
    // Memory management
    static void clearGlobalCaches();
    void clearInstanceCaches();
    
    // Getters
    const std::vector<std::shared_ptr<CTLProperty>>& getProperties() const { return properties_; }
    const std::vector<std::vector<std::shared_ptr<CTLProperty>>>& getEquivalenceClasses() const { 
        return equivalence_classes_; 
    }
    const std::vector<RefinementGraph>& getRefinementGraphs() const { return refinement_graphs_; }
    
    // Output and reporting
    void writeReport(const std::string& filename, const AnalysisResult& result) const;
    void writeGraphs(const std::string& output_directory, const std::string& base_name = "refinement_class") const;
    void writeRequiredProperties(const std::string& filename) const;
    void writeEmptyProperties(const std::string& filename) const;
    void writeInfoPerProperty(const std::string& filename) const;
    // Statistics
    std::vector<std::shared_ptr<CTLProperty>> getRequiredProperties() const;
    std::unordered_map<std::string, size_t> getStatistics() const;
    TransitiveOptimizationStats getTransitiveOptimizationStats() const;
    
private:
    // Helper methods
    void _analyzeRefinementClassSerial(size_t class_index, bool use_transitive = true);
    void analyzeRefinementClassParallel();
    void analyzeRefinementsParallelOptimized();


    void _checkAndRemoveUnsatisfiableProperties();
    void _checkAndRemoveUnsatisfiablePropertiesParallel();
    
    // Helper method for refinement checking
    RefinementResult checkRefinement(const CTLProperty& prop1, const CTLProperty& prop2) const;
    
    
    // Progress bar display
    void printProgressBar(int percent, size_t current_class, size_t total_classes) const;
    // Parallel execution helpers
    std::vector<std::future<RefinementGraph>> createAnalysisTasks();
    RefinementGraph _analyzeClassTask(const std::vector<std::shared_ptr<CTLProperty>>& class_properties);
    RefinementGraph _analyzeClassTaskOptimized(const std::vector<std::shared_ptr<CTLProperty>>& class_properties);
    
    // Transitive optimization methods
    void applyTransitiveOptimization(AnalysisResult& result);
    void updateGraphWithOptimization(RefinementGraph& graph, 
                                   const std::unordered_set<std::string>& eliminated_properties);
    
    // Utility methods
    std::string formatDuration(std::chrono::milliseconds duration) const;
    std::string getCurrentTimestamp() const;
    
    // Additional configuration for transitive optimization
    bool use_transitive_optimization_ = true;  // Enable transitive closure optimization
    
    // Transitive optimization data
    TransitiveOptimizationStats transitive_stats_;
};

// Utility functions
namespace analyzer_utils {
    
    // Load properties from file
    std::vector<std::string> loadPropertiesFromFile(const std::string& filename);
    
    // Export functions
    void exportToCSV(const Analyzer::AnalysisResult& result, const std::string& filename);
    void exportToJSON(const Analyzer::AnalysisResult& result, const std::string& filename);
    
    // Statistics functions
    std::unordered_map<std::string, double> computeGraphStatistics(const RefinementGraph& graph);
    std::unordered_map<std::string, double> computeOverallStatistics(const Analyzer::AnalysisResult& result);
    
    // Validation functions
    bool validateRefinementResult(const std::shared_ptr<CTLProperty>& p1, 
                                 const std::shared_ptr<CTLProperty>& p2, 
                                 bool claimed_refinement);
}

} // namespace ctl