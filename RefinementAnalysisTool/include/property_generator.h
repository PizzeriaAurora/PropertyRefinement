#pragma once

#include "property.h"
#include <random>
#include <unordered_map>

namespace ctl {

// Property generation configuration
struct GenerationConfig {
    size_t num_classes = 5;
    size_t properties_per_class = 10;
    size_t refinements_per_property = 3;
    size_t max_depth = 4;
    size_t max_atoms_per_class = 5;
    double temporal_probability = 0.6;
    double binary_probability = 0.7;
    bool use_time_intervals = true;
    int max_time_bound = 10;
    unsigned int seed = 42;
};

// Property generator for creating test cases and benchmarks
class PropertyGenerator {
private:
    GenerationConfig config_;
    mutable std::mt19937 rng_;
    
    // Atom pools for each equivalence class
    std::vector<std::vector<std::string>> atom_pools_;
    
    // Distribution objects for various choices
    mutable std::uniform_real_distribution<double> probability_dist_;
    mutable std::uniform_int_distribution<int> time_dist_;
    
    // Property templates and patterns
    std::vector<std::string> unary_temporal_ops_ = {"EF", "AF", "EG", "AG"};
    std::vector<std::string> binary_temporal_ops_ = {"EU", "AU"};
    std::vector<std::string> binary_logical_ops_ = {"&", "|", "->"};
    
public:
    explicit PropertyGenerator(const GenerationConfig& config = GenerationConfig{});
    
    // Main generation methods
    std::unordered_map<size_t, std::vector<std::shared_ptr<CTLProperty>>> 
    generateProperties() const;
    
    std::vector<std::shared_ptr<CTLProperty>> 
    generateEquivalenceClass(size_t class_id, size_t num_properties) const;
    
    // Individual property generation
    std::shared_ptr<CTLProperty> generateBaseProperty(size_t class_id) const;
    std::shared_ptr<CTLProperty> refineProperty(const CTLProperty& base_property, size_t class_id) const;
    std::shared_ptr<CTLProperty> abstractProperty(const CTLProperty& base_property, size_t class_id) const;
    
    // Configuration
    void setConfig(const GenerationConfig& config) { config_ = config; }
    const GenerationConfig& getConfig() const { return config_; }
    
    // Utility methods
    void generateAtomPools();
    std::vector<std::string> getAtomsForClass(size_t class_id) const;
    
    // Export generated properties
    void exportToFile(const std::string& filename, 
                     const std::unordered_map<size_t, std::vector<std::shared_ptr<CTLProperty>>>& properties) const;
    
    void exportClassToFile(const std::string& filename, 
                          const std::vector<std::shared_ptr<CTLProperty>>& properties) const;

private:
    // Helper methods for formula generation
    std::string generateAtom(size_t class_id) const;
    std::string generateComparison(size_t class_id) const;
    std::string generatePrimary(size_t class_id, size_t depth = 0) const;
    std::string generateUnary(size_t class_id, size_t depth = 0) const;
    std::string generateBinary(size_t class_id, size_t depth = 0) const;
    std::string generateTemporal(size_t class_id, size_t depth = 0) const;
    
    // Refinement generation helpers
    std::string strengthenFormula(const std::string& formula, size_t class_id) const;
    std::string weakenFormula(const std::string& formula, size_t class_id) const;
    std::string addConjunct(const std::string& formula, size_t class_id) const;
    std::string addDisjunct(const std::string& formula, size_t class_id) const;
    std::string strengthenTemporal(const std::string& formula, size_t class_id) const;
    
    // Utility helpers
    TimeInterval generateTimeInterval() const;
    std::string wrapInParentheses(const std::string& expr, bool force = false) const;
    bool needsParentheses(const std::string& expr, const std::string& context) const;
    
    // Random choice helpers
    template<typename Container>
    const typename Container::value_type& randomChoice(const Container& container) const {
        if (container.empty()) {
            throw std::runtime_error("Cannot choose from empty container");
        }
        std::uniform_int_distribution<size_t> dist(0, container.size() - 1);
        return container[dist(rng_)];
    }
    
    bool randomBool(double probability = 0.5) const {
        return probability_dist_(rng_) < probability;
    }
    
    int randomInt(int min, int max) const {
        std::uniform_int_distribution<int> dist(min, max);
        return dist(rng_);
    }
};

// Benchmark generation utilities
namespace benchmark_utils {
    
    // Generate properties with known refinement relationships
    std::vector<std::pair<std::shared_ptr<CTLProperty>, std::shared_ptr<CTLProperty>>> 
    generateRefinementPairs(size_t num_pairs, const GenerationConfig& config = GenerationConfig{});
    
    // Generate properties of specific complexity
    std::vector<std::shared_ptr<CTLProperty>> 
    generateComplexProperties(size_t num_properties, size_t min_depth, size_t max_depth,
                             const GenerationConfig& config = GenerationConfig{});
    
    // Load properties from various formats
    std::vector<std::shared_ptr<CTLProperty>> loadFromNuSMVFile(const std::string& filename);
    std::vector<std::shared_ptr<CTLProperty>> loadFromCSV(const std::string& filename, 
                                                         const std::string& formula_column = "formula");
    
    // Benchmark validation
    bool validateRefinementPair(const CTLProperty& refining, const CTLProperty& refined);
    double measureRefinementCheckTime(const CTLProperty& p1, const CTLProperty& p2, 
                                     bool use_syntactic = true, size_t iterations = 10);
    
    // Generate test suite
    void generateTestSuite(const std::string& output_dir, const GenerationConfig& config = GenerationConfig{});
}

} // namespace ctl