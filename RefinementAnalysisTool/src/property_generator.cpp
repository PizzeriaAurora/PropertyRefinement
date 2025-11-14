#include "property_generator.h"
#include "parser.h"
#include <fstream>
#include <sstream>
#include <algorithm>
#include <filesystem>

namespace ctl {

PropertyGenerator::PropertyGenerator(const GenerationConfig& config) 
    : config_(config), rng_(config.seed), probability_dist_(0.0, 1.0), time_dist_(1, config.max_time_bound) {
    generateAtomPools();
}

void PropertyGenerator::generateAtomPools() {
    atom_pools_.clear();
    atom_pools_.resize(config_.num_classes);
    
    for (size_t class_id = 0; class_id < config_.num_classes; ++class_id) {
        std::vector<std::string>& atoms = atom_pools_[class_id];
        
        // Generate basic atomic propositions
        for (size_t i = 0; i < config_.max_atoms_per_class; ++i) {
            atoms.push_back("p" + std::to_string(class_id) + "_" + std::to_string(i));
        }
        
        // Add some arithmetic variables for comparisons
        atoms.push_back("x" + std::to_string(class_id));
        atoms.push_back("y" + std::to_string(class_id));
        atoms.push_back("t" + std::to_string(class_id));
    }
}

std::unordered_map<size_t, std::vector<std::shared_ptr<CTLProperty>>> 
PropertyGenerator::generateProperties() const {
    std::unordered_map<size_t, std::vector<std::shared_ptr<CTLProperty>>> result;
    
    for (size_t class_id = 0; class_id < config_.num_classes; ++class_id) {
        result[class_id] = generateEquivalenceClass(class_id, config_.properties_per_class);
    }
    
    return result;
}

std::vector<std::shared_ptr<CTLProperty>> 
PropertyGenerator::generateEquivalenceClass(size_t class_id, size_t num_properties) const {
    std::vector<std::shared_ptr<CTLProperty>> properties;
    properties.reserve(num_properties);
    
    // Generate base properties
    size_t base_count = std::max(1UL, num_properties / (config_.refinements_per_property + 1));
    
    for (size_t i = 0; i < base_count; ++i) {
        auto base_prop = generateBaseProperty(class_id);
        properties.push_back(base_prop);
        
        // Generate refinements of this base property
        for (size_t j = 0; j < config_.refinements_per_property && properties.size() < num_properties; ++j) {
            auto refined = refineProperty(*base_prop, class_id);
            properties.push_back(refined);
        }
    }
    
    // Fill remaining slots with additional base properties
    while (properties.size() < num_properties) {
        properties.push_back(generateBaseProperty(class_id));
    }
    
    return properties;
}

std::shared_ptr<CTLProperty> PropertyGenerator::generateBaseProperty(size_t class_id) const {
    std::string formula = generateBinary(class_id, 0);
    return CTLProperty::create(formula);
}

std::string PropertyGenerator::generateAtom(size_t class_id) const {
    const auto& atoms = atom_pools_[class_id];
    return randomChoice(atoms);
}

std::string PropertyGenerator::generateComparison(size_t class_id) const {
    std::string var = "x" + std::to_string(class_id);
    std::vector<std::string> operators = {"==", "!=", "<", ">", "<=", ">="};
    std::string op = randomChoice(operators);
    int value = randomInt(0, 10);
    
    return var + " " + op + " " + std::to_string(value);
}

std::string PropertyGenerator::generatePrimary(size_t class_id, size_t depth) const {
    if (depth >= config_.max_depth) {
        // At max depth, only generate atoms
        if (randomBool(0.7)) {
            return generateAtom(class_id);
        } else {
            return generateComparison(class_id);
        }
    }
    
    std::vector<std::function<std::string()>> choices;
    
    // Basic atoms and comparisons
    choices.push_back([this, class_id]() { return generateAtom(class_id); });
    choices.push_back([this, class_id]() { return generateComparison(class_id); });
    
    // Boolean literals
    choices.push_back([]() { return "true"; });
    choices.push_back([]() { return "false"; });
    
    // Temporal operators
    if (randomBool(config_.temporal_probability)) {
        choices.push_back([this, class_id, depth]() { return generateTemporal(class_id, depth); });
    }
    
    // Parenthesized expressions
    if (depth < config_.max_depth - 1) {
        choices.push_back([this, class_id, depth]() { 
            return "(" + generateBinary(class_id, depth + 1) + ")"; 
        });
    }
    
    return randomChoice(choices)();
}

std::string PropertyGenerator::generateUnary(size_t class_id, size_t depth) const {
    if (randomBool(0.3) && depth < config_.max_depth) {
        // Negation
        return "!" + generateUnary(class_id, depth + 1);
    } else {
        return generatePrimary(class_id, depth);
    }
}

std::string PropertyGenerator::generateBinary(size_t class_id, size_t depth) const {
    if (depth >= config_.max_depth || !randomBool(config_.binary_probability)) {
        return generateUnary(class_id, depth);
    }
    
    std::string left = generateUnary(class_id, depth + 1);
    std::string op = randomChoice(binary_logical_ops_);
    std::string right = generateUnary(class_id, depth + 1);
    
    return left + " " + op + " " + right;
}

std::string PropertyGenerator::generateTemporal(size_t class_id, size_t depth) const {
    if (randomBool(0.7)) {
        // Unary temporal operator
        std::string op = randomChoice(unary_temporal_ops_);
        std::string interval_str = "";
        
        if (config_.use_time_intervals && randomBool(0.4)) {
            auto interval = generateTimeInterval();
            interval_str = interval.toString();
        }
        
        std::string operand = generateUnary(class_id, depth + 1);
        return op + interval_str + " " + operand;
    } else {
        // Binary temporal operator (U, W)
        std::string path_quantifier = randomBool(0.5) ? "E" : "A";
        std::string temporal_op = randomBool(0.8) ? "U" : "W";
        
        std::string left = generateUnary(class_id, depth + 1);
        std::string right = generateUnary(class_id, depth + 1);
        
        return path_quantifier + "(" + left + " " + temporal_op + " " + right + ")";
    }
}

std::shared_ptr<CTLProperty> PropertyGenerator::refineProperty(const CTLProperty& base_property, size_t class_id) const {
    std::string base_formula = base_property.toString();
    
    // Different refinement strategies
    std::vector<std::function<std::string()>> strategies;
    
    strategies.push_back([this, &base_formula, class_id]() { 
        return strengthenFormula(base_formula, class_id); 
    });
    strategies.push_back([this, &base_formula, class_id]() { 
        return addConjunct(base_formula, class_id); 
    });
    strategies.push_back([this, &base_formula, class_id]() { 
        return strengthenTemporal(base_formula, class_id); 
    });
    
    std::string refined_formula = randomChoice(strategies)();
    
    try {
        return CTLProperty::create(refined_formula);
    } catch (const std::exception&) {
        // If parsing fails, return the original property
        return std::make_shared<CTLProperty>(base_property.getFormulaPtr());
    }
}

std::string PropertyGenerator::strengthenFormula(const std::string& formula, size_t class_id) const {
    // Add a conjunct to strengthen the formula
    return addConjunct(formula, class_id);
}

std::string PropertyGenerator::addConjunct(const std::string& formula, size_t class_id) const {
    std::string additional = generateUnary(class_id, 0);
    return "(" + formula + ") & (" + additional + ")";
}

std::string PropertyGenerator::addDisjunct(const std::string& formula, size_t class_id) const {
    std::string additional = generateUnary(class_id, 0);
    return "(" + formula + ") | (" + additional + ")";
}

std::string PropertyGenerator::strengthenTemporal(const std::string& formula, size_t class_id) const {
    // Try to strengthen temporal operators
    // For now, just add a conjunct
    return addConjunct(formula, class_id);
}

TimeInterval PropertyGenerator::generateTimeInterval() const {
    int lower = randomInt(0, config_.max_time_bound / 2);
    int upper = randomInt(lower, config_.max_time_bound);
    return TimeInterval(lower, upper);
}

std::vector<std::string> PropertyGenerator::getAtomsForClass(size_t class_id) const {
    if (class_id < atom_pools_.size()) {
        return atom_pools_[class_id];
    }
    return {};
}

void PropertyGenerator::exportToFile(const std::string& filename, 
                                    const std::unordered_map<size_t, std::vector<std::shared_ptr<CTLProperty>>>& properties) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "# Generated CTL Properties\n";
    file << "# Classes: " << config_.num_classes << "\n";
    file << "# Properties per class: " << config_.properties_per_class << "\n";
    file << "# Seed: " << config_.seed << "\n\n";
    
    for (const auto& [class_id, class_properties] : properties) {
        file << "# Equivalence Class " << class_id << "\n";
        for (const auto& prop : class_properties) {
            file << prop->toString() << "\n";
        }
        file << "\n";
    }
    
    file.close();
}

void PropertyGenerator::exportClassToFile(const std::string& filename, 
                                         const std::vector<std::shared_ptr<CTLProperty>>& properties) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "# Generated CTL Properties for Single Class\n";
    file << "# Total properties: " << properties.size() << "\n\n";
    
    for (const auto& prop : properties) {
        file << prop->toString() << "\n";
    }
    
    file.close();
}

// Benchmark utilities implementation
namespace benchmark_utils {

std::vector<std::pair<std::shared_ptr<CTLProperty>, std::shared_ptr<CTLProperty>>> 
generateRefinementPairs(size_t num_pairs, const GenerationConfig& config) {
    PropertyGenerator generator(config);
    std::vector<std::pair<std::shared_ptr<CTLProperty>, std::shared_ptr<CTLProperty>>> pairs;
    pairs.reserve(num_pairs);
    
    for (size_t i = 0; i < num_pairs; ++i) {
        size_t class_id = i % config.num_classes;
        auto base = generator.generateBaseProperty(class_id);
        auto refined = generator.refineProperty(*base, class_id);
        pairs.emplace_back(refined, base); // refined refines base
    }
    
    return pairs;
}

std::vector<std::shared_ptr<CTLProperty>> 
generateComplexProperties(size_t num_properties, size_t min_depth, size_t max_depth,
                         const GenerationConfig& base_config) {
    GenerationConfig config = base_config;
    config.max_depth = max_depth;
    
    PropertyGenerator generator(config);
    std::vector<std::shared_ptr<CTLProperty>> properties;
    properties.reserve(num_properties);
    
    for (size_t i = 0; i < num_properties; ++i) {
        size_t class_id = i % config.num_classes;
        auto prop = generator.generateBaseProperty(class_id);
        
        // Ensure minimum depth by checking formula complexity
        size_t attempts = 0;
        while (attempts < 10) {
            std::string formula_str = prop->toString();
            size_t complexity = std::count_if(formula_str.begin(), formula_str.end(),
                                            [](char c) { return c == '(' || c == '&' || c == '|'; });
            
            if (complexity >= min_depth) {
                break;
            }
            
            prop = generator.generateBaseProperty(class_id);
            attempts++;
        }
        
        properties.push_back(prop);
    }
    
    return properties;
}

bool validateRefinementPair(const CTLProperty& refining, const CTLProperty& refined) {
    return refining.refines(refined, true); // Use syntactic check for validation
}

double measureRefinementCheckTime(const CTLProperty& p1, const CTLProperty& p2, 
                                 bool use_syntactic, size_t iterations) {
    auto start = std::chrono::high_resolution_clock::now();
    
    for (size_t i = 0; i < iterations; ++i) {
        volatile bool result = p1.refines(p2, use_syntactic);
        (void)result; // Suppress unused variable warning
    }
    
    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
    
    return static_cast<double>(duration.count()) / iterations; // Average time in microseconds
}

void generateTestSuite(const std::string& output_dir, const GenerationConfig& config) {
    std::filesystem::create_directories(output_dir);
    
    PropertyGenerator generator(config);
    auto properties_by_class = generator.generateProperties();
    
    // Export all properties
    generator.exportToFile(output_dir + "/all_properties.txt", properties_by_class);
    
    // Export each class separately
    for (const auto& [class_id, properties] : properties_by_class) {
        std::string class_file = output_dir + "/class_" + std::to_string(class_id) + ".txt";
        generator.exportClassToFile(class_file, properties);
    }
    
    // Generate refinement pairs for testing
    auto refinement_pairs = generateRefinementPairs(50, config);
    
    std::ofstream pairs_file(output_dir + "/refinement_pairs.txt");
    if (pairs_file.is_open()) {
        pairs_file << "# Refinement test pairs (format: refining_property -> refined_property)\n\n";
        
        for (const auto& [refining, refined] : refinement_pairs) {
            pairs_file << refining->toString() << " -> " << refined->toString() << "\n";
        }
        pairs_file.close();
    }
    
    // Generate configuration file
    std::ofstream config_file(output_dir + "/generation_config.txt");
    if (config_file.is_open()) {
        config_file << "# Test Suite Generation Configuration\n";
        config_file << "num_classes = " << config.num_classes << "\n";
        config_file << "properties_per_class = " << config.properties_per_class << "\n";
        config_file << "refinements_per_property = " << config.refinements_per_property << "\n";
        config_file << "max_depth = " << config.max_depth << "\n";
        config_file << "max_atoms_per_class = " << config.max_atoms_per_class << "\n";
        config_file << "temporal_probability = " << config.temporal_probability << "\n";
        config_file << "binary_probability = " << config.binary_probability << "\n";
        config_file << "use_time_intervals = " << (config.use_time_intervals ? "true" : "false") << "\n";
        config_file << "max_time_bound = " << config.max_time_bound << "\n";
        config_file << "seed = " << config.seed << "\n";
        config_file.close();
    }
}

} // namespace benchmark_utils

} // namespace ctl