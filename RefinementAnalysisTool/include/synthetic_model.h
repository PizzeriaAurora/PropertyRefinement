#pragma once

#include <string>
#include <vector>
#include <random>
#include <sstream>

namespace ctl {

struct ModelConfig {
    int num_states = 10;
    int num_transitions = 20;
    int num_atomic_props = 5;
    int chain_states = 3;
    int bit_width = 4;
    unsigned int seed = 42;
};

class SyntheticModelGenerator {
private:
    ModelConfig config_;
    mutable std::mt19937 rng_;
    
public:
    explicit SyntheticModelGenerator(const ModelConfig& config = ModelConfig{});
    
    // Generate NuSMV model
    std::string generateNuSMVModel() const;
    
    // Generate atomic propositions
    std::vector<std::string> generateAtomicProps() const;
    
    // Generate states and transitions
    std::string generateStatesAndTransitions() const;
    
    // Generate initial conditions
    std::string generateInitialConditions() const;
    
    // Generate fairness constraints
    std::string generateFairnessConstraints() const;
    
private:
    // Helper methods
    std::string generateVariableDeclaration() const;
    std::string generateTransitionFunction() const;
    std::string generateChainStructure() const;
    std::string generateBitStructure() const;
    
    // Random generation helpers
    bool randomBool(double probability = 0.5) const;
    int randomInt(int min, int max) const;
    std::string randomChoice(const std::vector<std::string>& choices) const;
};

} // namespace ctl