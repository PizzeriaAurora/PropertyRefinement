#include "synthetic_model.h"
#include <algorithm>
#include <iomanip>

namespace ctl {

SyntheticModelGenerator::SyntheticModelGenerator(const ModelConfig& config)
    : config_(config), rng_(config.seed) {}

std::string SyntheticModelGenerator::generateNuSMVModel() const {
    std::stringstream ss;
    
    ss << "-- Synthetically Generated NuSMV Model\n";
    ss << "-- States: " << config_.num_states << ", Transitions: " << config_.num_transitions << "\n";
    ss << "-- Atomic Props: " << config_.num_atomic_props << ", Chain States: " << config_.chain_states << "\n";
    ss << "-- Bit Width: " << config_.bit_width << ", Seed: " << config_.seed << "\n\n";
    
    ss << "MODULE main\n\n";
    
    // Variable declarations
    ss << generateVariableDeclaration();
    ss << "\n";
    
    // Initial conditions
    ss << generateInitialConditions();
    ss << "\n";
    
    // Transition relations
    ss << generateStatesAndTransitions();
    ss << "\n";
    
    // Fairness constraints
    ss << generateFairnessConstraints();
    ss << "\n";
    
    return ss.str();
}

std::vector<std::string> SyntheticModelGenerator::generateAtomicProps() const {
    std::vector<std::string> props;
    for (int i = 0; i < config_.num_atomic_props; ++i) {
        props.push_back("p_" + std::to_string(i));
    }
    return props;
}

std::string SyntheticModelGenerator::generateVariableDeclaration() const {
    std::stringstream ss;
    
    ss << "VAR\n";
    
    // State variable
    ss << "  state : 0.." << (config_.num_states - 1) << ";\n";
    
    // Chain state variable
    if (config_.chain_states > 1) {
        ss << "  chain : 0.." << (config_.chain_states - 1) << ";\n";
    }
    
    // Bit variables
    for (int i = 0; i < config_.bit_width; ++i) {
        ss << "  bit" << i << " : boolean;\n";
    }
    
    // Atomic propositions as derived variables
    ss << "\nDEFINE\n";
    auto atomic_props = generateAtomicProps();
    for (size_t i = 0; i < atomic_props.size(); ++i) {
        // Create interesting conditions for atomic props
        switch (i % 4) {
            case 0:
                ss << "  " << atomic_props[i] << " := (state = " << (i % config_.num_states) << ");\n";
                break;
            case 1:
                if (config_.bit_width > 0) {
                    ss << "  " << atomic_props[i] << " := bit" << (i % config_.bit_width) << ";\n";
                } else {
                    ss << "  " << atomic_props[i] << " := (state >= " << (config_.num_states / 2) << ");\n";
                }
                break;
            case 2:
                if (config_.chain_states > 1) {
                    ss << "  " << atomic_props[i] << " := (chain = " << (i % config_.chain_states) << ");\n";
                } else {
                    ss << "  " << atomic_props[i] << " := (state < " << (config_.num_states / 2) << ");\n";
                }
                break;
            case 3:
                ss << "  " << atomic_props[i] << " := (state mod 2 = " << (i % 2) << ");\n";
                break;
        }
    }
    
    return ss.str();
}

std::string SyntheticModelGenerator::generateInitialConditions() const {
    std::stringstream ss;
    
    ss << "INIT\n";
    ss << "  state = 0 & ";
    
    if (config_.chain_states > 1) {
        ss << "chain = 0 & ";
    }
    
    for (int i = 0; i < config_.bit_width; ++i) {
        ss << "bit" << i << " = FALSE";
        if (i < config_.bit_width - 1) {
            ss << " & ";
        }
    }
    
    return ss.str();
}

std::string SyntheticModelGenerator::generateStatesAndTransitions() const {
    std::stringstream ss;
    
    ss << "TRANS\n";
    
    // Generate state transitions
    ss << "  case\n";
    
    for (int state = 0; state < config_.num_states; ++state) {
        ss << "    state = " << state << " : next(state) in {";
        
        // Generate possible successors
        std::vector<int> successors;
        
        // Always allow self-loop
        successors.push_back(state);
        
        // Add some forward transitions
        for (int i = 1; i <= 3; ++i) {
            int next_state = (state + i) % config_.num_states;
            successors.push_back(next_state);
        }
        
        // Add some random transitions based on seed
        std::mt19937 local_rng(config_.seed + state);
        if (local_rng() % 3 == 0) {
            int random_state = local_rng() % config_.num_states;
            successors.push_back(random_state);
        }
        
        // Remove duplicates and sort
        std::sort(successors.begin(), successors.end());
        successors.erase(std::unique(successors.begin(), successors.end()), successors.end());
        
        for (size_t i = 0; i < successors.size(); ++i) {
            ss << successors[i];
            if (i < successors.size() - 1) {
                ss << ", ";
            }
        }
        ss << "};\n";
    }
    
    ss << "    TRUE : next(state) = state;\n";
    ss << "  esac\n\n";
    
    // Chain transitions
    if (config_.chain_states > 1) {
        ss << "TRANS\n";
        ss << "  next(chain) = case\n";
        ss << "    chain < " << (config_.chain_states - 1) << " : {chain, chain + 1};\n";
        ss << "    TRUE : 0;\n";
        ss << "  esac\n\n";
    }
    
    // Bit transitions
    for (int i = 0; i < config_.bit_width; ++i) {
        ss << "TRANS\n";
        ss << "  next(bit" << i << ") = case\n";
        ss << "    state = " << ((i + 1) % config_.num_states) << " : !bit" << i << ";\n";
        ss << "    TRUE : bit" << i << ";\n";
        ss << "  esac\n\n";
    }
    
    return ss.str();
}

std::string SyntheticModelGenerator::generateFairnessConstraints() const {
    std::stringstream ss;
    
    // Add some fairness constraints for more interesting behavior
    ss << "-- Fairness constraints\n";
    
    for (int i = 0; i < std::min(3, config_.num_states); ++i) {
        ss << "FAIRNESS state = " << i << "\n";
    }
    
    if (config_.bit_width > 0) {
        ss << "FAIRNESS bit0 = TRUE\n";
    }
    
    return ss.str();
}

bool SyntheticModelGenerator::randomBool(double probability) const {
    std::uniform_real_distribution<double> dist(0.0, 1.0);
    return dist(rng_) < probability;
}

int SyntheticModelGenerator::randomInt(int min, int max) const {
    std::uniform_int_distribution<int> dist(min, max);
    return dist(rng_);
}

std::string SyntheticModelGenerator::randomChoice(const std::vector<std::string>& choices) const {
    if (choices.empty()) return "";
    std::uniform_int_distribution<size_t> dist(0, choices.size() - 1);
    return choices[dist(rng_)];
}

} // namespace ctl