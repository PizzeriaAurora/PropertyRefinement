#include "analyzer.h"
#include "CTLautomaton.h"

#include <algorithm>
#include <fstream>
#include <sstream>
#include <chrono>
#include <iomanip>
#include <thread>
#include <execution>
#include <filesystem>
#include <queue>
#include <stack>
#include <numeric>
#ifdef __unix__
#include <sys/ioctl.h>
#include <unistd.h>
#endif
#include <numeric>
#include "utils.h"
namespace ctl {



// Analyzer implementation
Analyzer::Analyzer(const std::vector<std::string>& property_strings) {
    properties_.reserve(property_strings.size());
    for (const auto& prop_str : property_strings) {
        //std::cout << "Loading property: " << prop_str << std::endl;
        try {
            
            properties_.push_back(CTLProperty::create(prop_str));
        } catch (const std::exception& e) {
            std::cerr << "Warning: Failed to parse property '" << prop_str 
                      << "': " << e.what() << std::endl;
        }
    }
    //std::cout << "Loaded " << properties_.size() << " properties.\n";
}

Analyzer::Analyzer(const std::vector<std::shared_ptr<CTLProperty>>& properties) 
    : properties_(properties) {}

Analyzer::~Analyzer() {
    // Clear instance caches and Z3 resources
    clearInstanceCaches();
}

void Analyzer::clearInstanceCaches() {
    // Clear instance caches from individual properties first
    // This will reset their automaton shared_ptrs, which in turn will clean up
    // SMT interfaces (including Z3 contexts and solvers) via unique_ptr destructors
    for (auto& property : properties_) {
        if (property) {
            property->clearInstanceCaches();
        }
    }
    
    // Clear equivalence class properties too
    for (auto& eq_class : equivalence_classes_) {
        for (auto& property : eq_class) {
            if (property) {
                property->clearInstanceCaches();
            }
        }
        eq_class.clear();
    }
    
    // Clear all instance-level caches
    properties_.clear();
    equivalence_classes_.clear();
    refinement_graphs_.clear();
    false_properties_strings_.clear();
    false_properties_index_.clear();
    result_per_property_.clear();
    
    // Clear CTL-SAT interface (releases Z3 resources if using Z3 backend)
    ctl_sat_interface_.reset();
    
    // Note: All Z3 resources (contexts, solvers) are managed via unique_ptr
    // and will be automatically freed when their owning objects are destroyed.
    // The above cleanup ensures proper destruction order and prevents memory leaks.
}

void Analyzer::clearGlobalCaches() {
    // Clear static caches in CTLProperty class
    // Note: This requires adding a static method to CTLProperty
    CTLProperty::clearStaticCaches();
}

Analyzer Analyzer::fromFile(const std::string& filename) {
    auto property_strings = loadPropertiesFromFile(filename);
    return Analyzer(property_strings);
}





void Analyzer::_checkAndRemoveUnsatisfiableProperties() {
    if (!use_ctl_sat_){
        //create all the abtas before hand. If the abta is empty, we remove the property!
        for (auto it = properties_.begin(); it != properties_.end(); ) {
            it->get()->simplify();
            if(it->get()->isEmpty()) {
                std::cerr << "Property " << it->get()->toString() << " has an empty ABTA and will be removed from analysis.\n";
                false_properties_strings_.push_back(it->get()->toString());
                false_properties_index_.push_back(std::distance(properties_.begin(), it));
                it = properties_.erase(it); // Remove property if ABTA creation fails
            } else {
                ++it; // Move to next property
            }
        }
    }else{

        for (auto it = properties_.begin(); it != properties_.end(); ) {
            // Use CTL-SAT to check for unsatisfiability
            std::cout << "Checking property for unsatisfiability using CTL-SAT: " << it->get()->toString() << std::endl;
            bool is_unsat = ctl_sat_interface_->isSatisfiable(it->get()->toString(),true) == false;
            if (is_unsat) {
                std::cerr << "Property " << it->get()->toString() << " is unsatisfiable according to CTL-SAT and will be removed from analysis.\n";
                false_properties_strings_.push_back(it->get()->toString());
                false_properties_index_.push_back(std::distance(properties_.begin(), it));
                it = properties_.erase(it); // Remove property if unsatisfiable
            } else {
                ++it; // Move to next property
            }
        }
    }
}



void Analyzer::_checkAndRemoveUnsatisfiablePropertiesParallel() {
    if (properties_.empty()) return;
    
    size_t n = properties_.size();
    std::vector<std::future<std::vector<size_t>>> futures;
    
    // Launch parallel tasks
    for (size_t t = 0; t < threads_; ++t) {
        futures.push_back(std::async(std::launch::async, [this, t, n]() -> std::vector<size_t> {
            std::vector<size_t> false_indices;
            
            // Each thread handles indices: t, t+threads_, t+2*threads_, ...
            for (size_t i = t; i < n; i += threads_) {
                bool is_false = false;
                
                if (!use_ctl_sat_) {
                    // Simplify and check if ABTA is empty
                    properties_[i]->simplify();
                    is_false = properties_[i]->isEmpty();
                } else {
                    // Use CTL-SAT to check for unsatisfiability
                    is_false = !ctl_sat_interface_->isSatisfiable(properties_[i]->toString(), true);
                }
                
                if (is_false) {
                    false_indices.push_back(i);
                }
            }
            
            return false_indices;
        }));
    }
    
    // Collect all false property indices from all threads
    std::vector<size_t> all_false_indices;
    for (auto& future : futures) {
        auto thread_false_indices = future.get();
        all_false_indices.insert(all_false_indices.end(), 
                                 thread_false_indices.begin(), 
                                 thread_false_indices.end());
    }
    
    // Sort indices in descending order to safely remove from properties_ vector
    std::sort(all_false_indices.rbegin(), all_false_indices.rend());
    
    // Store false properties and remove them
    for (size_t idx : all_false_indices) {
        false_properties_strings_.push_back(properties_[idx]->toString());
        false_properties_index_.push_back(idx);
    }   
}



Analyzer::AnalysisResult Analyzer::analyze() {
    auto start_time = std::chrono::high_resolution_clock::now();
    auto mem_initial = memory_utils::getCurrentMemoryUsage();
    AnalysisResult result;
    result.total_properties = properties_.size();
    //result.initial_memory_mb = mem_initial.getResidentMB();
    // Parse time (already done in constructor, so this is 0)
    auto parse_end = std::chrono::high_resolution_clock::now();
    result.parsing_time = std::chrono::duration_cast<std::chrono::milliseconds>(parse_end - start_time);
    
    
    result.false_properties = 0;
    if (use_parallel_analysis_) {
        std::cout << "Checking and removing unsatisfiable properties in parallel...\n";
        _checkAndRemoveUnsatisfiableProperties();
    } else {
        std::cout << "Checking and removing unsatisfiable properties serially...\n";
        _checkAndRemoveUnsatisfiableProperties();
    }
    
    //if (!use_ctl_sat_){
    //    //create all the abtas before hand. If the abta is empty, we remove the property!
    //    for (auto it = properties_.begin(); it != properties_.end(); ) {
    //        it->get()->simplify();
    //        if(it->get()->isEmpty()) {
    //            std::cerr << "Property " << it->get()->toString() << " has an empty ABTA and will be removed from analysis.\n";
    //            false_properties_strings_.push_back(it->get()->toString());
    //            false_properties_index_.push_back(std::distance(properties_.begin(), it));
    //            it = properties_.erase(it); // Remove property if ABTA creation fails
    //            result.false_properties++;
    //        } else {
    //            ++it; // Move to next property
    //        }
    //    }
    //}else{
//
    //    for (auto it = properties_.begin(); it != properties_.end(); ) {
    //        // Use CTL-SAT to check for unsatisfiability
    //        bool is_unsat = ctl_sat_interface_->isSatisfiable(it->get()->toString(),true) == false;
    //        if (is_unsat) {
    //            std::cerr << "Property " << it->get()->toString() << " is unsatisfiable according to CTL-SAT and will be removed from analysis.\n";
    //            false_properties_strings_.push_back(it->get()->toString());
    //            false_properties_index_.push_back(std::distance(properties_.begin(), it));
    //            it = properties_.erase(it); // Remove property if unsatisfiable
    //            result.false_properties++;
    //        } else {
    //            ++it; // Move to next property
    //        }
    //    }
    //}
    
    result.false_properties = false_properties_strings_.size();
    // Build equivalence classes
    auto equiv_start = std::chrono::high_resolution_clock::now();
    buildEquivalenceClasses();
    auto equiv_end = std::chrono::high_resolution_clock::now();
    result.equivalence_time = std::chrono::duration_cast<std::chrono::milliseconds>(equiv_end - equiv_start);
    result.equivalence_classes = equivalence_classes_.size();
    result.equivalence_class_properties = equivalence_classes_;
    
    





    // Analyze refinements
    auto refine_start = std::chrono::high_resolution_clock::now();
    auto mem_refine_start = memory_utils::getCurrentMemoryUsage();
    if (use_parallel_analysis_) {
        if (use_transitive_optimization_) {
            std::cout << "Analyzing refinements in parallel with transitive optimization in parallel...\n";
            analyzeRefinementsParallelOptimized();
        } else {
            std::cout << "Analyzing refinements in parallel without transitive optimization...\n";
            analyzeRefinementClassParallel();
        }
    } else {
        std::cout << "Analyzing refinements serially...\n";
        analyzeRefinements();
    }
    auto mem_refine_end = memory_utils::getCurrentMemoryUsage();
    auto refine_end = std::chrono::high_resolution_clock::now();
    result.refinement_time = std::chrono::duration_cast<std::chrono::milliseconds>(refine_end - refine_start);
    result.refinement_memory_kb = mem_refine_end.getResident() - mem_refine_start.getResident();
    // Calculate total refinements
    result.total_refinements = 0;
    for (const auto& graph : refinement_graphs_) {
        result.total_refinements += graph.getEdgeCount();
    }
    
    // Calculate required properties (those with in-degree 0)
    auto required = getRequiredProperties();
    result.required_properties = required.size();
    
    // Apply transitive optimization if enabled (placeholder for now)
    if (use_transitive_optimization_) {
        result.transitive_eliminated = total_skipped_; // Placeholder
    }else{
        result.transitive_eliminated = -1;
    }
    
    result.class_graphs = refinement_graphs_;
    
    auto end_time = std::chrono::high_resolution_clock::now();
    result.total_time = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
    auto mem_final = memory_utils::getCurrentMemoryUsage();
    result.total_analysis_memory_kb = (mem_final.resident_memory_kb > mem_initial.resident_memory_kb)
                                       ? (mem_final.resident_memory_kb - mem_initial.resident_memory_kb)
                                       : 0;
    result.peak_memory_kb = memory_utils::getPeakMemoryUsage();

    return result;
}

void Analyzer::buildEquivalenceClasses() {
    if (properties_.empty()) {
        return;
    }
    
    UnionFind uf;
    
    // Initialize all properties in the union-find structure
    for (size_t i = 0; i < properties_.size(); ++i) {
        uf.find(i); // This ensures the element is tracked
    }
    
    // Build a map from atomic propositions to property indices
    // Properties that share at least one atomic proposition should be in the same class
    std::unordered_map<std::string, std::vector<size_t>> atom_to_properties;
    
    for (size_t i = 0; i < properties_.size(); ++i) {
        //if property in false_properties_index skip it
        bool skip = false;
        for (const auto& index : false_properties_index_) {
            if (i == index) {
                skip = true;
                break;
            }
        }
        if (skip) continue;

        const auto& atoms = properties_[i]->getAtomicPropositions();
        for (const auto& atom : atoms) {
            // Skip numeric literals - they're not meaningful for grouping
            if (atom == "true" || atom == "false" || atom == "1" || atom == "0") {
                continue;
            }
            // Skip if it's a pure number
            try {
                std::stod(atom);
                continue; // It's a number, skip it
            } catch (...) {
                // Not a number, it's a valid atom
            }
            atom_to_properties[atom].push_back(i);
        }
    }
    
    // Unite all properties that share an atomic proposition
    for (const auto& [atom, prop_indices] : atom_to_properties) {
        // Unite all properties that share this atom
        for (size_t i = 1; i < prop_indices.size(); ++i) {
            uf.unite(prop_indices[0], prop_indices[i]);
        }
    }
    
    // Build equivalence classes
    auto classes = uf.getEquivalenceClasses();
    equivalence_classes_.clear();
    equivalence_classes_.reserve(classes.size());
    
    for (const auto& class_indices : classes) {
        std::vector<std::shared_ptr<CTLProperty>> class_properties;
        class_properties.reserve(class_indices.size());
        
        for (size_t idx : class_indices) {
            class_properties.push_back(properties_[idx]);
        }
        
        equivalence_classes_.push_back(std::move(class_properties));
    }
}

void Analyzer::analyzeRefinements() {
    refinement_graphs_.clear();
    refinement_graphs_.reserve(equivalence_classes_.size());
    
    for (size_t i = 0; i < equivalence_classes_.size(); ++i) {
        std::cout << "Analyzing refinement class " << (i + 1) << "/" << equivalence_classes_.size() << "...\n";
        _analyzeRefinementClassSerial(i, use_transitive_optimization_);

    }
}

void Analyzer::_analyzeRefinementClassSerial(size_t class_index, bool use_transitive) {
    const auto& class_properties = equivalence_classes_[class_index];
    
    RefinementGraph graph;
    
    // Add all properties as nodes
    for (const auto& prop : class_properties) {
        graph.addNode(prop);
    }
    
    size_t n = class_properties.size();
    size_t skipped_pairs = 0;
    
    // Check all pairs for refinement
    size_t total_operations = n * (n - 1);
    size_t completed_operations = 0;
    int last_printed_percent = -1;
    
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = 0; j < n; ++j) {
            if (i == j) continue;
            
            // OPTIMIZATION: Skip if already reachable (transitive closure)
            if (use_transitive && graph.hasEdge(i, j)) {
                skipped_pairs++;
                completed_operations++;
                continue;
            }
            
            RefinementResult result = checkRefinement(*class_properties[i], *class_properties[j]);
            result.property1_index = i;
            result.property2_index = j;
            if (result.refines) {
                graph.addEdge(i, j);
                
                // TRANSITIVE CLOSURE: If i->j, then i can reach everything j can reach
                if (use_transitive) {
                    for (size_t k = 0; k < n; ++k) {
                        if (graph.hasEdge(j, k)) {
                            graph.addEdge(i, k);
                        }
                    }
                }
            }
            result_per_property_.push_back(result);
            completed_operations++;
            
            // Update progress bar every 5%
            int current_percent = (completed_operations * 100) / total_operations;
            if (current_percent >= last_printed_percent + 5) {
                last_printed_percent = current_percent;
                printProgressBar(current_percent, class_index + 1, equivalence_classes_.size());
            }
        }
    }
    
    // Print optimization statistics
    if (use_transitive && skipped_pairs > 0) {
        size_t total_pairs = n * (n - 1);
        double skip_ratio = (total_pairs > 0) ? (100.0 * skipped_pairs / total_pairs) : 0.0;
        std::cout << "    [Transitive Closure] Skipped " << skipped_pairs << "/" << total_pairs 
                  << " pairs (" << std::fixed << std::setprecision(1) << skip_ratio << "%)" << std::endl;
        
    }
    total_skipped_ += skipped_pairs;
    
    refinement_graphs_.push_back(std::move(graph));
}

RefinementResult Analyzer::checkRefinement(const CTLProperty& prop1, const CTLProperty& prop2) const {
    auto mem_before = memory_utils::getCurrentMemoryUsage();
    if (!use_ctl_sat_) {
        // Use existing refinement methods
        auto start_time = std::chrono::high_resolution_clock::now();
        bool res= prop1.refines(prop2, use_syntactic_refinement_, use_full_language_inclusion_);
        auto end_time = std::chrono::high_resolution_clock::now();
         auto mem_after = memory_utils::getCurrentMemoryUsage();
        size_t mem_delta = (mem_after.resident_memory_kb > mem_before.resident_memory_kb) 
                          ? (mem_after.resident_memory_kb - mem_before.resident_memory_kb) 
                          : 0;
        return {res, 
                std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time),
                0, 0, mem_delta};
    } else {
        // Use CTL-SAT for refinement checking
        std::cout << "Checking for refinement using CTLSAT";
        auto start_time = std::chrono::high_resolution_clock::now();
        bool res = ctl_sat_interface_->refines(prop1.toString(), prop2.toString());
        auto end_time = std::chrono::high_resolution_clock::now();
        auto mem_after = memory_utils::getCurrentMemoryUsage();
        size_t mem_delta = (mem_after.resident_memory_kb > mem_before.resident_memory_kb)
                          ? (mem_after.resident_memory_kb - mem_before.resident_memory_kb)
                          : 0;
        
        return {res,
                std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time),
                0, 0, mem_delta};
    }
}

void Analyzer::analyzeRefinementClassParallel() {
    auto futures = createAnalysisTasks();
    
    refinement_graphs_.clear();
    refinement_graphs_.resize(equivalence_classes_.size());
    
    // Collect results
    for (size_t i = 0; i < futures.size(); ++i) {
        refinement_graphs_[i] = futures[i].get();
    }
}

void Analyzer::analyzeRefinementsParallelOptimized() {
    refinement_graphs_.clear();
    refinement_graphs_.reserve(equivalence_classes_.size());

    // Run sequentially over classes (inner level already parallel)
    int class_count = 0;
    for (const auto& eq_class : equivalence_classes_) {
        refinement_graphs_.push_back(_analyzeClassTaskOptimized(eq_class));
        std::cout << "Equivalence class analyzed. ("<< ++class_count << "/" << equivalence_classes_.size() << ")\n";
    }
}


//void Analyzer::analyzeRefinementsParallelOptimized() {
//    refinement_graphs_.clear();
//    refinement_graphs_.reserve(equivalence_classes_.size());
//    
//    // Process each class with the optimized task
//    std::vector<std::future<RefinementGraph>> futures;
//    futures.reserve(equivalence_classes_.size());
//    
//    for (size_t i = 0; i < equivalence_classes_.size(); ++i) {
//        futures.push_back(
//            std::async(std::launch::async,
//                      &Analyzer::_analyzeClassTaskOptimized, this,
//                      std::cref(equivalence_classes_[i])));
//    }
//    
//    // Collect results
//    for (auto& future : futures) {
//        refinement_graphs_.push_back(future.get());
//    }
//}

std::vector<std::future<RefinementGraph>> Analyzer::createAnalysisTasks() {
    std::vector<std::future<RefinementGraph>> futures;
    futures.reserve(equivalence_classes_.size());
    
    // Create a thread pool
    size_t num_threads = threads_;
    
    for (size_t i = 0; i < equivalence_classes_.size(); ++i) {
        futures.push_back(
            std::async(std::launch::async, 
                      &Analyzer::_analyzeClassTask, this, 
                      std::cref(equivalence_classes_[i])));
    }
    
    return futures;
}

RefinementGraph Analyzer::_analyzeClassTask(const std::vector<std::shared_ptr<CTLProperty>>& class_properties) {
    RefinementGraph graph;
    
    // Add all properties as nodes
    for (const auto& prop : class_properties) {
        graph.addNode(prop);
    }
    
    // Check all pairs for refinement
    for (size_t i = 0; i < class_properties.size(); ++i) {
        for (size_t j = 0; j < class_properties.size(); ++j) {
            if (i != j) {
                RefinementResult result = checkRefinement(*class_properties[i], *class_properties[j]);
                result.property1_index = i;
                result.property2_index = j;
                if (result.refines) {
                    graph.addEdge(i, j);
                }
                result_per_property_.push_back(result);
            }
        }
    }


    
    return graph;
}

// Optimized version with property-level parallelization and transitive closure
RefinementGraph Analyzer::_analyzeClassTaskOptimized(const std::vector<std::shared_ptr<CTLProperty>>& class_properties) {
    RefinementGraph graph;
    
    // Add all properties as nodes
    for (const auto& prop : class_properties) {
        graph.addNode(prop);
    }
    
    size_t n = class_properties.size();
    if (n <= 1) {
        return graph;
    }

    // Simple reachability array - using std::atomic<bool> for thread safety
    std::unique_ptr<std::atomic<bool>[]> reachability(new std::atomic<bool>[n * n]);
    for (size_t i = 0; i < n * n; ++i) {
        reachability[i].store(false, std::memory_order_relaxed);
    }
    
    // Lambda to access reachability[i][j]
    auto reach = [&](size_t i, size_t j) -> std::atomic<bool>& {
        if (i >= n || j >= n) {
            throw std::out_of_range("reachability index out of range");
        }
        return reachability[i * n + j];
    };
    
    std::atomic<size_t> skipped_pairs(0);
    std::mutex update_mutex;  // Protect transitive closure updates
    std::mutex read_mutex;
    // Process all pairs in parallel - check refinements and update reachability
    std::vector<std::future<std::vector<RefinementResult>>> futures;
    
    std::cout << "    [Refinement Class] Analyzing " << n << " properties with " << threads_ << " threads...\n";
    auto num_threads = threads_;
    for (size_t t = 0; t < num_threads; ++t) {
        futures.push_back(std::async(std::launch::async, [&, t, num_threads]() -> std::vector<RefinementResult> {
            std::vector<RefinementResult> results_per_thread;
            // Each thread handles rows: t, t+threads_, t+2*threads_, ...
            for (size_t i = t; i < n; i += num_threads) {
                for (size_t j = 0; j < n; ++j) {
                    if (i == j) continue;
                    
    
                        if (reach(i, j).load(std::memory_order_acquire)) {
                            skipped_pairs.fetch_add(true, std::memory_order_relaxed);
                            continue;
                        }
                    
                    
                    // Actually test refinement
                    RefinementResult result = checkRefinement(*class_properties[i], *class_properties[j]);
                    result.property1_index = i;
                    result.property2_index = j;
                    results_per_thread.push_back(result);
                    if (result.refines) {
                        // Mark direct reachability
                        reach(i, j).store(1, std::memory_order_release);
                        
                        // TRANSITIVE CLOSURE: If i->j, then i can reach everything j can reach
                        
                            for (size_t k = 0; k < n; ++k) {
                                if (reach(j, k).load(std::memory_order_relaxed)) {
                                    reach(i, k).store(true, std::memory_order_relaxed);
                                }
                            }
                        
                    }
                }
            }
            return results_per_thread;
        }));
    }
    
    // Wait for all threads to complete
    for (auto& future : futures) {
        auto results = future.get();
        result_per_property_.insert(result_per_property_.end(), results.begin(), results.end());
    }
    
    // Print optimization statistics
    if (use_transitive_optimization_) {
        size_t total_pairs = n * (n - 1);
        size_t skipped = skipped_pairs.load();
        if (skipped > 0) {
            double skip_ratio = (total_pairs > 0) ? (100.0 * skipped / total_pairs) : 0.0;
            std::cout << "    [Transitive Closure] Skipped " << skipped << "/" << total_pairs 
                      << " pairs (" << std::fixed << std::setprecision(1) << skip_ratio << "%)" << std::endl;
        }
        total_skipped_ += skipped;
    }
    
    // Now build the graph from the reachability matrix (single-threaded, no race conditions)
    for (size_t i = 0; i < n; ++i) {
        for (size_t j = 0; j < n; ++j) {
            if (reach(i, j).load(std::memory_order_acquire)) {
                graph.addEdge(i, j);
            }
        }
    }
    
    return graph;
}

void Analyzer::writeReport(const std::string& filename, const AnalysisResult& result) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "CTL Refinement Analysis Report\n";
    file << "==============================\n\n";
    file << "Generated on: " << getCurrentTimestamp() << "\n\n";
    
    file << "Summary:\n";
    file << "--------\n";
    file << "Total properties: " << result.total_properties << "\n";
    file << "Equivalence classes: " << result.equivalence_classes << "\n";
    file << "Total refinements found: " << result.total_refinements << "\n";
    file << "Parsing time: " << formatDuration(result.parsing_time) << "\n";
    file << "Equivalence analysis time: " << formatDuration(result.equivalence_time) << "\n";
    file << "Refinement analysis time: " << formatDuration(result.refinement_time) << "\n";
    file << "Total analysis time: " << formatDuration(result.total_time) << "\n\n";
    file << "Refinement Memory Usage: " << result.refinement_memory_kb << " KB\n";
    file << "Total Analysis Memory Usage: " << result.total_analysis_memory_kb << " KB\n";
    file << "Peak Memory Usage: " << result.peak_memory_kb << " KB\n";

    // Write details for each equivalence class
    for (size_t i = 0; i < result.equivalence_class_properties.size(); ++i) {
        const auto& class_props = result.equivalence_class_properties[i];
        const auto& graph = result.class_graphs[i];
        
        file << "Equivalence Class " << (i + 1) << ":\n";
        file << "-------------------\n";
        file << "Properties in this class: " << class_props.size() << "\n";
        file << "Refinement edges: " << graph.getEdgeCount() << "\n";
        file << "Graph density: " << std::fixed << std::setprecision(3) 
             << graph.getDensity() << "\n\n";
        
        file << "Properties:\n";
        for (size_t j = 0; j < class_props.size(); ++j) {
            file << "  " << (j + 1) << ". " << class_props[j]->toString() << "\n";
        }
        file << "\n";
        
        if (!graph.getEdges().empty()) {
            file << "Refinements (⇒ means 'refines'):\n";
            for (const auto& edge : graph.getEdges()) {
                file << "  " << class_props[edge.from]->toString() 
                     << "  ⇒  " << class_props[edge.to]->toString() << "\n";
            }
        } else {
            file << "No non-trivial refinements found in this class.\n";
        }
        
        file << "\n\n";
    }
    
    file.close();
}

void Analyzer::writeGraphs(const std::string& output_directory, const std::string& base_name) const {
    // Create output directory if it doesn't exist
    std::filesystem::create_directories(output_directory);
    
    for (size_t i = 0; i < refinement_graphs_.size(); ++i) {
        std::string filename = output_directory + "/" + base_name + "_" + std::to_string(i + 1) + ".dot";
        std::string title = "Refinement Graph - Class " + std::to_string(i + 1);
        refinement_graphs_[i].toDot(filename, title);
    }
}

std::vector<std::shared_ptr<CTLProperty>> Analyzer::getRequiredProperties() const {
    std::vector<std::shared_ptr<CTLProperty>> required;
    
    for (const auto& graph : refinement_graphs_) {
        // Step 1: Find all strongly connected components (cycles)
        auto sccs = graph.findStronglyConnectedComponents();
        const auto& nodes = graph.getNodes();
        
        if (sccs.empty() || nodes.empty()) {
            continue;
        }
        
        // Step 2: For each SCC, pick one representative (the first node in the SCC)
        std::unordered_map<size_t, size_t> node_to_scc_id;
        std::vector<size_t> scc_representatives;
        
        for (size_t scc_id = 0; scc_id < sccs.size(); ++scc_id) {
            const auto& scc = sccs[scc_id];
            if (!scc.empty()) {
                scc_representatives.push_back(scc[0]);  // Pick first node as representative
                for (size_t node_id : scc) {
                    node_to_scc_id[node_id] = scc_id;
                }
            }
        }
        
        // Step 3: Build condensation graph (SCC graph)
        // For each SCC, find which other SCCs it refines
        std::vector<std::unordered_set<size_t>> condensation_graph(sccs.size());
        const auto& adjacency = graph.getAdjacencyList();
        
        for (size_t node_id = 0; node_id < nodes.size(); ++node_id) {
            size_t from_scc = node_to_scc_id[node_id];
            
            auto adj_it = adjacency.find(node_id);
            if (adj_it != adjacency.end()) {
                for (size_t target_node : adj_it->second) {
                    size_t to_scc = node_to_scc_id[target_node];
                    if (from_scc != to_scc) {  // Only edges between different SCCs
                        condensation_graph[from_scc].insert(to_scc);
                    }
                }
            }
        }
        
        // Step 4: Find SCCs with in-degree 0 in condensation graph
        std::vector<size_t> scc_in_degrees(sccs.size(), 0);
        for (size_t from_scc = 0; from_scc < sccs.size(); ++from_scc) {
            for (size_t to_scc : condensation_graph[from_scc]) {
                scc_in_degrees[to_scc]++;
            }
        }
        
        // Step 5: Add representatives of SCCs with in-degree 0
        for (size_t scc_id = 0; scc_id < sccs.size(); ++scc_id) {
            if (scc_in_degrees[scc_id] == 0 && !sccs[scc_id].empty()) {
                size_t repr_node_id = scc_representatives[scc_id];
                required.push_back(nodes[repr_node_id]);
            }
        }
    }
    
    return required;
}




void Analyzer::updateGraphWithOptimization(RefinementGraph& graph, 
                                          const std::unordered_set<std::string>& eliminated_properties) {
    // Remove eliminated properties from the graph
    
    // Create mapping from formula to index
    std::unordered_map<std::string, size_t> formula_to_index;
    for (size_t i = 0; i < graph.nodes_.size(); ++i) {
        formula_to_index[graph.nodes_[i]->getFormula().toString()] = i;
    }
    
    // Identify indices to remove
    std::vector<size_t> indices_to_remove;
    for (const auto& formula : eliminated_properties) {
        auto it = formula_to_index.find(formula);
        if (it != formula_to_index.end()) {
            indices_to_remove.push_back(it->second);
        }
    }
    
    // Sort in descending order to safely remove
    std::sort(indices_to_remove.rbegin(), indices_to_remove.rend());
    
    // Remove nodes and update adjacency lists
    for (size_t idx : indices_to_remove) {
        // Remove from nodes
        graph.nodes_.erase(graph.nodes_.begin() + idx);
        
        // Remove from adjacency lists
        graph.adjacency_.erase(graph.adjacency_.begin() + idx);
        
        // Update remaining adjacency lists (decrement indices > removed index)
        for (auto& adj_list : graph.adjacency_) {
            adj_list.erase(
                std::remove_if(adj_list.begin(), adj_list.end(),
                              [idx](size_t i) { return i == idx; }),
                adj_list.end()
            );
            
            // Decrement indices greater than removed index
            for (auto& i : adj_list) {
                if (i > idx) {
                    i--;
                }
            }
        }
    }
}

TransitiveOptimizationStats Analyzer::getTransitiveOptimizationStats() const {
    return transitive_stats_;
}


std::unordered_map<std::string, size_t> Analyzer::getStatistics() const {
    std::unordered_map<std::string, size_t> stats;
    
    stats["total_properties"] = properties_.size();
    stats["equivalence_classes"] = equivalence_classes_.size();
    stats["total_refinements"] = 0;
    
    for (const auto& graph : refinement_graphs_) {
        stats["total_refinements"] += graph.getEdgeCount();
    }
    
    auto required = getRequiredProperties();
    stats["required_properties"] = required.size();
    
    return stats;
}

std::string Analyzer::formatDuration(std::chrono::milliseconds duration) const {
    auto ms = duration.count();
    if (ms < 1000) {
        return std::to_string(ms) + "ms";
    } else if (ms < 60000) {
        return std::to_string(ms / 1000.0) + "s";
    } else {
        auto minutes = ms / 60000;
        auto seconds = (ms % 60000) / 1000.0;
        return std::to_string(minutes) + "m " + std::to_string(seconds) + "s";
    }
}

void Analyzer::writeEmptyProperties(const std::string& filename) const {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }

    file << "# False Properties (removed during analysis)\n";
    file << "# Total: " << false_properties_strings_.size() << " properties\n\n";

    for (const auto& prop : false_properties_strings_) {
        file << prop << "\n";
    }

    file.close();

    std::string filename_no_ext = filename.substr(0, filename.find_last_of('.'));
    std::ofstream file_csv(filename_no_ext + ".csv");
    if (!file_csv.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename_no_ext + ".csv");
    }
    file_csv << "Property\n";
    for (auto prop : false_properties_strings_) {
            file_csv << "\"" << prop << "\"\n";
    }
    file_csv.close();
}

void Analyzer::writeRequiredProperties(const std::string& filename) const {
    auto required = getRequiredProperties();
    
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "# Required Properties (not refined by others)\n";
    file << "# Total: " << required.size() << " out of " << properties_.size() << " properties\n\n";
    
    

    for (const auto& prop : required) {
        file << prop->toString() << "\n";
    }

    file << "# Required Properties (by Index)\n";
    file << "# Format: Index: Property. We index from 0, so when loading remember to add 1\n\n";

    for (size_t i = 0; i < properties_.size(); ++i) {
        if (std::find(required.begin(), required.end(), properties_[i]) != required.end()) {
            file << i << ": " << properties_[i]->toString() << "\n";
        }
    }

    file.close();
    //remove .txt from filename
    std::string filename_no_ext = filename.substr(0, filename.find_last_of('.'));
    std::ofstream file_csv(filename_no_ext + ".csv");
    if (!file_csv.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename_no_ext + ".csv");
    }
    file_csv << "Index,Property\n";
    for (size_t i = 0; i < properties_.size(); ++i) {
        if (std::find(required.begin(), required.end(), properties_[i]) != required.end()) {
            file_csv << i << ",\"" << properties_[i]->toString() << "\"\n";
        }
    }
    file_csv.close();
}

std::string Analyzer::getCurrentTimestamp() const {
    auto now = std::chrono::system_clock::now();
    auto time_t = std::chrono::system_clock::to_time_t(now);
    std::stringstream ss;
    ss << std::put_time(std::localtime(&time_t), "%Y-%m-%d %H:%M:%S");
    return ss.str();
}

void Analyzer::printProgressBar(int percent, size_t current_class, size_t total_classes) const {
    // Get terminal width (default to 80 if can't determine)
    int terminal_width = 80;
    #ifdef __unix__
    struct winsize w;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &w) == 0) {
        terminal_width = w.ws_col;
    }
    #endif
    
    // Format prefix with class info
    std::ostringstream prefix_stream;
    prefix_stream << "    [Class " << current_class << "/" << total_classes << "] ";
    std::string prefix = prefix_stream.str();
    
    // Format suffix with percentage
    std::ostringstream suffix_stream;
    suffix_stream << " " << std::setw(3) << percent << "%";
    std::string suffix = suffix_stream.str();
    
    // Calculate available space for the progress bar
    int available_width = terminal_width - prefix.length() - suffix.length() - 2; // -2 for brackets
    if (available_width < 10) available_width = 10; // Minimum bar width
    
    // Calculate filled and empty portions
    int filled = (percent * available_width) / 100;
    int empty = available_width - filled;
    
    // Build the progress bar
    std::ostringstream bar_stream;
    bar_stream << prefix << "[";
    for (int i = 0; i < filled; ++i) bar_stream << "=";
    for (int i = 0; i < empty; ++i) bar_stream << " ";
    bar_stream << "]" << suffix;
    
    // Print with carriage return to overwrite previous line
    std::cout << "\r" << bar_stream.str() << std::flush;
    
    // Add newline when complete
    if (percent >= 100) {
        std::cout << std::endl;
    }
}

std::vector<size_t> RefinementGraph::getInDegrees() const {
    std::vector<size_t> in_degrees(nodes_.size(), 0);
    for (const auto& edge : edges_) {
        in_degrees[edge.to]++;
    }
    return in_degrees;
}

std::vector<size_t> RefinementGraph::getOutDegrees() const {
    std::vector<size_t> out_degrees(nodes_.size(), 0);
    for (const auto& edge : edges_) {
        out_degrees[edge.from]++;
    }
    return out_degrees;
}

// Utility functions
namespace analyzer_utils {


void exportToCSV(const Analyzer::AnalysisResult& result, const std::string& filename) {
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }
    
    file << "class_id,property_index,property,refines_property_index,refines_property\n";
    
    for (size_t class_id = 0; class_id < result.class_graphs.size(); ++class_id) {
        const auto& graph = result.class_graphs[class_id];
        const auto& properties = result.equivalence_class_properties[class_id];
        
        for (const auto& edge : graph.getEdges()) {
            file << class_id << ","
                 << edge.from << ","
                 << "\"" << properties[edge.from]->toString() << "\","
                 << edge.to << ","
                 << "\"" << properties[edge.to]->toString() << "\"\n";
        }
    }
    
    file.close();
}

std::unordered_map<std::string, double> computeGraphStatistics(const RefinementGraph& graph) {
    std::unordered_map<std::string, double> stats;
    
    stats["nodes"] = static_cast<double>(graph.getNodeCount());
    stats["edges"] = static_cast<double>(graph.getEdgeCount());
    stats["density"] = graph.getDensity();
    
    auto in_degrees = graph.getInDegrees();
    auto out_degrees = graph.getOutDegrees();
    
    if (!in_degrees.empty()) {
        double avg_in = std::accumulate(in_degrees.begin(), in_degrees.end(), 0.0) / in_degrees.size();
        double avg_out = std::accumulate(out_degrees.begin(), out_degrees.end(), 0.0) / out_degrees.size();
        
        stats["avg_in_degree"] = avg_in;
        stats["avg_out_degree"] = avg_out;
        stats["max_in_degree"] = static_cast<double>(*std::max_element(in_degrees.begin(), in_degrees.end()));
        stats["max_out_degree"] = static_cast<double>(*std::max_element(out_degrees.begin(), out_degrees.end()));
    }
    
    return stats;
}




} // namespace analyzer_utils

void Analyzer::setUseTransitiveOptimization(bool use_transitive) {
    use_transitive_optimization_ = use_transitive;
}

void Analyzer:: writeInfoPerProperty(const std::string& filename) const
{
    std::ofstream file(filename);
    if (!file.is_open()) {
        throw std::runtime_error("Cannot open file for writing: " + filename);
    }

    file << "Index 1, Index 2, Property 1, Property 2, Time Taken (ms),Memory Used (KB)\n";
    for (const auto& result : result_per_property_) {

        //find property names
        std::string property1_name = "";
        std::string property2_name = "";
        if(result.property1_index < properties_.size()) {
            property1_name = properties_[result.property1_index]->toString();
        }
        if(result.property2_index < properties_.size()) {
            property2_name = properties_[result.property2_index]->toString();
        }


        file << result.property1_index << "," << result.property2_index << ","
             << "\"" << property1_name << "\","
             << "\"" << property2_name << "\","
             << result.time_taken.count() << ","
             << result.memory_used_kb << "\n";
    }

    file.close();
}

} // namespace ctl




//nohup ./check_refinements ./assets/benchmark/Dataset/Properties/2018 --use-full-language-inclusion --verbose -o output_2018_p --parallel -j 6  > output.log 2>&1 &
//CloudDeployment-PT-6b.txt