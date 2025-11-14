#pragma once
#include <z3++.h>
#include <vector>
#include <memory>
#include <mutex>
struct Z3SolverPool {
        std::vector<std::unique_ptr<z3::solver>> solvers;
        std::vector<bool> in_use;
        std::mutex pool_mutex;
        z3::context* ctx;
        
        Z3SolverPool(z3::context* context, size_t pool_size = 8) : ctx(context) {
            solvers.reserve(pool_size);
            in_use.resize(pool_size, false);
            for (size_t i = 0; i < pool_size; ++i) {
                solvers.push_back(std::make_unique<z3::solver>(*ctx));
            }
        }
        
        // Acquire a solver from the pool
        std::pair<z3::solver*, size_t> acquire() {
            std::lock_guard<std::mutex> lock(pool_mutex);
            for (size_t i = 0; i < solvers.size(); ++i) {
                if (!in_use[i]) {
                    in_use[i] = true;
                    return {solvers[i].get(), i};
                }
            }
            std::cout << "Warning: Z3 Solver Pool exhausted, creating new solver." << std::endl;
            // Pool exhausted - create new solver
            size_t idx = solvers.size();
            solvers.push_back(std::make_unique<z3::solver>(*ctx));
            in_use.push_back(true);
            return {solvers[idx].get(), idx};
        }
        
        // Release solver back to pool
        void release(size_t idx) {
            std::lock_guard<std::mutex> lock(pool_mutex);
            if (idx < in_use.size()) {
                in_use[idx] = false;
            }
        }
    };