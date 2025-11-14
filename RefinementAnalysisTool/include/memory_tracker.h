#ifndef MEMORY_UTILS_H
#define MEMORY_UTILS_H

#include <cstddef>
#include <string>

#ifdef __linux__
#include <fstream>
#include <unistd.h>
#elif defined(_WIN32)
#include <windows.h>
#include <psapi.h>
#endif

namespace ctl {
namespace memory_utils {

struct MemorySnapshot {
    size_t resident_memory_kb;  // Physical memory (RSS)
    size_t virtual_memory_kb;   // Virtual memory (VSZ)
    
    size_t getResidentMB() const { return resident_memory_kb / 1024; }
    size_t getVirtualMB() const { return virtual_memory_kb / 1024; }
    size_t getResident() const { return resident_memory_kb; }
    size_t getVirtual() const { return virtual_memory_kb; }
};

inline MemorySnapshot getCurrentMemoryUsage() {
    MemorySnapshot snapshot{0, 0};
    
#ifdef __linux__
    // Read from /proc/self/status for accurate memory info
    std::ifstream status("/proc/self/status");
    std::string line;
    
    while (std::getline(status, line)) {
        if (line.substr(0, 6) == "VmRSS:") {
            sscanf(line.c_str(), "VmRSS: %zu", &snapshot.resident_memory_kb);
        } else if (line.substr(0, 7) == "VmSize:") {
            sscanf(line.c_str(), "VmSize: %zu", &snapshot.virtual_memory_kb);
        }
    }
    
#elif defined(_WIN32)
    PROCESS_MEMORY_COUNTERS_EX pmc;
    if (GetProcessMemoryInfo(GetCurrentProcess(), (PROCESS_MEMORY_COUNTERS*)&pmc, sizeof(pmc))) {
        snapshot.resident_memory_kb = pmc.WorkingSetSize / 1024;
        snapshot.virtual_memory_kb = pmc.PrivateUsage / 1024;
    }
#endif
    
    return snapshot;
}

inline size_t getPeakMemoryUsage() {
#ifdef __linux__
    std::ifstream status("/proc/self/status");
    std::string line;
    size_t peak_kb = 0;
    
    while (std::getline(status, line)) {
        if (line.substr(0, 6) == "VmPeak:") {
            sscanf(line.c_str(), "VmPeak: %zu", &peak_kb);
            return peak_kb;
        }
    }
    
#elif defined(_WIN32)
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc))) {
        return pmc.PeakWorkingSetSize / 1024;
    }
#endif
    
    return 0;
}

} // namespace memory_utils
} // namespace ctl

#endif // MEMORY_UTILS_H