
#include "analyzer.h"
#include <string>
#include <chrono>
#include <string>
#include <iostream>

void test(ctl::Analyzer& analyzer, std::string test_name) {
    // Run analysis
    auto result = analyzer.analyze();
    // Output results
    std::cout << "Analysis completed (" << test_name << ") in " << std::to_string(result.refinement_time.count()) << "ms . Required properties : " << result.required_properties << "\n";
}

int main(int argc, char* argv[]) {
    try {


        // Parse command line arguments for ctl_sat path: Defualt: ./extern/ctl-sat
        std::string ctl_sat_path = "../assets/extern/ctl-sat";
        for (int i = 1; i < argc; ++i) {
            std::string arg = argv[i];
            if (arg == "--ctl-sat-path") {
                if (i + 1 < argc) {
                    ctl_sat_path = argv[++i];
                } else {
                    std::cerr << "Error: --ctl-sat-path option requires an argument\n";
                    return 1;
                }
            }
        }

{
    
        std::string input_file = "/home/luca/Documents/CTL_TOOL/RefinementBasedCTLReduction/assets/tests/complex_test.txt";
        std::string output_dir = "test_dir";

        // Initialize analyzer
        auto analyzer = ctl::Analyzer::fromFile(input_file);
        analyzer.setUseCTLSAT(true);
        analyzer.createCTLSATInterface(ctl_sat_path);
        analyzer.setParallelAnalysis(true);
        analyzer.getCTLSATInterface()->setVerbose(true);
        

        // Run analysis
        test(analyzer, "CTL-SAT based refinement checking");
        
        //auto analyzer3 = ctl::Analyzer::fromFile(input_file);
        //analyzer3.setUseCTLSAT(false);
        //analyzer3.setParallelAnalysis(false);
        //analyzer3.setSyntacticRefinement(false);
        //analyzer3.setUseTransitiveOptimization(true);
        //analyzer3.setFullLanguageInclusion(true);
        //auto result3 = analyzer3.analyze();
//
        //test(analyzer3, "Language inclusion refinement checking");

        /*
        input_file = "/home/luca/Documents/CTL_TOOL/RefinementBasedCTLReduction/assets/benchmark/Dataset_lite/ParallelRers2019Ctl/problem101-ctl-properties.txt";
        output_dir = "RERS_test_dir";


        auto analyzer4 = ctl::Analyzer::fromFile(input_file);
        analyzer4.setUseCTLSAT(true);
        analyzer4.createCTLSATInterface(ctl_sat_path);
        analyzer4.setParallelAnalysis(false);
        analyzer4.getCTLSATInterface()->setVerbose(false);

        test(analyzer4, "RERS CTL-SAT based refinement checking");


        auto analyzer5 = ctl::Analyzer::fromFile(input_file);
        analyzer5.setUseCTLSAT(false);
        analyzer5.setParallelAnalysis(true);
        analyzer5.setSyntacticRefinement(false);
        analyzer5.setUseTransitiveOptimization(true);
        analyzer5.setFullLanguageInclusion(true);

        test(analyzer5, "RERS Language inclusion refinement checking");


        auto analyzer6 = ctl::Analyzer::fromFile(input_file);
        analyzer6.setUseCTLSAT(false);
        analyzer6.setParallelAnalysis(true);
        analyzer6.setSyntacticRefinement(false);
        analyzer6.setUseTransitiveOptimization(true);
        analyzer6.setFullLanguageInclusion(false);

        test(analyzer6, "RERS Simulation refinement checking");
*/
    }







        return 0;
        
    } catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << "\n";
        return 1;
    }
}