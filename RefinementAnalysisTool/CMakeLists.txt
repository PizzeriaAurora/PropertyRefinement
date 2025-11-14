cmake_minimum_required(VERSION 3.16)
project(RefinementBasedCTLReduction VERSION 1.0.0 LANGUAGES CXX)

# Set C++ standard
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Set optimization flags
set(CMAKE_CXX_FLAGS_RELEASE "-O3 -DNDEBUG -march=native")

# Set default build type to Release if not specified
set(CMAKE_BUILD_TYPE Release)

# Option to choose SMT solver (default: CVC5)
set(SMT_SOLVER "Z3" CACHE STRING "Choose SMT solver: Z3 or CVC5")
set_property(CACHE SMT_SOLVER PROPERTY STRINGS "Z3" "CVC5")

# Option to use on-the-fly product construction for emptiness checking
option(USE_ON_THE_FLY_PRODUCT "Use on-the-fly product construction for language inclusion" OFF)

# Find required packages
find_package(PkgConfig REQUIRED)

# SMT Solver configuration
if(SMT_SOLVER STREQUAL "CVC5")
    message(STATUS "Using CVC5 as SMT solver")
    
    # Find CVC5
    find_package(cvc5 QUIET)
    if(NOT cvc5_FOUND)
        pkg_check_modules(CVC5 REQUIRED cvc5)
        set(SMT_INCLUDE_DIRS ${CVC5_INCLUDE_DIRS})
        set(SMT_LIBRARIES ${CVC5_LIBRARIES})
        set(SMT_CFLAGS_OTHER ${CVC5_CFLAGS_OTHER})
    else()
        set(SMT_INCLUDE_DIRS "")
        set(SMT_LIBRARIES cvc5::cvc5)
        set(SMT_CFLAGS_OTHER "")
    endif()
    
    add_compile_definitions(USE_CVC5)
    
elseif(SMT_SOLVER STREQUAL "Z3")
    message(STATUS "Using Z3 as SMT solver")
    
    # Find Z3
    find_package(Z3 QUIET)
    if(NOT Z3_FOUND)
        pkg_check_modules(Z3 REQUIRED z3)
        set(SMT_INCLUDE_DIRS ${Z3_INCLUDE_DIRS})
        set(SMT_LIBRARIES ${Z3_LIBRARIES})
        set(SMT_CFLAGS_OTHER ${Z3_CFLAGS_OTHER})
    else()
        set(SMT_INCLUDE_DIRS ${Z3_INCLUDE_DIRS})
        set(SMT_LIBRARIES ${Z3_LIBRARIES})
        set(SMT_CFLAGS_OTHER "")
    endif()
    
    add_compile_definitions(USE_Z3)
    
else()
    message(FATAL_ERROR "Invalid SMT_SOLVER: ${SMT_SOLVER}. Choose Z3 or CVC5.")
endif()

# Include directories
include_directories(include)
include_directories(${SMT_INCLUDE_DIRS})

# Configure emptiness checking implementation
if(USE_ON_THE_FLY_PRODUCT)
    message(STATUS "Using ON-THE-FLY product construction for emptiness")
    add_compile_definitions(USE_ON_THE_FLY_PRODUCT)
    # Use the OTF implementation
    file(GLOB_RECURSE EMPTINESS_SOURCES "src/CTLautomatonImplementations/CTLAutomatonEmptinessOF.cpp")
else()
    message(STATUS "Using STANDARD fixpoint emptiness checking")
    # Use the standard implementation
    file(GLOB_RECURSE EMPTINESS_SOURCES "src/CTLautomatonImplementations/CTLAutomatonEmptiness.cpp")
endif()

# Create the main library
file(GLOB_RECURSE SOURCES "src/*.cpp")
# Add all CTLautomatonImplementations except emptiness files
file(GLOB_RECURSE CTL_IMPL_SOURCES "src/CTLautomatonImplementations/*.cpp")
list(REMOVE_ITEM CTL_IMPL_SOURCES 
    "${CMAKE_CURRENT_SOURCE_DIR}/src/CTLautomatonImplementations/CTLAutomatonEmptiness.cpp"
    "${CMAKE_CURRENT_SOURCE_DIR}/src/CTLautomatonImplementations/CTLAutomatonEmptinessOF.cpp")

add_library(ctl_refine_lib ${SOURCES} ${CTL_IMPL_SOURCES} ${EMPTINESS_SOURCES})

# Link libraries
target_link_libraries(ctl_refine_lib ${SMT_LIBRARIES})

# Add compile options
target_compile_options(ctl_refine_lib PRIVATE ${SMT_CFLAGS_OTHER})

# Create the main executable
add_executable(ctl_refine_tool main.cpp)
target_link_libraries(ctl_refine_tool ctl_refine_lib)



# Enable testing
enable_testing()

# Find GTest
find_package(GTest QUIET)
if(NOT GTest_FOUND)
    # Download and build GoogleTest
    include(FetchContent)
    FetchContent_Declare(
        googletest
        URL https://github.com/google/googletest/archive/release-1.12.1.zip
    )
    # For Windows: Prevent overriding the parent project's compiler/linker settings
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)
endif()

# Add test executable for CTLSAT parser
add_executable(test_ctlsat_parser tests/test_ctlsat_parser.cpp)
target_link_libraries(test_ctlsat_parser ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME ctlsat_parser_tests COMMAND test_ctlsat_parser)

add_executable(test_abta tests/test_abta.cpp)
target_link_libraries(test_abta ctl_refine_lib)
add_test(NAME test_abta COMMAND test_abta)


add_executable(test_language_inclusion tests/test_language_inclusion.cpp)
target_link_libraries(test_language_inclusion ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME test_language_inclusion COMMAND test_language_inclusion)




add_executable(test_simulation tests/test_simulation.cpp)
target_link_libraries(test_simulation ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME test_simulation COMMAND test_simulation)


add_executable(simple_test_simulation tests/simple_test_simulation.cpp)
target_link_libraries(simple_test_simulation ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME simple_test_simulation COMMAND simple_test_simulation)



add_executable(test_z3_simple tests/test_z3_simple.cpp)
target_link_libraries(test_z3_simple ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME test_z3_simple COMMAND test_z3_simple)


add_executable(test_atom_collector tests/test_atom_collector.cpp)
target_link_libraries(test_atom_collector ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME test_atom_collector COMMAND test_atom_collector)


add_executable(test_ctl_sat tests/test_ctl_sat.cpp)
target_link_libraries(test_ctl_sat ctl_refine_lib GTest::gtest GTest::gtest_main)
add_test(NAME test_ctl_sat COMMAND test_ctl_sat)



## Add other test executables
#file(GLOB_RECURSE OTHER_TEST_SOURCES "tests/*.cpp")
#if(OTHER_TEST_SOURCES)
#    add_executable(ctl_tests ${OTHER_TEST_SOURCES}  GTest::gtest GTest::gtest_main)
#    target_link_libraries(ctl_tests ctl_refine_lib)
#    add_test(NAME ctl_unit_tests COMMAND ctl_tests)
#endif()



add_executable(collect_formula_info collect_formula_info.cpp)
target_link_libraries(collect_formula_info ctl_refine_lib)




# Installation
install(TARGETS ctl_refine_tool DESTINATION bin)
install(TARGETS ctl_refine_lib DESTINATION lib)
install(DIRECTORY include/ DESTINATION include)