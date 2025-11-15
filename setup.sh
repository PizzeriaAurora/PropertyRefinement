sudo apt update
sudo apt install build-essential cmake libz3-dev libstdc++6




# if not already present, clone CTL sat and build it
if [ ! -d "assets/extern/CTLSAT" ]; then
    # create extern directory if it does not exist
    mkdir -p assets/extern/
    cd assets/extern/
    git clone https://github.com/nicolaprezza/CTLSAT.git
    cd CTLSAT || { echo "Failed to enter CTLSAT directory."; exit 1; }
    make clean
    make
    cp ctl-sat ../ctl-sat
    cd ../../..
fi
#
#
#if [ ! -d "assets/extern/cvc5" ]; then
#    cd assets/extern/
#    git clone https://github.com/cvc5/cvc5.git
#    cd cvc5 || { echo "Failed to enter cvc5 directory."; exit 1; }
#    ./configure.sh --prefix=/usr/local --auto-download
#    cd build
#    make -j$(nproc)
#    sudo make install
#fi

#nohup ./check_refinements ./assets/benchmark/Dataset/Properties/2024 --use-full-language-inclusion --verbose -o results/language_inclusion_RCTLC_s/2024 --no-parallel > logs/2024_language


#nohup ./check_refinements ./assets/benchmark/Dataset/Properties/2018 --use-full-language-inclusion --verbose -o test/2018 --no-parallel > logs/2018_test 2>&1 &


#nohup ./check_refinements ./assets/benchmark/Dataset_lite/ParallelRers2019Ctl --use-full-language-inclusion --verbose -o results/ParallelRers2019Ctl/ --no-parallel > logs/ParallelRers2019Ctl_language 
#nohup ./ctl_refine_tool ../../assets/benchmark/Dataset/Properties/2018  --use-full-language-inclusion --verbose -o ./test --no-parallel > ./test.log 2>&1 &

cd RefinementAnalysisTool


mkdir build || { echo "Failed to create build directory. Probably because it exists"; }
cd build || { echo "Failed to create or enter build directory."; exit 1; }
cmake ..
make -j$(nproc)
cp ./ctl_refine_tool ../../check_refinements
cp ./collect_formula_info ../../scripts/collect_formula_info
cd ../..


# to run benchmarks, needs to be set up
# if input is full, then it will also download the dataset
if [ "$1" == "full" ]; then
    bash ./setup_benchmarks.sh
fi
