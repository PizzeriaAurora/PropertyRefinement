echo "Setting up the environment..."
echo "This may take a while depending on your internet connection and system performance."
echo "Sudo is needed for installing system packages as well as lola system wide."

sudo apt-get update && sudo apt-get install -y \
    python3 \
    python3-pip \
    python3-venv \
    cmake \
    bison \
    curl \
    p7zip-full \
    tar \
    libssl-dev \
    git \
    build-essential \
    automake

python3 -m venv venv
source venv/bin/activate
pip install psutil tqdm pandas matplotlib seaborn pyyaml

cd assets/benchmark || exit

mkdir extern

# Install extfstools, if the folder doesn't already exist 
if [ ! -d "./extern/extfstools" ]; then
    git clone https://github.com/nlitsme/extfstools
    mv ./extfstools ./extern/extfstools
    cd ./extern/extfstools
    make

    cp ./build/ext2rd /usr/local/bin/
    chmod +x /usr/local/bin/ext2rd
    cd ../..
else
    echo "extfstools already exists, skipping clone and build."
fi



if [ ! -d "./extern/pompet" ]; then
    git clone https://depot.lipn.univ-paris13.fr/evangelista/pompet
    mv ./pompet ./extern/pompet
   
else
    echo "pompet already exists, skipping clone and install."
fi

cd ./extern/pompet
pip install .
cd ../..

if  [ ! -d "extern/lola-2.0" ]; then
    curl -o lola-2.0.tar.gz https://theo.informatik.uni-rostock.de/storages/uni-rostock/Alle_IEF/Inf_THEO/images/tools_daten/lola-2.0.tar.gz
    tar -xvzf lola-2.0.tar.gz
    mv ./lola-2.0 ./extern/lola-2.0
    #apply patch to lola-2.0
    cp ./patches/generalized.c ./extern/lola-2.0/src/Formula/LTL/
    #cp ./patches/Makefile.am ./extern/lola-2.0/
    echo "Applying patches to lola-2.0"
    cd extern/lola-2.0
    ./configure
    make
    sudo make install
    cd ../..
    rm lola-2.0.tar.gz
else
    echo "lola-2.0 already exists, skipping download and install."
fi


#if argument is full, then download the dataset
if [ "$1" == "full" ]; then
    echo "Downloading the full dataset. This may take a while."
    sudo chmod +x get_dataset.sh
    ./get_dataset.sh
else
    echo "Skipping dataset download."
fi

