#!/bin/bash
set -e
set -x
source ../../venv/bin/activate
mkdir -p Dataset_raw

#get as input the year range, default 2021-2024
start_year=${1:-2023}
end_year=${2:-2024}

for year in $(seq "$start_year" "$end_year"); do
    year_folder="Dataset_raw/$year"
    if [ -d "$year_folder" ]; then
        echo "Folder $year_folder already exists, skipping..."
        continue
    fi

    echo "=== Processing year $year ==="
    mkdir -p "$year_folder"
    cd "$year_folder" || exit
    pwd
    case "$year" in
        2018)
            url="http://mcc.lip6.fr/2018/archives/mcc2018-input.vmdk.tar.bz2"
            ;;
        2019)
            url="http://mcc.lip6.fr/2019/archives/mcc2019-input.vmdk.tar.bz2"
            ;;
        2020)
            url="http://mcc.lip6.fr/2020/archives/mcc2020-input.vmdk.tar.bz2"
            ;;
        2021)
            url="http://mcc.lip6.fr/2021/archives/mcc2021-input.vmdk.tar.bz2"
            ;;
        *)
            url="https://mcc.lip6.fr/${year}/archives/mcc${year}-input.tar.gz"
            ;;
    esac

    echo "Downloading $url"
    curl -L -O "$url"

    # Extract based on file type
    filename="${url##*/}"
    if [[ "$filename" == *.tar.gz ]]; then
        tar xzf "$filename"
    elif [[ "$filename" == *.tar.bz2 ]]; then
        tar xjf "$filename"
    fi


    rm -f "$filename"

    # Extract VMDK if exists
    if [ -f "mcc${year}-input.vmdk" ]; then
        7z e "mcc${year}-input.vmdk" || echo "7z extraction failed for $year"
        if [ -f "0.img" ]; then
            echo "Found 0.img, extraction requires ext2rd or Linux tools."
            mkdir INPUTS
            ext2rd "0.img" ./:INPUTS || echo "ext2rd extraction failed for $year"
            rm -f 0.img
            rm 1 || echo "No 1 file to remove"
            mv INPUTS/* ./
            rmdir INPUTS
        fi
        rm -f "mcc${year}-input.vmdk"
    fi

    # Patch tgz archives in INPUTS
    if [ -d "INPUTS" ]; then
        cd INPUTS
        for i in *.tgz; do
            [ -f "$i" ] || continue
            tar xzf "$i"
            model="${i%.tgz}"
            rm "$i"
            tar czf "$i" "$model"/
            rm -rf "$model"/
        done
        cd ..
    fi

    cd ../..
done

echo "=== Dataset setup complete! ==="
python3 dataset_scripts/prepare_dataset.py


