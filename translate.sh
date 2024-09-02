#!/bin/bash

if [ $# != 4 ]; then
    echo "[ERROR] Please provide the correct number of arguments."
    exit 1
fi

template=$1
source=$2
source_name="${source%.*}"
target=$3
target_name="${target%.*}"
output=$4

if [ $template != "morphism" ] && [ $template != "relation" ] && [ $template != "embedding" ]; then
    echo "[ERROR] The first argument should be morphism, relation or embedding."
    exit 1
fi

if [ ${source##*.} != "dk" ]; then
    echo "[ERROR] The source file provided is not a Dedukti file."
    exit 1
fi

if [ ${target##*.} != "dk" ]; then
    echo "[ERROR] The target file provided is not a Dedukti file."
    exit 1
fi

if [ ${output##*.} != "dk" ]; then
    echo "[ERROR] The output file provided is not a Dedukti file."
    exit 1
fi

dune build

dune exec -- translation --template $template --source $source_name --target $target_name > $output
sed -i 's/module_to_erase.//g' $output
sed -i 's/module_todo.//g' $output