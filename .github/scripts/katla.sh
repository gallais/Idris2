#!/bin/sh

prefix="../../libs"

for rawfile in $(find ${prefix} -name "*.idr"); do
    file=$(echo $rawfile | sed "s|\.\./\.\./libs/\(.*\)|\1|");
    libname=$(echo $file | sed "s|\([^/]*\)/.*|\1|");
    filename=$(echo $file | sed "s|[^/]*/\(.*\)\.idr|\1|");
    directories=$(echo $file | sed "s|\(.*\)/[^/]*\.idr|\1|");
    mkdir -p "html/${directories}";
    katla html $rawfile "${prefix}/${libname}/build/ttc/${filename}.ttm" > "html/${libname}/${filename}.html";
done
