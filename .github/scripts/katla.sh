#!/bin/sh

prefix="../../libs"

find "$prefix" -name "*.idr" > tmp
while IFS= read -r rawfile
do
    file=$(echo "$rawfile" | sed "s|\.\./\.\./libs/\(.*\)|\1|")
    libname=$(echo "$file" | sed "s|\([^/]*\)/.*|\1|")
    filename=$(echo "$file" | sed "s|[^/]*/\(.*\)\.idr|\1|")
    directories=$(echo "$file" | sed "s|[^/]*/\(.*\)/[^/]*\.idr|\1|")
    mkdir -p "html/${libname}/source/${directories}"
    katla html "$rawfile" "${prefix}/${libname}/build/ttc/${filename}.ttm" > "html/${libname}/source/${filename}.html"
done < tmp
# rm tmp
