#!/bin/sh

prefix="../../libs"

find "$prefix" -name "*.idr" >tmp
while IFS= read -r rawfile; do
    file=$(echo "$rawfile" | sed "s|\.\./\.\./libs/\(.*\)|\1|")
    libname=$(echo "$file" | sed "s|\([^/]*\)/.*|\1|")
    filename=$(echo "$file" | sed "s|[^/]*/\(.*\)\.idr|\1|")
    htmlfile=$(echo "$filename" | sed "s|/|.|g")
    directories=$(echo "$file" | sed "s|[^/]*/\(.*\)/[^/]*\.idr|\1|")
    mkdir -p "html/${libname}/source/"
    katla html "$rawfile" "${prefix}/${libname}/build/ttc/${filename}.ttm" >"html/${libname}/source/${htmlfile}.html"
done <tmp
rm tmp
