#!/bin/sh

prefix="../../libs"

find "$prefix" -name "*.idr" >tmp
while IFS= read -r rawfile; do
    file=$(echo "$rawfile" | sed "s|\.\./\.\./libs/\(.*\)|\1|")
    libname=$(echo "$file" | sed "s|\([^/]*\)/.*|\1|")
    filename=$(echo "$file" | sed "s|[^/]*/\(.*\)\.idr|\1|")
    modulename=$(echo "$filename" | sed "s|/|.|g")
    htmldir="html/${libname}/docs/source/"
    htmlfile="${htmldir}/${modulename}.html"
    mkdir -p "$htmldir"
    katla html "$rawfile" "${prefix}/${libname}/build/ttc/${filename}.ttm" >"$htmlfile"
done <tmp
rm tmp
