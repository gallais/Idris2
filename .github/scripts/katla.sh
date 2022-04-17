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
    sed -i "s|<head>|<head><title>${modulename}</title>|" "$htmlfile"
done <tmp
rm tmp

for libname in "$prefix"/*; do
    cp -r "$prefix"/"$libname"/build/docs/* html/"$libname"
    find html/"$libname"/docs/ -name "*.html" >tmp
    while IFS=read -r rawfile; do
        file=$(echo "$rawfile" | sed "s|/docs/\(.*\)|\1|")
        filename=$(basename "$file" ".html")
        sed -i "s|<h1>${filename}</h1>|<h1><a href=\"../source/${filename}.html\">${filename}</a></h1>" "$file"
    done <tmp
    rm tmp
done
