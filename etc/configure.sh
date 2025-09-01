#!/usr/bin/env bash

set -e

if [ $# -ne 1 ]; then
  echo "Usage: $0 <directory>"
  exit 1
fi

dirpath="$1"
theory=$(basename "$dirpath")
output="$dirpath/dune.inc"

prelude='; this only provides an alias to build all *.vo files
(rule
 (alias vo_files)
 (deps (glob_files *.vo))
 (action (echo "Generated *.vo files\\n")))'

# Template for .v files
template_v='(subdir %s.v.d
  (rule
    (action
      (write-file %s_extr.v "Require Coq.extraction.Extraction %s.%s. Extraction \\"%s.ml\\" %s.prog.")))
  (coq.extraction
    (prelude %s_extr)
    (extracted_modules %s)
    (theories Ltac2 Koika %s)
    (flags "-w" "-overriding-logical-loadpath"))
  (rule
    (alias compile)
    (deps (:ml %s.ml) (:mli %s.mli))
    (targets
      %s.kpkg %s.cpp
      %s.hpp %s.verilator.cpp
      %s.v %s.dot
      cuttlesim.hpp verilator.hpp
      Makefile)
    (action
      (run cuttlec %%\173ml\175 -T all -o .))))'

template_lv='(subdir %s.lv.d
  (rule
    (alias compile)
    (deps ../%s.lv)
    (targets
      %s_coq.v %s.cpp
      %s.hpp %s.verilator.cpp
      %s.v %s.dot
      cuttlesim.hpp verilator.hpp
      Makefile)
    (action
      (run cuttlec %%\173deps\175 -T all -o .))))'

template_lv_errors='(subdir %s.lv.d
  (rule
    (alias compile)
    (deps ../%s.lv)
    (targets )
    (action
      (ignore-stderr (run cuttlec %%\173deps\175 -T all -o . --expect-errors)))))'

# Truncate or create dune.inc
: > "$output"
printf "creating $output\n"

# start with general rules
printf "$prelude\n" >> "$output"

# Loop over *.v files in the directory
shopt -s nullglob
for filepath in "$dirpath"/*.v; do
  module=$(basename "$filepath" .v)
  printf "\n$template_v\n" "$module" "$module" "$theory" "$module" "$module" "$module" "$module" "$module" "$theory" "$module" "$module" "$module" "$module" "$module" "$module" "$module" "$module" >> "$output"
done
# Loop over *.lv files in the directory
for filepath in "$dirpath"/*.lv; do
  module=$(basename "$filepath" .lv)

  if [[ "$module" == *.1 ]]; then
    printf "\n$template_lv_errors\n" "$module" "$module" >> "$output"
  else
    printf "\n$template_lv\n" "$module" "$module" "$module" "$module" "$module" "$module" "$module" "$module" >> "$output"
  fi
done