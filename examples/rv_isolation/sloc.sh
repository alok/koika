#! /bin/sh

echo "CLOC cuttlesim"
cloc _objects/rv32i.v/rv32.hpp

echo "CLOC verilator"
cloc _objects/rv32i.v/rv32.v

echo "CLOC impl"
IMPL_FILES=("Common.v" "External.v" "Machine.v" "Memory.v" "Multiplier.v" "RegFile.v" "rv32i.v" "RVCore.v" "RVEncoding.v" "Scoreboard.v" "SecurityMonitor.v")
cloc "${IMPL_FILES[@]}"


