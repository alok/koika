/*! Custom Cuttlesim driver that implements a Kôika extfun using a Verilator model !*/
#include "cosimulation.hpp"
#include <verilated.h>


class simulator final : public module_cosimulation<extfuns> {
  void strobe() const {
    std::cout << "# Cycle: " << meta.cycle_id << std::endl;
    snapshot().report();
  }
};

int main(int argc, char **argv) { return cuttlesim::main<simulator>(argc, argv); }

// Local Variables:
// flycheck-clang-include-path: ("/usr/share/verilator/include" "/usr/local/share/verilator/include/")
// End:
