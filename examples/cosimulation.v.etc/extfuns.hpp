#include "blackbox.obj_dir.opt/Vblackbox.h"

using Dut = Vblackbox;

class BlackboxWrapper {
public:
  Dut dut;

  void cycle() {
    dut.CLK = 1;
    dut.eval();
    dut.CLK = 0;
    dut.eval();
  }

  BlackboxWrapper() : dut{} {}
};

struct extfuns {
  BlackboxWrapper blackbox_driver;

  bits<32> blackbox(bits<32> input) {
    blackbox_driver.dut.in = input.v;
    blackbox_driver.cycle();
    return  bits<32>{blackbox_driver.dut.out};
  }
};