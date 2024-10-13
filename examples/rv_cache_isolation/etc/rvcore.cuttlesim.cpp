/*! C++ driver for rv32i simulation with Cuttlesim !*/
#include <iostream>
#include <optional>
#include <memory>
#include "rv32.hpp"
#include "elf.hpp"
#include "cuttlesim.hpp"

#define DMEM_SIZE (static_cast<std::size_t>(1) << 25)
#define MEM_DEBUG 0

#define LOG_NUM_SETS 9
#define LOG_TAG_SZ 21

#define NUM_SETS (static_cast<std::size_t>(1) << LOG_NUM_SETS)

struct metadata_bram {
  std::unique_ptr<struct_metadata[]> mem;
  std::optional<struct_metadata_req> last;
  int core_id;
  int cache_id;

  std::optional<struct_metadata> get(bool enable) {
    if (!enable || !last.has_value())
      return std::nullopt;
    auto isWrite = last->is_write;
    auto index = last->addr; // index
    auto data = last->data; 
    auto tag = data.tag;
    auto valid = data.valid;

    bits<32> addr = (prims::widen<32>(tag)<< (LOG_NUM_SETS + 2)) | ((prims::widen<32>(index) << 2));

 #if MEM_DEBUG
    printf("MetadataReq: $(%d,%d); isWrite 0x%x; index 0x%x; addr:0x%x; valid:0x%x\n", 
            core_id, cache_id, isWrite.v, index.v, addr.v, valid.v);
#endif // MEM_DEBUG

    auto current = mem[index.v];
    last.reset(); 

    if (isWrite) {
      mem[index.v] = data;
 #if MEM_DEBUG
      printf("MetadataResp: store no resp\n");
#endif // MEM_DEBUG

      return std::nullopt;
    } else { // Read 
 #if MEM_DEBUG
      printf("MetadataResp: $(%d,%d); tag:0x%x; valid:0x%x\n", 
           core_id, cache_id, current.tag.v, current.valid.v);
#endif // MEM_DEBUG
      return std::optional<struct_metadata>{current};

    }

  }

  bool put(std::optional<struct_metadata_req> req) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_metadata_output getput(struct_metadata_input req) {
    std::optional<struct_metadata> get_response = get(bool(req.get_ready));
    bool put_ready = put(req.put_valid ? std::optional<struct_metadata_req>{req.put_request} : std::nullopt);
    return struct_metadata_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(struct_metadata{})
    };
  }

  metadata_bram(int core_id, int cache_id) : 
      mem{std::make_unique<struct_metadata[]>(NUM_SETS)}, 
      last{}, core_id{core_id}, cache_id{cache_id} {}
};
struct cache_bram {
  std::unique_ptr<bits<32>[]> mem;
  std::optional<struct_cache_req> last;
  int core_id;
  int cache_id;

  std::optional<bits<32>> get(bool enable) {
    if (!enable || !last.has_value())
      return std::nullopt;

    auto data = last->data;
    auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> current = bits<32>{0};

#if MEM_DEBUG
    printf("CacheReq: $(%d,%d); dEn 0x%x; data 0x%x; addr:0x%x\n", 
          core_id, cache_id, dEn.v, data.v, addr.v);
#endif // MEM_DEBUG

    current = mem[addr.v ];
    mem[addr.v ] =
      ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
      ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
      ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
      ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);

    last.reset();
    if (dEn.v == 0x0) { // Load
#if MEM_DEBUG
      printf("CacheResp: $(%d,%d); dEn : 0x%x; addr: 0x%x; data: 0x%x\n", 
             core_id, cache_id, dEn.v, addr.v, current.v);
#endif // MEM_DEBUG
      return std::optional<bits<32>>{ current };
    } else { // Store 
#if MEM_DEBUG
      printf("CacheResp: store; no resp\n"); 
#endif // MEM_DEBUG
      return std::nullopt;
    }
  }

  bool put(std::optional<struct_cache_req> req) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_cache_output getput(struct_cache_input req) {
    std::optional<bits<32>> get_response = get(bool(req.get_ready));
    bool put_ready = put(req.put_valid ? std::optional<struct_cache_req>{req.put_request} : std::nullopt);
    return struct_cache_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(bits<32>{0})
    };
  }

  // Use new … instead of make_unique to avoid 0-initialization
  cache_bram(int core_id, int cache_id)
      : mem{new bits<32>[DMEM_SIZE]}, last{}, core_id(core_id), cache_id(cache_id) {}
};

struct bram {
  std::unique_ptr<bits<32>[]> mem;
  std::optional<struct_mem_req> last;

  std::optional<struct_mem_resp> get(bool enable) {
    if (!enable || !last.has_value())
      return std::nullopt;

    auto data = last->data;
    auto addr = last->addr;
    auto dEn = last->byte_en;
    bits<32> current = bits<32>{0};

#if MEM_DEBUG
    printf("MainReq: dEn 0x%x; data 0x%x; addr:0x%x\n", dEn.v, data.v, addr.v);
#endif // MEM_DEBUG

    current = mem[addr.v >> 2];
    mem[addr.v >> 2] =
      ((dEn[2'0_d] ? data : current) & 0x32'000000ff_x) |
      ((dEn[2'1_d] ? data : current) & 0x32'0000ff00_x) |
      ((dEn[2'2_d] ? data : current) & 0x32'00ff0000_x) |
      ((dEn[2'3_d] ? data : current) & 0x32'ff000000_x);

    last.reset();

    if (dEn.v == 0x0) {
#if MEM_DEBUG
      printf("MainResp: byte_en: 0x%x; addr: 0x%x; data: 0x%x\n", dEn.v, addr.v, current.v);
#endif // MEM_DEBUG
      return std::optional<struct_mem_resp>{{
        .byte_en = dEn, .addr = addr, .data = current
      }};
    } else {
#if MEM_DEBUG
      printf("MainStore: return nothing\n");
#endif // MEM_DEBUG
      return std::optional<struct_mem_resp>{std::nullopt};
    }
  }

  bool put(std::optional<struct_mem_req> req) {
    if (!req.has_value() || last.has_value())
      return false;

    last = *req;
    return true;
  }

  struct_mem_output getput(struct_mem_input req) {
    std::optional<struct_mem_resp> get_response = get(bool(req.get_ready));
    bool put_ready = put(req.put_valid ? std::optional<struct_mem_req>{req.put_request} : std::nullopt);
    return struct_mem_output{
      .get_valid = bits<1>{get_response.has_value()},
      .put_ready = bits<1>{put_ready},
      .get_response = get_response.value_or(struct_mem_resp{})
    };
  }

  void read_elf(const std::string& elf_fpath) {
    elf_load(reinterpret_cast<uint32_t*>(mem.get()), elf_fpath.c_str());
  }

  // Use new … instead of make_unique to avoid 0-initialization
  bram() : mem{new bits<32>[DMEM_SIZE]}, last{} {}
};

struct extfuns_t {
  bram mainmem;
  metadata_bram metadata_imem0;
  metadata_bram metadata_dmem0;
  metadata_bram metadata_imem1;
  metadata_bram metadata_dmem1;
  cache_bram cache_imem0;
  cache_bram cache_dmem0;
  cache_bram cache_imem1;
  cache_bram cache_dmem1;


  bits<1> led;

  struct_mem_output ext_mainmem(struct_mem_input req) {
    return mainmem.getput(req);
  }

  struct_metadata_output ext_metadata_imem_CoreId0 (struct_metadata_input req) {
    return metadata_imem0.getput(req);
  }
  struct_metadata_output ext_metadata_imem_CoreId1 (struct_metadata_input req) {
    return metadata_imem1.getput(req);
  }

  struct_metadata_output ext_metadata_dmem_CoreId0 (struct_metadata_input req) {
    return metadata_dmem0.getput(req);
  }
  struct_metadata_output ext_metadata_dmem_CoreId1 (struct_metadata_input req) {
    return metadata_dmem1.getput(req);
  }
  struct_cache_output ext_cache_imem_CoreId0 (struct_cache_input req) {
    return cache_imem0.getput(req);
  }
  struct_cache_output ext_cache_imem_CoreId1 (struct_cache_input req) {
    return cache_imem1.getput(req);
  }

  struct_cache_output ext_cache_dmem_CoreId0 (struct_cache_input req) {
    return cache_dmem0.getput(req);
  }
  struct_cache_output ext_cache_dmem_CoreId1 (struct_cache_input req) {
    return cache_dmem1.getput(req);
  }


  bits<1> ext_uart_write(struct_maybe_bits_8 req) {
    if (req.valid) {
      putchar(static_cast<char>(req.data.v));
    }
    return req.valid;
  }

  struct_maybe_bits_8 ext_uart_read(bits<1> req) {
    bool valid = req.v;
    return struct_maybe_bits_8 {
      .valid = bits<1>{valid},
      .data = bits<8>{(bits_t<8>)(valid ? getchar() : 0)} };
  }

  bits<1> ext_led(struct_maybe_bits_1 req) {
    bits<1> current = led;
    if (req.valid) {
      led = req.data;
      fprintf(stderr, led.v ? "☀" : "🌣");
    }
    return current;
  }

  template<typename simulator>
  bits<1> ext_finish(simulator& sim, struct_maybe_bits_8 req) {
    if (req.valid) {
      bits<8> exitcode = req.data;
      if (exitcode == 8'0_b) {
        printf("  [0;32mPASS[0m\n");
      } else {
        printf("  [0;31mFAIL[0m (%d)\n", exitcode.v);
      }
      sim.finish(cuttlesim::exit_info_none, exitcode.v);
    }
    return 1'0_b;
  }

  extfuns_t() : mainmem{}, 
                metadata_imem0{metadata_bram(0,0)},
                metadata_dmem0{metadata_bram(0,1)},
                metadata_imem1{metadata_bram(1,0)},
                metadata_dmem1{metadata_bram(1,1)},
                cache_imem0{cache_bram(0,0)},
                cache_dmem0{cache_bram(0,1)},
                cache_imem1{cache_bram(1,0)},
                cache_dmem1{cache_bram(1,1)},
                led{false} {}
};

class rv_core final : public module_rv32<extfuns_t> {
  void strobe() const {
#if defined(SIM_STROBE) && !defined(SIM_MINIMAL)
    std::cout << "# " << ncycles << std::endl;
    std::cout << "pc = " << Log.state.pc << std::endl;
    std::cout << "epoch = " << Log.state.epoch << std::endl;
    std::cout << "inst_count = " << Log.state.inst_count << std::endl;
    std::cout << "rf = {" << std::endl;
    std::cout << "  " <<
      "[01] (ra) = " << Log.state.rf_x01_ra << "; " <<
      "[02] (sp) = " << Log.state.rf_x02_sp << "; " <<
      "[03] (gp) = " << Log.state.rf_x03_gp << "; " <<
      "[04] (tp) = " << Log.state.rf_x04_tp << std::endl;
    std::cout << "  [05-07] (t0-t2)     = " <<
      Log.state.rf_x05_t0 << "; " <<
      Log.state.rf_x06_t1 << "; " <<
      Log.state.rf_x07_t2 << std::endl;
    std::cout << "  [08-09] (s0_fp, s1) = " <<
      Log.state.rf_x08_s0_fp << "; " <<
      Log.state.rf_x09_s1 << std::endl;
    std::cout << "  [10-17] (a0-a7)     = " <<
      Log.state.rf_x10_a0 << "; " <<
      Log.state.rf_x11_a1 << "; " <<
      Log.state.rf_x12_a2 << "; " <<
      Log.state.rf_x13_a3 << "; " <<
      Log.state.rf_x14_a4 << "; " <<
      Log.state.rf_x15_a5 << "; " <<
      Log.state.rf_x16_a6 << "; " <<
      Log.state.rf_x17_a7 << std::endl;
    std::cout << "  [18-27] (s2-s11)    = " << Log.state.rf_x18_s2 << "; " <<
      Log.state.rf_x19_s3 << "; " <<
      Log.state.rf_x20_s4 << "; " <<
      Log.state.rf_x21_s5 << "; " <<
      Log.state.rf_x22_s6 << "; " <<
      Log.state.rf_x23_s7 << "; " <<
      Log.state.rf_x24_s8 << "; " <<
      Log.state.rf_x25_s9 << "; " <<
      Log.state.rf_x26_s10 << "; " <<
      Log.state.rf_x27_s11 << std::endl;
    std::cout << "  [28-31] (t3-t6)     = " <<
      Log.state.rf_x28_t3 << "; " <<
      Log.state.rf_x29_t4 << "; " <<
      Log.state.rf_x30_t5 << "; " <<
      Log.state.rf_x31_t6 << std::endl;
    std::cout << "}" << std::endl;
    std::cout <<
      "toIMem = { valid0 = " << Log.state.toIMem_valid0
              << ", data0 = " << Log.state.toIMem_data0 << " };" <<
      "fromIMem = { valid0 = " << Log.state.fromIMem_valid0
              << ", data0 = " << Log.state.fromIMem_data0 << " }" << std::endl;
    std::cout <<
      "toDMem = { valid0 = " << Log.state.toDMem_valid0
              << ", data0 = " << Log.state.toDMem_data0 << " };" <<
      "fromDMem = { valid0 = " << Log.state.fromDMem_valid0
              << ", data0 = " << Log.state.fromDMem_data0 << " }" << std::endl;
    std::cout <<
      "toSM = { valid0 = " << Log.state.toSM_valid0
              << ", data0 = " << Log.state.toSM_data0 << " };" << std::endl;

    std::cout <<
      "f2d    = { valid0 = " << Log.state.f2d_valid0
              << ", data0 = " << Log.state.f2d_data0 << " };" <<
      "f2dprim  = { valid0 = " << Log.state.f2dprim_valid0
              << ", data0 = " << Log.state.f2dprim_data0 << " }" << std::endl;
    std::cout <<
      "d2e    = { valid0 = " << Log.state.d2e_valid0
              << ", data0 = " << Log.state.d2e_data0 << " };" <<
      "e2w      = { valid0 = " << Log.state.e2w_valid0
              << ", data0 = " << Log.state.e2w_data0 << " }" << std::endl;
#endif
  }

public:
  explicit rv_core(const std::string& elf_fpath) : module_rv32{} {
    extfuns.mainmem.read_elf(elf_fpath);
  }
};

#ifdef SIM_MINIMAL
template rv_core::snapshot_t cuttlesim::init_and_run<rv_core>(unsigned long long, std::string&);
#else
int main(int argc, char** argv) {
  if (argc <= 1) {
    std::cerr << "Usage: ./rv_core elf_file [ncycles [vcd_path [vcd_period]]]" << std::endl;
    return 1;
  }

  setbuf(stdout, NULL);
  std::ios_base::sync_with_stdio(false);
  cuttlesim::main<rv_core>(argc - 1, argv + 1, argv[1]);
}
#endif

// Local Variables:
// flycheck-clang-include-path: ("../_objects/rv32i.v/")
// flycheck-clang-language-standard: "c++17"
// End:
