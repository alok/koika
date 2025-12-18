# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What is Kôika?

Kôika is a hardware design language inspired by BlueSpec SystemVerilog. Programs are built from **rules** (atomic state update operations) orchestrated by a **scheduler**. The language provides one-rule-at-a-time semantics with formal verification support.

## Build Commands

```sh
# Full build (Coq + OCaml + examples + tests)
make all

# Build just Coq library (fast, no proofs)
make coq

# Build Coq library with proofs (slower)
make coq-all

# Build examples
make examples

# Build tests
make tests

# Clean everything
make clean

# Using Nix (reproduces CI exactly)
nix build
nix flake check
```

The build uses dune. Before building examples/tests, run `make configure` (creates `dune.inc` files).

## Architecture Overview

### Coq Core (`coq/`)
The formal semantics and verified compiler, organized in layers:

1. **Syntax Layer**: `Syntax.v` (untyped AST), `TypedSyntax.v` (typed AST)
2. **Semantics**: `TypedSemantics.v` (rule execution), `Logs.v` (read/write tracking)
3. **Lowering**: `Lowering.v` (AST→lowered form), `LoweredSyntax.v`
4. **Circuit Generation**: `CircuitSyntax.v`, `CircuitGeneration.v`, `CircuitOptimization.v`
5. **Verification**: `OneRuleAtATime.v` (atomicity proof), `CompilerCorrectness/` (full compiler correctness)

Key imports for writing Kôika programs: `Require Import Koika.Frontend.`

### OCaml Compiler (`ocaml/`)
- `cuttlec.ml`: Main CLI entry point
- `frontends/`: Coq package loader (`coq.ml`), Lispy Verilog parser (`lv.ml`)
- `backends/`: Code generators for Verilog, C++ (cuttlesim), DOT, Verilator drivers
- `cuttlebone/`: Core data structures shared between frontends/backends

### Syntax Notation

Kôika uses custom Coq notations (defined in `SyntaxMacros.v`):
- `{{ ... }}` — rule body
- `read0(reg)`, `read1(reg)` — read register at port 0/1
- `write0(reg, val)`, `write1(reg, val)` — write register
- `|16`d42|` — 16-bit decimal literal
- `Ob~1~0~1` — binary literal
- `get(struct, field)` — struct field access
- `rl1 |> rl2 |> done` — scheduler priority chain

### Examples Structure

Each example (e.g., `gcd_machine.v`) defines:
1. `reg_t` — register types (inductive)
2. `R : reg_t -> type` — register type mapping
3. `rules` — rule definitions using `tc_rules`
4. `scheduler` — priority order
5. `package` — bundled config for extraction

## Testing

```sh
# Run all tests
make tests

# Run specific example
dune build @examples/<file>.v.d/runtest

# Check Coq proof axioms
make coq-check
```

## Dependencies

- OCaml 4.14, Coq 8.18, dune 3.14+
- OCaml packages: base, core, core_unix, stdio, parsexp, hashcons, zarith
- For RISC-V tests: RISC-V toolchain
- For C++ sim: C++ compiler, libboost-dev

## Key Files for Understanding the Pipeline

1. `coq/Frontend.v` — top-level imports for user programs
2. `coq/Compiler.v` — `compile_scheduler` entry point
3. `coq/Interop.v` — package structure for extraction
4. `examples/gcd_machine.v` — minimal complete example
5. `examples/rv/RVCore.v` — complex RISC-V processor example

---

## Lean 4 Port (`lean4/`)

### Build Commands

```sh
cd lean4
lake build        # Build all modules
lake build Koika  # Build just the library
```

### Port Status (~85% complete for core semantics)

| Coq Module | Lean Module | Status |
|------------|-------------|--------|
| `Types.v` | `Types.lean` | ✅ Complete |
| `Syntax.v` | `Syntax.lean` | ✅ Complete |
| `TypedSyntax.v` | `TypedSyntax.lean` | ✅ Complete |
| `Primitives.v` | `Primitives.lean` | ✅ Complete |
| `Logs.v` | `Semantics/Logs.lean` | ✅ Complete |
| `TypedSemantics.v` | `Semantics/Interp.lean` | ✅ Complete |
| `LoweredSyntax.v` | `Compile/Lowered.lean` | ✅ Complete |
| `LoweredSemantics.v` | `Semantics/LoweredInterp.lean` | ⚠️ 10 sorries |
| `Lowering.v` | `Compile/Lower.lean` | ✅ Complete |
| `CircuitSyntax.v` | `Compile/Circuit.lean` | ✅ Complete |
| `CircuitGeneration.v` | `Compile/Compiler.lean` | ✅ Complete |
| `LoweringCorrectness.v` | `Compile/Correctness/LoweringCorrectness.lean` | ⚠️ 18 sorries |
| `CircuitCorrectness.v` | `Compile/Correctness/CircuitCorrectness.lean` | ⚠️ 2 sorries |
| Verilog backend | `Backend/Verilog.lean` | ⚠️ Stub only |

**Total sorries: 36** (mainly in correctness proofs)

### Key Differences from Coq

1. **DSL**: Uses `koika!` macro instead of Coq notations
2. **BitVec**: Native Lean 4 `BitVec` instead of custom `bits` type
3. **Arrays**: `Fin n → α` instead of `vect α n`
4. **No extraction needed**: Lean compiles natively

### Current TODOs (for future sessions)

#### High Priority
1. **Fill `Properties/Primitives.lean` sorries** (4 sorries)
   - `unpackValue_packValue` struct/array cases
   - `packValue_unpackValue` struct/array cases
   - Need bitvector extraction reconstruction lemmas:
     ```lean
     -- Key pattern from Coq: extractLsb' reconstructs original
     theorem extractLsb'_ofNat_low/high ...
     ```

2. **Fill `LoweredInterp.lean` sorries** (10 sorries)
   - These are "correct by construction" - WF recursion breaks definitional equality
   - May need `native_decide` or explicit proof terms

3. **Port log lemmas from `SemanticProperties.v`**
   - `log_find_app`, `log_app_assoc`, `log_app_empty_l`
   - `log_forallb_app`, `log_existsb_app`
   - Needed for `LoweringCorrectness.lean`

#### Medium Priority
4. **Fill `LoweringCorrectness.lean` sorries** (18 sorries)
   - Main action lowering theorem by case analysis
   - Coq uses Ltac `lowering_correct_t` for automation
   - Key lemmas needed: `context_equiv_cassoc`, `context_equiv_ctl`

5. **Expand Verilog backend**
   - Currently only unop/binop generation
   - Missing: circuit emission, testbench generation

#### Low Priority
6. **Port C++ backend (cuttlesim)**
7. **Port DOT backend**
8. **Add examples**

### Key Coq Files to Study

For filling proofs, study these Coq files:
- `coq/Types.v:119-232` — `bits_of_value`/`value_of_bits` roundtrip proofs
- `coq/PrimitiveProperties.v` — `get_field_bits_slice`, `subst_field_bits_slice_subst`
- `coq/SemanticProperties.v` — Log composition lemmas
- `coq/CompilerCorrectness/LoweringCorrectness.v` — Main correctness proof structure
