/-
  Koika/Compile/Compiler.lean - Port of coq/Compiler.v
  Top-level compilation function that ties everything together

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/Compiler.v
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.TypedSyntax
import Koika.Compile.Lowered
import Koika.Compile.Lower
import Koika.Compile.Circuit
import Koika.Compile.CircuitSemantics
import Koika.Compile.Optimize

namespace Koika

namespace Compiler

/-- Circuit-level register environment (alias for CRegEnv) -/
abbrev RegEnv (reg_t : Type) (CR : reg_t → Nat) := CRegEnv reg_t CR

/-- Circuit-level external function environment (alias for CExtEnv) -/
abbrev ExtEnv (ext_fn_t : Type) (CSigma : ext_fn_t → CExternalSig) := CExtEnv ext_fn_t CSigma

/-! ## End-to-End Compilation

This module provides the top-level compilation entry points that connect
typed rules to circuit generation and interpretation.
-/

section Compiler

variable {reg_t ext_fn_t rule_name_t : Type}
variable [DecidableEq reg_t]

variable (R : reg_t → Ty)
variable (Sigma : ext_fn_t → ExternalSig)

/-! ## Top-Level Compilation Function -/

/-- Compile a scheduler with typed rules into register update circuits.

This is the main entry point for Koika compilation:
1. Creates read register circuits
2. Lowers typed rules to circuit-level actions
3. Compiles the scheduler with optimizations
4. Returns circuits for updating each register

Parameters:
- `rules`: Maps rule names to typed rule definitions
- `s`: The scheduler defining rule execution order

Returns: A `SchedulerCircuit` containing the write enable and write data
         circuits for each register.
-/
def compileSchedulerWithRules
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    : SchedulerCircuit reg_t ext_fn_t rule_name_t (lowerR R) (lowerSigma Sigma) :=
  -- Create read register circuits
  let regCircuits : (r : reg_t) → Circuit reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) ((lowerR R) r) :=
    fun r => .readReg r
  -- Lower typed rules to circuit-level
  let loweredRules : rule_name_t → LRule reg_t ext_fn_t (lowerR R) (lowerSigma Sigma) :=
    fun rl => lowerRule R Sigma (rules rl)
  -- Compile with optimizations
  let circuits := compileScheduler (lowerR R) (lowerSigma Sigma) regCircuits loweredRules s
  -- Apply optimizations
  optimizeSchedulerCircuit circuits

/-! ## Circuit Interpretation -/

/-- Interpret all register update circuits in a scheduler circuit.

Given:
- `circuits`: The compiled scheduler circuit (from `compileSchedulerWithRules`)
- `regEnv`: Current register values
- `extEnv`: External function implementations

Returns: A function mapping each register to its new value after one cycle.
-/
def interpSchedulerCircuits
    (circuits : SchedulerCircuit reg_t ext_fn_t rule_name_t (lowerR R) (lowerSigma Sigma))
    (regEnv : RegEnv reg_t (lowerR R))
    (extEnv : ExtEnv ext_fn_t (lowerSigma Sigma))
    : (r : reg_t) → BitVec ((lowerR R) r) :=
  fun r =>
    let writeEnabled := interpCircuit regEnv extEnv (circuits.writeEnable r)
    if isTrue writeEnabled then
      interpCircuit regEnv extEnv (circuits.writeData r)
    else
      regEnv r

/-! ## Convenience Functions -/

/-- Lower external function implementation from typed to circuit level -/
def lowerExtEnv
    (sigma : (f : ext_fn_t) → (Sigma f).argType.denote → (Sigma f).retType.denote)
    : ExtEnv ext_fn_t (lowerSigma Sigma) :=
  fun f arg =>
    let typedArg : (Sigma f).argType.denote := valueOfBits arg
    let typedResult := sigma f typedArg
    bitsOfValue typedResult

/-- Execute one cycle: compile, interpret, and update registers -/
def executeOneCycle
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    (regEnv : RegEnv reg_t (lowerR R))
    (extEnv : ExtEnv ext_fn_t (lowerSigma Sigma))
    : RegEnv reg_t (lowerR R) :=
  let circuits := compileSchedulerWithRules R Sigma rules s
  interpSchedulerCircuits R Sigma circuits regEnv extEnv

end Compiler -- end section

end Compiler -- end namespace

/-! ## Legacy Notation Compatibility

These definitions maintain compatibility with the Coq naming conventions.
-/

/-- Compatibility alias for compile_scheduler -/
abbrev compile_scheduler {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
    (R : reg_t → Ty)
    (Sigma : ext_fn_t → ExternalSig)
    (rules : rule_name_t → Rule reg_t ext_fn_t R Sigma)
    (s : Scheduler Unit rule_name_t)
    : SchedulerCircuit reg_t ext_fn_t rule_name_t (lowerR R) (lowerSigma Sigma) :=
  Compiler.compileSchedulerWithRules R Sigma rules s

/-- Compatibility alias for interp_circuits -/
abbrev interp_circuits {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
    (R : reg_t → Ty)
    (Sigma : ext_fn_t → ExternalSig)
    (circuits : SchedulerCircuit reg_t ext_fn_t rule_name_t (lowerR R) (lowerSigma Sigma))
    (regEnv : CRegEnv reg_t (lowerR R))
    (extEnv : CExtEnv ext_fn_t (lowerSigma Sigma))
    : (r : reg_t) → BitVec ((lowerR R) r) :=
  Compiler.interpSchedulerCircuits R Sigma circuits regEnv extEnv

end Koika
