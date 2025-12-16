/-
  Koika/Compile/CircuitSemantics.lean - Port of coq/CircuitSemantics.v
  Circuit interpretation/evaluation

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/CircuitSemantics.v
-/

import Koika.Compile.Circuit
import Koika.Primitives

namespace Koika

/-! ## Circuit Interpretation

This module defines the semantics of circuits by interpreting them as functions
from register values and external function implementations to bitvector results.
-/

section Interpretation

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Circuit register environment: maps each register to its current bitvector value -/
abbrev CRegEnv (reg_t : Type) (CR : reg_t → Nat) :=
  (r : reg_t) → BitVec (CR r)

/-- Circuit external function environment: maps each external function to its bitvector semantics -/
abbrev CExtEnv (ext_fn_t : Type) (CSigma : ext_fn_t → CExternalSig) :=
  (f : ext_fn_t) → BitVec (CSigma f).argSize → BitVec (CSigma f).retSize

/-- Test if a 1-bit bitvector is true (nonzero) -/
def isTrue (b : BitVec 1) : Bool :=
  b.toNat ≠ 0

/-- Interpret/evaluate a circuit to a bitvector value.

Given:
- A register environment `regEnv` mapping registers to their current values
- An external function environment `extEnv` implementing external functions
- A circuit `c` of size `sz`

Returns: The bitvector value of size `sz` that the circuit computes.
-/
def interpCircuit
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    : {sz : Nat} → Circuit reg_t ext_fn_t CR CSigma sz → BitVec sz
  | _, .mux select c1 c2 =>
      if isTrue (interpCircuit regEnv extEnv select) then
        interpCircuit regEnv extEnv c1
      else
        interpCircuit regEnv extEnv c2
  | _, .const cst =>
      cst
  | _, .readReg reg =>
      regEnv reg
  | _, .external fn arg =>
      extEnv fn (interpCircuit regEnv extEnv arg)
  | _, .unop fn arg =>
      Circuit.evalFBits1 fn (interpCircuit regEnv extEnv arg)
  | _, .binop fn arg1 arg2 =>
      Circuit.evalFBits2 fn (interpCircuit regEnv extEnv arg1) (interpCircuit regEnv extEnv arg2)
  | _, .annot _ c =>
      interpCircuit regEnv extEnv c

end Interpretation

/-! ## Helper Functions for Circuit Evaluation -/

namespace Circuit

/-- Evaluate a circuit in a given register and external function environment -/
def eval {reg_t ext_fn_t : Type} {CR : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    (regEnv : CRegEnv reg_t CR)
    (extEnv : CExtEnv ext_fn_t CSigma)
    (c : Circuit reg_t ext_fn_t CR CSigma sz)
    : BitVec sz :=
  interpCircuit regEnv extEnv c

end Circuit

end Koika
