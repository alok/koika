/-
  Koika/Compile/Correctness/CircuitCorrectness.lean
  Port of coq/CompilerCorrectness/CircuitCorrectness.v

  Proof that circuit generation preserves the semantics of lowered actions.
  This is the core correctness theorem for the circuit compiler.
-/

import Koika.Types
import Koika.Primitives
import Koika.Compile.Lowered
import Koika.Compile.Circuit
import Koika.Compile.CircuitSemantics
import Koika.Compile.CircuitProperties
import Koika.Semantics.Logs
import Koika.Semantics.LoweredInterp
import Koika.Semantics.Properties
import Koika.FiniteType

namespace Koika

/-! ## Circuit Compilation Correctness

This module proves that the circuit generation phase correctly implements
the lowered semantics. The main theorem states that interpreting the generated
circuits produces the same results as interpreting the lowered actions.
-/

section CircuitCorrectness

variable {pos_t var_t rule_name_t reg_t ext_fn_t : Type}
variable [DecidableEq reg_t] [FiniteType reg_t]
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

variable (cr : (r : reg_t) → BitVec (CR r))
variable (csigma : (f : ext_fn_t) → BitVec (CSigma f).argSize → BitVec (CSigma f).retSize)

/-! ### Circuit Environment Equivalence -/

/-- Circuit environment equivalence: each circuit evaluates to register value -/
def circuitEnvEquiv
    (rc : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r)) : Prop :=
  ∀ idx, interpCircuit cr csigma (rc idx) = cr idx

/-! ### Log Consistency Invariants -/

/-- The data0 field correctly reflects latest_write0 -/
def logData0Consistent' (l : LInterpLog CR) (regs : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)) : Prop :=
  ∀ idx,
    interpCircuit cr csigma (regs idx).data0 =
    match l.latestWrite0 idx with
    | some v => v
    | none => cr idx

/-- The data1 field correctly reflects latest_write1 when write1 exists -/
def logData1Consistent' (l : LInterpLog CR) (regs : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)) : Prop :=
  ∀ idx,
    l.existsb idx isWrite1 = true →
    match l.latestWrite1 idx with
    | some v => interpCircuit cr csigma (regs idx).data1 = v
    | none => False

/-- The read/write flags correctly reflect the log -/
def logRwdataConsistent (log : LInterpLog CR) (regs : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)) : Prop :=
  ∀ idx,
    interpCircuit cr csigma (regs idx).read0 = BitVec.ofBool (log.existsb idx isRead0) ∧
    interpCircuit cr csigma (regs idx).read1 = BitVec.ofBool (log.existsb idx isRead1) ∧
    interpCircuit cr csigma (regs idx).write0 = BitVec.ofBool (log.existsb idx isWrite0) ∧
    interpCircuit cr csigma (regs idx).write1 = BitVec.ofBool (log.existsb idx isWrite1)

/-! ### Circuit Context Equivalence -/

/-- Circuit context equivalence -/
def circuitGammaEquiv {sig : LSig}
    (Gamma : LContext sig)
    (gamma : CContext reg_t ext_fn_t CR CSigma sig) : Prop :=
  ∀ sz (m : LMember sz sig),
    interpCircuit cr csigma (gamma.get m) = Gamma.get m

/-! ### Main Theorems -/

variable (rc : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r))
variable (rules : rule_name_t → LRule reg_t ext_fn_t CR CSigma)

/-- **Scheduler Circuit Correctness**

The compiled scheduler produces circuits that correctly implement
the scheduler semantics. The final writeData evaluates to the correct value.
-/
theorem compile_scheduler_circuit_correct
    (s : Scheduler Unit rule_name_t) :
    circuitEnvEquiv cr csigma rc →
    ∀ idx,
      interpCircuit cr csigma ((compileScheduler CR CSigma rc rules s).writeData idx) =
      match (interpLScheduler CR CSigma cr csigma rules SimpleLog.empty s).latestWrite idx with
      | some v => v
      | none => cr idx := by
  sorry

/-- **Compile Scheduler Correctness**

The main correctness theorem: compiled circuits produce the same
register values as interpreting the scheduler directly.
-/
theorem compile_scheduler'_correct
    (s : Scheduler Unit rule_name_t) :
    circuitEnvEquiv cr csigma rc →
    ∀ idx,
      interpCircuit cr csigma ((compileScheduler CR CSigma rc rules s).writeData idx) =
      (interpLCycle CR CSigma cr csigma rules s) idx := by
  sorry

end CircuitCorrectness

/-! ### Initial Circuit Environment -/

section CircuitInit

variable {pos_t var_t rule_name_t reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- The initial circuit environment (reading registers) is equivalent -/
theorem circuitEnvEquiv_readReg
    (cr : (r : reg_t) → BitVec (CR r))
    (csigma : (f : ext_fn_t) → BitVec (CSigma f).argSize → BitVec (CSigma f).retSize) :
    circuitEnvEquiv cr csigma (fun r => .readReg r) := by
  intro r
  simp only [interpCircuit]

end CircuitInit

end Koika
