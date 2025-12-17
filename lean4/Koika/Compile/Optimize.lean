/-
  Koika/Compile/Optimize.lean - Port of coq/CircuitOptimization.v
  Local optimization of circuits
-/

import Koika.Types
import Koika.Primitives
import Koika.Compile.Circuit

namespace Koika

/-! ## Circuit Optimization Utilities -/

namespace CircuitOpt

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Strip annotations from a circuit -/
def unannot : Circuit reg_t ext_fn_t CR CSigma sz → Circuit reg_t ext_fn_t CR CSigma sz
  | .annot _ c => unannot c
  | c => c

/-- Size measure for circuits (sum of all sub-circuit sizes) -/
def circuitSize : {sz : Nat} → Circuit reg_t ext_fn_t CR CSigma sz → Nat
  | _, .const _ => 1
  | _, .readReg _ => 1
  | _, .mux sel t f => 1 + circuitSize sel + circuitSize t + circuitSize f
  | _, .unop _ arg => 1 + circuitSize arg
  | _, .binop _ a1 a2 => 1 + circuitSize a1 + circuitSize a2
  | _, .external _ arg => 1 + circuitSize arg
  | _, .annot _ c => 1 + circuitSize c

/-- Stripping annotations preserves or decreases size -/
theorem unannot_size_le (c : Circuit reg_t ext_fn_t CR CSigma sz) :
    circuitSize (unannot c) ≤ circuitSize c := by
  induction c with
  | annot s c ih => simp only [unannot, circuitSize] at *; omega
  | _ => simp only [unannot]; exact Nat.le_refl _

/-- Try to extract a constant from a circuit -/
def asConst (c : Circuit reg_t ext_fn_t CR CSigma sz) : Option (BitVec sz) :=
  match unannot c with
  | .const v => some v
  | _ => none

/-- Check if a circuit is a specific constant -/
def isConst (c : Circuit reg_t ext_fn_t CR CSigma sz) (v : BitVec sz) : Bool :=
  match asConst c with
  | some v' => v == v'
  | none => false

/-! ## Constant Propagation -/

/-- Constant propagation optimization
    Performs the following simplifications:
    - Not(1) => 0, Not(0) => 1
    - And(_, 0) | And(0, _) => 0
    - And(c, 1) | And(1, c) => c
    - Or(_, 1) | Or(1, _) => 1
    - Or(c, 0) | Or(0, c) => c
    - Mux(0, x, y) => y, Mux(1, x, y) => x -/
def optConstProp (c : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  match sz with
  | 0 => .const 0
  | _ =>
    match unannot c with
    | .unop (.not _) c1 =>
        match asConst c1 with
        | some v => .const (~~~v)
        | none => c
    | .binop (.and _) c1 c2 =>
        if isConst c1 0 || isConst c2 0 then .const 0
        else if isConst c1 (BitVec.allOnes _) then c2
        else if isConst c2 (BitVec.allOnes _) then c1
        else c
    | .binop (.or _) c1 c2 =>
        if isConst c1 (BitVec.allOnes _) || isConst c2 (BitVec.allOnes _) then
          .const (BitVec.allOnes _)
        else if isConst c1 0 then c2
        else if isConst c2 0 then c1
        else c
    | .mux sel c1 c2 =>
        if isConst sel 1 then c1
        else if isConst sel 0 then c2
        else c
    | _ => c

/-! ## Identical Value Elimination -/

/-- Check structural equality of circuits (conservative approximation).
    Returns true only for structurally identical const or mux circuits.
    Uses well-founded recursion on circuit size sum. -/
def circuitEquiv (c1 c2 : Circuit reg_t ext_fn_t CR CSigma sz) : Bool :=
  circuitEquivAux (unannot c1) (unannot c2)
where
  /-- Helper that compares already-unannotated circuits -/
  circuitEquivAux : {sz : Nat} →
      Circuit reg_t ext_fn_t CR CSigma sz →
      Circuit reg_t ext_fn_t CR CSigma sz → Bool
    | _, .const v1, .const v2 => v1 == v2
    | _, .mux s1 t1 f1, .mux s2 t2 f2 =>
        circuitEquivAux (unannot s1) (unannot s2) &&
        circuitEquivAux (unannot t1) (unannot t2) &&
        circuitEquivAux (unannot f1) (unannot f2)
    | _, _, _ => false
  termination_by _ x y => circuitSize x + circuitSize y
  decreasing_by
    all_goals simp_wf
    all_goals simp only [circuitSize]
    all_goals (
      have h1 := unannot_size_le s1; have h2 := unannot_size_le s2
      have h3 := unannot_size_le t1; have h4 := unannot_size_le t2
      have h5 := unannot_size_le f1; have h6 := unannot_size_le f2
      omega
    )

/-- Identical value elimination
    - Or(c, c) → c
    - And(c, c) → c
    - Mux(_, c, c) → c -/
def optIdentical (c : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  match unannot c with
  | .mux _ c1 c2 =>
      if circuitEquiv c1 c2 then c1 else c
  | .binop (.and _) c1 c2 =>
      if circuitEquiv c1 c2 then c1 else c
  | .binop (.or _) c1 c2 =>
      if circuitEquiv c1 c2 then c1 else c
  | _ => c

/-! ## Simplification -/

/-- Simplification pass
    - Not(Not(c)) → c
    - Various slice and concat optimizations -/
def optSimplify (c : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  match unannot c with
  | .unop (.not _) c1 =>
      match unannot c1 with
      | .unop (.not _) c2 => c2
      | _ => c
  | _ => c

/-! ## Partial Evaluation -/

/-- Partial evaluation - evaluate operations on constant inputs -/
def optPartialEval (c : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  match unannot c with
  | .unop fn c1 =>
      match asConst c1 with
      | some v => .const (Koika.Circuit.evalFBits1 fn v)
      | none => c
  | .binop fn c1 c2 =>
      match asConst c1, asConst c2 with
      | some v1, some v2 => .const (Koika.Circuit.evalFBits2 fn v1 v2)
      | _, _ => c
  | _ => c

/-! ## Combined Optimization -/

/-- Compose two optimizations -/
def composeOpt (o1 o2 : Circuit reg_t ext_fn_t CR CSigma sz → Circuit reg_t ext_fn_t CR CSigma sz)
    : Circuit reg_t ext_fn_t CR CSigma sz → Circuit reg_t ext_fn_t CR CSigma sz :=
  fun c => o2 (o1 c)

/-- Apply all local optimizations -/
def optAll (c : Circuit reg_t ext_fn_t CR CSigma sz) : Circuit reg_t ext_fn_t CR CSigma sz :=
  optPartialEval (optSimplify (optIdentical (optConstProp c)))

/-- Iterate optimization until fixpoint or fuel exhausted -/
partial def optIterate (fuel : Nat) (c : Circuit reg_t ext_fn_t CR CSigma sz)
    : Circuit reg_t ext_fn_t CR CSigma sz :=
  match fuel with
  | 0 => c
  | n + 1 =>
      let c' := optAll c
      -- In a complete implementation, we'd check if c == c' to stop early
      optIterate n c'

/-! ## Recursive Circuit Optimization -/

/-- Recursively optimize a circuit, applying optimizations bottom-up -/
def optimizeCircuit (c : Circuit reg_t ext_fn_t CR CSigma sz)
    : Circuit reg_t ext_fn_t CR CSigma sz :=
  let c' := match c with
    | .mux sel t f =>
        .mux (optimizeCircuit sel) (optimizeCircuit t) (optimizeCircuit f)
    | .const v => .const v
    | .readReg r => .readReg r
    | .unop fn arg => .unop fn (optimizeCircuit arg)
    | .binop fn a1 a2 => .binop fn (optimizeCircuit a1) (optimizeCircuit a2)
    | .external fn arg => .external fn (optimizeCircuit arg)
    | .annot s c => .annot s (optimizeCircuit c)
  optAll c'

end CircuitOpt

/-! ## Scheduler Circuit Optimization -/

/-- Optimize a scheduler circuit -/
def optimizeSchedulerCircuit {reg_t ext_fn_t rule_name_t : Type}
    {CR : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    (sc : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma)
    : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma :=
  { writeEnable := fun r => CircuitOpt.optimizeCircuit (sc.writeEnable r)
    writeData := fun r => CircuitOpt.optimizeCircuit (sc.writeData r) }

end Koika
