/-
  Koika/Compile/Circuit.lean - Port of coq/CircuitSyntax.v
  Circuit/RTL syntax for hardware representation
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.Compile.Lowered

namespace Koika

/-! ## Read/Write Data Fields -/

/-- Fields in read/write data structure -/
inductive RWDataField where
  | r0     -- read on port 0
  | r1     -- read on port 1
  | w0     -- write on port 0
  | w1     -- write on port 1
  | data0  -- data for port 0
  | data1  -- data for port 1
  deriving DecidableEq, Repr, BEq

/-- Fields in the circuit structure -/
inductive CircuitField (reg_t : Type) where
  | rwdata (r : reg_t) (field : RWDataField)
  | canfire
  deriving Repr

/-! ## Circuit Syntax -/

/-- Circuit (RTL) representation.
    Circuits are combinational logic with references to registers. -/
inductive Circuit (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    : Nat → Type where
  | mux : Circuit reg_t ext_fn_t CR CSigma 1 →
          Circuit reg_t ext_fn_t CR CSigma sz →
          Circuit reg_t ext_fn_t CR CSigma sz →
          Circuit reg_t ext_fn_t CR CSigma sz
  | const : BitVec sz → Circuit reg_t ext_fn_t CR CSigma sz
  | readReg : (reg : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR reg)
  | unop : (fn : Typed.FBits1) →
           Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig1 fn).1 →
           Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig1 fn).2
  | binop : (fn : Typed.FBits2) →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).1 →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).2.1 →
            Circuit reg_t ext_fn_t CR CSigma (Koika.Circuit.sig2 fn).2.2
  | external : (fn : ext_fn_t) →
               Circuit reg_t ext_fn_t CR CSigma (CSigma fn).argSize →
               Circuit reg_t ext_fn_t CR CSigma (CSigma fn).retSize
  | annot : String → Circuit reg_t ext_fn_t CR CSigma sz →
            Circuit reg_t ext_fn_t CR CSigma sz

/-! ## Circuit Smart Constructors -/

namespace Circuit

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Constant zero -/
def zero : Circuit reg_t ext_fn_t CR CSigma sz :=
  .const 0

/-- Constant one (for 1-bit circuits) -/
def one : Circuit reg_t ext_fn_t CR CSigma 1 :=
  .const 1

/-- AND gate (for 1-bit circuits) -/
def and1 (a b : Circuit reg_t ext_fn_t CR CSigma 1) : Circuit reg_t ext_fn_t CR CSigma 1 :=
  .binop (.and 1) a b

/-- OR gate (for 1-bit circuits) -/
def or1 (a b : Circuit reg_t ext_fn_t CR CSigma 1) : Circuit reg_t ext_fn_t CR CSigma 1 :=
  .binop (.or 1) a b

/-- NOT gate (for 1-bit circuits) -/
def not1 (a : Circuit reg_t ext_fn_t CR CSigma 1) : Circuit reg_t ext_fn_t CR CSigma 1 :=
  .unop (.not 1) a

/-- Implies: a → b = ¬a ∨ b -/
def implies (a b : Circuit reg_t ext_fn_t CR CSigma 1) : Circuit reg_t ext_fn_t CR CSigma 1 :=
  or1 (not1 a) b

end Circuit

/-! ## Circuit Primitive Evaluation -/

namespace Circuit

/-- Evaluate a unary circuit primitive on a bitvector -/
def evalFBits1 (fn : Typed.FBits1) (v : BitVec (Koika.Circuit.sig1 fn).1)
    : BitVec (Koika.Circuit.sig1 fn).2 :=
  match fn with
  | .not _sz => ~~~v
  | .sext sz width => v.signExtend (max sz width)
  | .zextL sz width => v.zeroExtend (max sz width)
  | .zextR sz width => (v.zeroExtend (max sz width)) <<< (max sz width - sz)
  | .repeat sz times => (BitVec.replicate times v).cast (Nat.mul_comm sz times)
  | .slice _sz offset width => v.extractLsb' offset width
  | .lowered (.ignoreBits _sz) => 0
  | .lowered (.displayBits _) => 0

/-- Evaluate a binary circuit primitive on bitvectors -/
def evalFBits2 : (fn : Typed.FBits2) →
    (v1 : BitVec (Koika.Circuit.sig2 fn).1) →
    (v2 : BitVec (Koika.Circuit.sig2 fn).2.1) →
    BitVec (Koika.Circuit.sig2 fn).2.2
  | .and sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      (v1' &&& v2').cast rfl
  | .or sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      (v1' ||| v2').cast rfl
  | .xor sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      (v1' ^^^ v2').cast rfl
  | .lsl bitsSz _shiftSz, v1, v2 =>
      let v1' : BitVec bitsSz := v1.cast rfl
      (v1' <<< v2.toNat).cast rfl
  | .lsr bitsSz _shiftSz, v1, v2 =>
      let v1' : BitVec bitsSz := v1.cast rfl
      (v1' >>> v2.toNat).cast rfl
  | .asr bitsSz _shiftSz, v1, v2 =>
      let v1' : BitVec bitsSz := v1.cast rfl
      (v1'.sshiftRight v2.toNat).cast rfl
  | .concat sz1 sz2, v1, v2 =>
      let v1' : BitVec sz1 := v1.cast rfl
      let v2' : BitVec sz2 := v2.cast rfl
      -- Append produces sz1 + sz2, but sig2 expects sz2 + sz1
      (v1' ++ v2').cast (Nat.add_comm sz1 sz2)
  | .sel sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      BitVec.ofBool (v1'.getLsbD v2.toNat)
  | .sliceSubst sz offset width, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec width := v2.cast rfl
      let mask : BitVec sz := (BitVec.allOnes width).zeroExtend sz <<< offset
      let clearedV1 := v1' &&& ~~~mask
      let shiftedV2 := (v2'.zeroExtend sz) <<< offset
      (clearedV1 ||| shiftedV2).cast rfl
  | .indexedSlice sz width, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      (v1'.extractLsb' v2.toNat width).cast rfl
  | .plus sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      (v1' + v2').cast rfl
  | .minus sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      (v1' - v2').cast rfl
  | .mul sz1 sz2, v1, v2 =>
      let v1' : BitVec sz1 := v1.cast rfl
      let v2' : BitVec sz2 := v2.cast rfl
      (v1'.zeroExtend (sz1 + sz2) * v2'.zeroExtend (sz1 + sz2)).cast rfl
  | .eqBits sz negate, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      let eq := v1' == v2'
      BitVec.ofBool (if negate then !eq else eq)
  | .compare signed cmp sz, v1, v2 =>
      let v1' : BitVec sz := v1.cast rfl
      let v2' : BitVec sz := v2.cast rfl
      let result := match cmp with
        | .lt => if signed then BitVec.slt v1' v2' else v1' < v2'
        | .le => if signed then BitVec.sle v1' v2' else v1' ≤ v2'
        | .gt => if signed then BitVec.slt v2' v1' else v2' < v1'
        | .ge => if signed then BitVec.sle v2' v1' else v2' ≤ v1'
      BitVec.ofBool result

end Circuit

/-! ## Read/Write Data Structures -/

/-- Read/write data for a single register -/
structure RWData (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    (sz : Nat) where
  read0 : Circuit reg_t ext_fn_t CR CSigma 1
  read1 : Circuit reg_t ext_fn_t CR CSigma 1
  write0 : Circuit reg_t ext_fn_t CR CSigma 1
  write1 : Circuit reg_t ext_fn_t CR CSigma 1
  data0 : Circuit reg_t ext_fn_t CR CSigma sz
  data1 : Circuit reg_t ext_fn_t CR CSigma sz

/-- Create initial RWData for a register -/
def RWData.init {reg_t ext_fn_t : Type}
    {CR : reg_t → Nat}
    {CSigma : ext_fn_t → CExternalSig}
    (sz : Nat) : RWData reg_t ext_fn_t CR CSigma sz :=
  { read0 := .const 0
    read1 := .const 0
    write0 := .const 0
    write1 := .const 0
    data0 := .const 0
    data1 := .const 0 }

/-! ## Action Circuit Result -/

/-- Result of compiling an action to a circuit -/
structure ActionCircuit (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    (sz : Nat) where
  canfire : Circuit reg_t ext_fn_t CR CSigma 1
  value : Circuit reg_t ext_fn_t CR CSigma sz
  rwdata : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)

/-! ## Rule/Scheduler Circuit -/

/-- Result of compiling a scheduler to circuits -/
structure SchedulerCircuit (reg_t ext_fn_t rule_name_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig) where
  /-- Final write enable for each register -/
  writeEnable : reg_t → Circuit reg_t ext_fn_t CR CSigma 1
  /-- Final write data for each register -/
  writeData : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r)

instance {reg_t ext_fn_t rule_name_t : Type}
    {CR : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    : Nonempty (SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma) :=
  ⟨{ writeEnable := fun _ => .const 0
     writeData := fun _ => .const 0 }⟩

/-! ## Circuit Context -/

/-- Circuit context: maps variable sizes to circuits -/
inductive CContext (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig)
    : LSig → Type where
  | empty : CContext reg_t ext_fn_t CR CSigma []
  | cons : Circuit reg_t ext_fn_t CR CSigma sz →
           CContext reg_t ext_fn_t CR CSigma sig →
           CContext reg_t ext_fn_t CR CSigma (sz :: sig)

namespace CContext

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Get a circuit from the context -/
def get : CContext reg_t ext_fn_t CR CSigma sig → LMember sz sig →
          Circuit reg_t ext_fn_t CR CSigma sz
  | .cons c _, .here => c
  | .cons _ ctx, .there m => ctx.get m

/-- Set a circuit in the context -/
def set : CContext reg_t ext_fn_t CR CSigma sig → LMember sz sig →
          Circuit reg_t ext_fn_t CR CSigma sz → CContext reg_t ext_fn_t CR CSigma sig
  | .cons _ ctx, .here, c => .cons c ctx
  | .cons c' ctx, .there m, c => .cons c' (ctx.set m c)

/-- Mux two contexts based on a condition -/
def mux (cond : Circuit reg_t ext_fn_t CR CSigma 1)
    : CContext reg_t ext_fn_t CR CSigma sig →
      CContext reg_t ext_fn_t CR CSigma sig →
      CContext reg_t ext_fn_t CR CSigma sig
  | .empty, .empty => .empty
  | .cons ct ctxT, .cons cf ctxF =>
      .cons (.mux cond ct cf) (mux cond ctxT ctxF)

end CContext

/-! ## RWCircuit: Intermediate Compilation State -/

/-- Intermediate state during action compilation -/
structure RWCircuit (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat)
    (CSigma : ext_fn_t → CExternalSig) where
  canFire : Circuit reg_t ext_fn_t CR CSigma 1
  rwdata : (r : reg_t) → RWData reg_t ext_fn_t CR CSigma (CR r)

namespace RWCircuit

variable {reg_t ext_fn_t : Type}
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Initial RWCircuit with canFire=1 and no reads/writes -/
def init : RWCircuit reg_t ext_fn_t CR CSigma :=
  { canFire := .const 1
    rwdata := fun r => RWData.init (CR r) }

/-- Mux two RWCircuits based on a condition -/
def mux (cond : Circuit reg_t ext_fn_t CR CSigma 1)
    (t f : RWCircuit reg_t ext_fn_t CR CSigma) : RWCircuit reg_t ext_fn_t CR CSigma :=
  { canFire := .mux cond t.canFire f.canFire
    rwdata := fun r =>
      { read0 := .mux cond (t.rwdata r).read0 (f.rwdata r).read0
        read1 := .mux cond (t.rwdata r).read1 (f.rwdata r).read1
        write0 := .mux cond (t.rwdata r).write0 (f.rwdata r).write0
        write1 := .mux cond (t.rwdata r).write1 (f.rwdata r).write1
        data0 := .mux cond (t.rwdata r).data0 (f.rwdata r).data0
        data1 := .mux cond (t.rwdata r).data1 (f.rwdata r).data1 } }

end RWCircuit

/-! ## Action Compilation -/

/-- Result of compiling an action -/
structure CompileResult (reg_t ext_fn_t : Type)
    (CR : reg_t → Nat) (CSigma : ext_fn_t → CExternalSig)
    (sig : LSig) (sz : Nat) where
  retVal : Circuit reg_t ext_fn_t CR CSigma sz
  rwc : RWCircuit reg_t ext_fn_t CR CSigma
  ctx : CContext reg_t ext_fn_t CR CSigma sig

/-- Default CContext for any signature -/
def CContext.default {reg_t ext_fn_t : Type}
    {CR : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    : (sig : LSig) → CContext reg_t ext_fn_t CR CSigma sig
  | [] => .empty
  | _sz :: rest => .cons (.const 0) (CContext.default rest)

instance {reg_t ext_fn_t : Type} {CR : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    {sig : LSig} {sz : Nat}
    : Nonempty (CompileResult reg_t ext_fn_t CR CSigma sig sz) :=
  ⟨{ retVal := .const 0
     rwc := RWCircuit.init
     ctx := CContext.default sig }⟩

namespace CompileAction

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (CR : reg_t → Nat)
variable (CSigma : ext_fn_t → CExternalSig)
variable (regCircuits : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r))

open Circuit in
/-- Compile a lowered action to a circuit -/
partial def compileAction
    (ctx : CContext reg_t ext_fn_t CR CSigma sig)
    (rwc : RWCircuit reg_t ext_fn_t CR CSigma)
    (a : LAction reg_t ext_fn_t CR CSigma sig sz)
    : CompileResult reg_t ext_fn_t CR CSigma sig sz :=
  match a with
  | .fail sz =>
      { retVal := .const 0
        rwc := { rwc with canFire := .const 0 }
        ctx := ctx }
  | .var _ m =>
      { retVal := ctx.get m
        rwc := rwc
        ctx := ctx }
  | .const v =>
      { retVal := .const v
        rwc := rwc
        ctx := ctx }
  | .assign _ m e =>
      let r := compileAction ctx rwc e
      { retVal := .const 0
        rwc := r.rwc
        ctx := r.ctx.set m r.retVal }
  | .seq a b =>
      let ra := compileAction ctx rwc a
      compileAction ra.ctx ra.rwc b
  | .bind _ e body =>
      let re := compileAction ctx rwc e
      let rbody := compileAction (.cons re.retVal re.ctx) re.rwc body
      match rbody.ctx with
      | .cons _ ctx' =>
          { retVal := rbody.retVal
            rwc := rbody.rwc
            ctx := ctx' }
  | .if cond tbranch fbranch =>
      let rc := compileAction ctx rwc cond
      let rt := compileAction rc.ctx rc.rwc tbranch
      let rf := compileAction rc.ctx rc.rwc fbranch
      let condVal := rc.retVal
      { retVal := .mux condVal rt.retVal rf.retVal
        rwc := RWCircuit.mux condVal rt.rwc rf.rwc
        ctx := CContext.mux condVal rt.ctx rf.ctx }
  | .read port r =>
      let reg := rwc.rwdata r
      match port with
      | .p0 =>
          let newReg := { reg with read0 := .const 1 }
          { retVal := regCircuits r
            rwc := { rwc with rwdata := fun r' => if h : r' = r then h ▸ newReg else rwc.rwdata r' }
            ctx := ctx }
      | .p1 =>
          let newReg := { reg with read1 := .const 1 }
          { retVal := reg.data0
            rwc := { rwc with rwdata := fun r' => if h : r' = r then h ▸ newReg else rwc.rwdata r' }
            ctx := ctx }
  | .write port r valAction =>
      let rv := compileAction ctx rwc valAction
      let reg := rv.rwc.rwdata r
      match port with
      | .p0 =>
          let canWrite := and1 (and1 (not1 reg.read1) (not1 reg.write0)) (not1 reg.write1)
          let newCanFire := and1 rv.rwc.canFire canWrite
          let newReg := { reg with write0 := .const 1, data0 := rv.retVal }
          { retVal := .const 0
            rwc := { canFire := newCanFire
                     rwdata := fun r' => if h : r' = r then h ▸ newReg else rv.rwc.rwdata r' }
            ctx := rv.ctx }
      | .p1 =>
          let canWrite := not1 reg.write1
          let newCanFire := and1 rv.rwc.canFire canWrite
          let newReg := { reg with write1 := .const 1, data1 := rv.retVal }
          { retVal := .const 0
            rwc := { canFire := newCanFire
                     rwdata := fun r' => if h : r' = r then h ▸ newReg else rv.rwc.rwdata r' }
            ctx := rv.ctx }
  | .unop fn arg =>
      let ra := compileAction ctx rwc arg
      { retVal := .unop fn ra.retVal
        rwc := ra.rwc
        ctx := ra.ctx }
  | .binop fn arg1 arg2 =>
      let r1 := compileAction ctx rwc arg1
      let r2 := compileAction r1.ctx r1.rwc arg2
      { retVal := .binop fn r1.retVal r2.retVal
        rwc := r2.rwc
        ctx := r2.ctx }
  | .extCall fn arg =>
      let ra := compileAction ctx rwc arg
      { retVal := .external fn ra.retVal
        rwc := ra.rwc
        ctx := ra.ctx }

/-- Compile a lowered rule -/
def compileRule (rl : LRule reg_t ext_fn_t CR CSigma)
    : RWCircuit reg_t ext_fn_t CR CSigma :=
  let result : CompileResult reg_t ext_fn_t CR CSigma [] 0 :=
    compileAction CR CSigma regCircuits CContext.empty RWCircuit.init rl
  result.rwc

end CompileAction

/-! ## Scheduler Compilation -/

namespace SchedulerCompile

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable {CR : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

open Circuit CompileAction

/-- Check if a rule will fire given current accumulated state -/
def willFire (ruleRwc _accRwc : RWCircuit reg_t ext_fn_t CR CSigma)
    : Circuit reg_t ext_fn_t CR CSigma 1 :=
  ruleRwc.canFire  -- Simplified

/-- Merge rule RW data into accumulated state when rule fires -/
def mergeRWData (wf : Circuit reg_t ext_fn_t CR CSigma 1)
    (ruleRwc accRwc : RWCircuit reg_t ext_fn_t CR CSigma)
    : RWCircuit reg_t ext_fn_t CR CSigma :=
  { canFire := .const 1
    rwdata := fun r =>
      let ruleReg := ruleRwc.rwdata r
      let accReg := accRwc.rwdata r
      { read0 := .mux wf (or1 ruleReg.read0 accReg.read0) accReg.read0
        read1 := .mux wf (or1 ruleReg.read1 accReg.read1) accReg.read1
        write0 := .mux wf (or1 ruleReg.write0 accReg.write0) accReg.write0
        write1 := .mux wf (or1 ruleReg.write1 accReg.write1) accReg.write1
        data0 := .mux wf ruleReg.data0 accReg.data0
        data1 := .mux wf ruleReg.data1 accReg.data1 } }

/-- Initial accumulated RW state -/
def initAcc (regCircuits : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r))
    : RWCircuit reg_t ext_fn_t CR CSigma :=
  { canFire := .const 1
    rwdata := fun r =>
      { read0 := .const 0
        read1 := .const 0
        write0 := .const 0
        write1 := .const 0
        data0 := regCircuits r
        data1 := regCircuits r } }

/-- Compile a scheduler to a final circuit -/
partial def go
    (CR : reg_t → Nat) (CSigma : ext_fn_t → CExternalSig)
    (regCircuits : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r))
    (rules : rule_name_t → LRule reg_t ext_fn_t CR CSigma)
    (acc : RWCircuit reg_t ext_fn_t CR CSigma)
    (s : Scheduler Unit rule_name_t)
    : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma :=
  match s with
  | .done =>
      { writeEnable := fun r => (acc.rwdata r).write0
        writeData := fun r => (acc.rwdata r).data0 }
  | .cons ruleName rest =>
      let rl := rules ruleName
      let ruleRwc := compileRule CR CSigma regCircuits rl
      let wf := willFire ruleRwc acc
      let newAcc := mergeRWData wf ruleRwc acc
      go CR CSigma regCircuits rules newAcc rest
  | .try_ ruleName s1 s2 =>
      let rl := rules ruleName
      let ruleRwc := compileRule CR CSigma regCircuits rl
      let wf := willFire ruleRwc acc
      let accIfFired := mergeRWData wf ruleRwc acc
      let r1 := go CR CSigma regCircuits rules accIfFired s1
      let r2 := go CR CSigma regCircuits rules acc s2
      { writeEnable := fun r => .mux wf (r1.writeEnable r) (r2.writeEnable r)
        writeData := fun r => .mux wf (r1.writeData r) (r2.writeData r) }
  | .pos _ rest => go CR CSigma regCircuits rules acc rest

end SchedulerCompile

/-- Compile a scheduler to circuits -/
def compileScheduler {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
    (CR : reg_t → Nat) (CSigma : ext_fn_t → CExternalSig)
    (regCircuits : (r : reg_t) → Circuit reg_t ext_fn_t CR CSigma (CR r))
    (rules : rule_name_t → LRule reg_t ext_fn_t CR CSigma)
    (s : Scheduler Unit rule_name_t)
    : SchedulerCircuit reg_t ext_fn_t rule_name_t CR CSigma :=
  SchedulerCompile.go CR CSigma regCircuits rules (SchedulerCompile.initAcc regCircuits) s

end Koika
