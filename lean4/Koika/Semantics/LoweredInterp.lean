/-
  Koika/Semantics/LoweredInterp.lean - Port of coq/LoweredSemantics.v
  Interpreter for lowered (circuit-level) Kôika programs

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/LoweredSemantics.v
-/

import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.Compile.Lowered
import Koika.Semantics.Logs

namespace Koika

/-! ## Lowered Context

A context mapping sizes to BitVec values (type-erased version of TContext).
-/

/-- Lowered context: maps each variable to a bitvector of its size -/
inductive LContext : LSig → Type where
  | empty : LContext []
  | cons : BitVec sz → LContext sig → LContext (sz :: sig)

/-- Get a value from a lowered context -/
def LContext.get : LContext sig → LMember sz sig → BitVec sz
  | .cons v _, .here => v
  | .cons _ ctx, .there m => ctx.get m

/-- Set a value in a lowered context -/
def LContext.set : LContext sig → LMember sz sig → BitVec sz → LContext sig
  | .cons _ ctx, .here, v => .cons v ctx
  | .cons v' ctx, .there m, v => .cons v' (ctx.set m v)

/-- Pop the head of a context (tail operation) -/
def LContext.tail : LContext (sz :: sig) → LContext sig
  | .cons _ ctx => ctx

/-! ## Lowered Interpreter

Interpreter for lowered actions using bitvector operations.
-/

section Interp

variable {reg_t ext_fn_t : Type} [DecidableEq reg_t]
variable (CR : reg_t → Nat)
variable (CSigma : ext_fn_t → CExternalSig)

/-- Register environment for lowered semantics: bitvectors for each register -/
abbrev LRegEnv := (r : reg_t) → BitVec (CR r)

/-- External function implementations (circuit-level) -/
abbrev LExtEnv := (f : ext_fn_t) → BitVec (CSigma f).argSize → BitVec (CSigma f).retSize

/-- Log type specialized to bitvectors -/
abbrev LInterpLog := SimpleLog (fun r => BitVec (CR r))

/-! ## Bitvector Primitive Operations -/

/-- Apply a unary bitvector primitive - using unsafe casts where needed -/
def applyBits1 (fn : Typed.FBits1) (arg : BitVec (Circuit.sig1 fn).1) : BitVec (Circuit.sig1 fn).2 :=
  match fn with
  | .not sz => cast (by rfl) (~~~arg)
  | .sext sz width =>
      cast (by rfl) <|
        if sz ≤ width then
          BitVec.signExtend width arg
        else
          arg
  | .zextL sz width =>
      cast (by rfl) <|
        if sz ≤ width then
          BitVec.zeroExtend width arg
        else
          arg
  | .zextR sz width =>
      cast (by rfl) <|
        if sz ≤ width then
          BitVec.zeroExtend width arg
        else
          arg
  | .repeat sz times => cast (by rfl) (BitVec.replicate times arg)
  | .slice sz offset width => cast (by rfl) (BitVec.extractLsb' offset width arg)
  | .lowered (.ignoreBits _) => 0
  | .lowered (.displayBits _) => 0

/-- Apply a binary bitvector primitive - using unsafe casts where needed -/
def applyBits2 (fn : Typed.FBits2)
    (arg1 : BitVec (Circuit.sig2 fn).1)
    (arg2 : BitVec (Circuit.sig2 fn).2.1)
    : BitVec (Circuit.sig2 fn).2.2 :=
  match fn with
  | .sel sz =>
      cast (by rfl) (BitVec.ofBool (arg1.getLsbD arg2.toNat))
  | .sliceSubst sz offset width =>
      let mask : BitVec sz := (BitVec.allOnes width).zeroExtend sz <<< offset
      cast (by rfl) ((arg1 &&& ~~~mask) ||| ((arg2.zeroExtend sz) <<< offset))
  | .indexedSlice sz width =>
      cast (by rfl) (BitVec.extractLsb' arg2.toNat width arg1)
  | .and sz => cast (by rfl) (arg1 &&& arg2)
  | .or sz => cast (by rfl) (arg1 ||| arg2)
  | .xor sz => cast (by rfl) (arg1 ^^^ arg2)
  | .lsl _ _ => cast (by rfl) (arg1 <<< arg2.toNat)
  | .lsr _ _ => cast (by rfl) (arg1 >>> arg2.toNat)
  | .asr _ _ => cast (by rfl) (arg1.sshiftRight arg2.toNat)
  | .concat sz1 sz2 => cast (by rfl) (arg2 ++ arg1)
  | .plus sz => cast (by rfl) (arg1 + arg2)
  | .minus sz => cast (by rfl) (arg1 - arg2)
  | .mul sz1 sz2 =>
      let prod := arg1.toNat * arg2.toNat
      cast (by rfl) (BitVec.ofNat (sz1 + sz2) prod)
  | .eqBits _ false => cast (by rfl) (BitVec.ofBool (arg1 == arg2))
  | .eqBits _ true => cast (by rfl) (BitVec.ofBool (arg1 != arg2))
  | .compare true .lt _ => cast (by rfl) (BitVec.ofBool (arg1.toInt < arg2.toInt))
  | .compare true .gt _ => cast (by rfl) (BitVec.ofBool (arg1.toInt > arg2.toInt))
  | .compare true .le _ => cast (by rfl) (BitVec.ofBool (arg1.toInt ≤ arg2.toInt))
  | .compare true .ge _ => cast (by rfl) (BitVec.ofBool (arg1.toInt ≥ arg2.toInt))
  | .compare false .lt _ => cast (by rfl) (BitVec.ofBool (arg1.toNat < arg2.toNat))
  | .compare false .gt _ => cast (by rfl) (BitVec.ofBool (arg1.toNat > arg2.toNat))
  | .compare false .le _ => cast (by rfl) (BitVec.ofBool (arg1.toNat ≤ arg2.toNat))
  | .compare false .ge _ => cast (by rfl) (BitVec.ofBool (arg1.toNat ≥ arg2.toNat))

/-- Read a register value -/
def readLReg (env : LRegEnv CR) (schedLog actLog : LInterpLog CR) (port : Port) (r : reg_t)
    : BitVec (CR r) :=
  match port with
  | .p0 => env r
  | .p1 =>
      match (actLog.append schedLog).latestWrite0 r with
      | some v => v
      | none => env r

/-- Interpret a lowered action -/
partial def interpLoweredAction
    (env : LRegEnv CR)
    (extEnv : LExtEnv CSigma)
    (schedLog : LInterpLog CR)
    (actLog : LInterpLog CR)
    (ctx : LContext sig)
    (a : LAction reg_t ext_fn_t CR CSigma sig sz)
    : Option (LInterpLog CR × BitVec sz × LContext sig) :=
  match a with
  | .fail _ => none

  | .var _ m => some (actLog, ctx.get m, ctx)

  | .const v => some (actLog, v, ctx)

  | .assign _ m e =>
      match interpLoweredAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', v, ctx') =>
          some (log', 0, ctx'.set m v)

  | .seq a b =>
      match interpLoweredAction env extEnv schedLog actLog ctx a with
      | none => none
      | some (log', _, ctx') =>
          interpLoweredAction env extEnv schedLog log' ctx' b

  | .bind _ e body =>
      match interpLoweredAction env extEnv schedLog actLog ctx e with
      | none => none
      | some (log', val, ctx') =>
          match interpLoweredAction env extEnv schedLog log' (.cons val ctx') body with
          | none => none
          | some (log'', result, ctx'') =>
              some (log'', result, ctx''.tail)

  | .if cond tbranch fbranch =>
      match interpLoweredAction env extEnv schedLog actLog ctx cond with
      | none => none
      | some (log', condVal, ctx') =>
          -- Check the LSB of the condition bitvector
          if condVal.getLsbD 0 then
            interpLoweredAction env extEnv schedLog log' ctx' tbranch
          else
            interpLoweredAction env extEnv schedLog log' ctx' fbranch

  | .read port r =>
      if schedLog.mayRead port r then
        let val := readLReg CR env schedLog actLog port r
        let log' := actLog.cons r .read port none
        some (log', val, ctx)
      else none

  | .write port r valAction =>
      match interpLoweredAction env extEnv schedLog actLog ctx valAction with
      | none => none
      | some (log', val, ctx') =>
          if schedLog.mayWrite log' port r then
            let log'' := log'.cons r .write port (some val)
            some (log'', 0, ctx')
          else none

  | .unop fn arg =>
      match interpLoweredAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          some (log', applyBits1 fn argVal, ctx')

  | .binop fn arg1 arg2 =>
      match interpLoweredAction env extEnv schedLog actLog ctx arg1 with
      | none => none
      | some (log', arg1Val, ctx') =>
          match interpLoweredAction env extEnv schedLog log' ctx' arg2 with
          | none => none
          | some (log'', arg2Val, ctx'') =>
              some (log'', applyBits2 fn arg1Val arg2Val, ctx'')

  | .extCall fn arg =>
      match interpLoweredAction env extEnv schedLog actLog ctx arg with
      | none => none
      | some (log', argVal, ctx') =>
          some (log', extEnv fn argVal, ctx')

/-- Interpret a lowered rule (closed action returning 0 bits) -/
def interpLRule
    (env : LRegEnv CR)
    (extEnv : LExtEnv CSigma)
    (schedLog : LInterpLog CR)
    (rl : LRule reg_t ext_fn_t CR CSigma)
    : Option (LInterpLog CR) :=
  match interpLoweredAction CR CSigma env extEnv schedLog .empty .empty rl with
  | some (log, _, _) => some log
  | none => none

end Interp

/-! ## Lowered Scheduler Interpretation -/

section Scheduler

variable {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
variable (CR : reg_t → Nat)
variable (CSigma : ext_fn_t → CExternalSig)

/-- Interpret a scheduler with lowered rules -/
partial def interpLScheduler
    (env : LRegEnv CR)
    (extEnv : LExtEnv CSigma)
    (rules : rule_name_t → LRule reg_t ext_fn_t CR CSigma)
    (schedLog : LInterpLog CR)
    (s : Scheduler Unit rule_name_t)
    : LInterpLog CR :=
  match s with
  | .done => schedLog
  | .cons ruleName rest =>
      match interpLRule CR CSigma env extEnv schedLog (rules ruleName) with
      | some ruleLog => interpLScheduler env extEnv rules (ruleLog.append schedLog) rest
      | none => interpLScheduler env extEnv rules schedLog rest  -- Rule failed, continue
  | .try_ ruleName s1 s2 =>
      match interpLRule CR CSigma env extEnv schedLog (rules ruleName) with
      | some ruleLog => interpLScheduler env extEnv rules (ruleLog.append schedLog) s1
      | none => interpLScheduler env extEnv rules schedLog s2
  | .pos _ s => interpLScheduler env extEnv rules schedLog s

/-- Run a complete cycle: interpret scheduler and commit updates -/
def interpLCycle
    (env : LRegEnv CR)
    (extEnv : LExtEnv CSigma)
    (rules : rule_name_t → LRule reg_t ext_fn_t CR CSigma)
    (s : Scheduler Unit rule_name_t)
    : LRegEnv CR :=
  let log := interpLScheduler CR CSigma env extEnv rules .empty s
  commitUpdate env log

end Scheduler

end Koika
