/-
  Koika/Std.lean - Port of coq/Std.v
  Standard library: Maybe, FIFOs, Register Files

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/Std.v
-/

import Koika.Types
import Koika.Syntax
import Koika.Primitives

namespace Koika.Std

/-! ## Maybe Type

A maybe/optional type represented as a struct with valid bit and data.
-/

/-- Create a Maybe struct type for a given element type -/
def MaybeTy (tau : Ty) : Ty :=
  .struct ("maybe_" ++ tau.id) [("valid", .bits 1), ("data", tau)]

/-- Create a valid maybe value -/
def mkValid {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (tau : Ty) (value : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar (.structInit ("maybe_" ++ tau.id) [("valid", .bits 1), ("data", tau)]
    [("valid", .sugar (.constBits 1 1)), ("data", value)])

/-- Create an invalid/empty maybe value -/
def mkInvalid {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (tau : Ty) : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .sugar (.structInit ("maybe_" ++ tau.id) [("valid", .bits 1), ("data", tau)]
    [("valid", .sugar (.constBits 1 0))])

/-! ## FIFO (First-In-First-Out Queue) Types

Standard FIFO interfaces for hardware design.
-/

/-- A simple 1-element FIFO
    - Enqueue on port 1, dequeue on port 0
    - No bypass: cannot enqueue and dequeue in the same cycle -/
structure Fifo1Config where
  /-- Element type stored in the FIFO -/
  elemTy : Ty

/-- Register type for Fifo1 -/
inductive Fifo1Reg where
  | data0
  | valid0
  deriving DecidableEq, Repr, Inhabited

/-- Get the type of a Fifo1 register -/
def Fifo1Reg.ty (cfg : Fifo1Config) : Fifo1Reg → Ty
  | .data0 => cfg.elemTy
  | .valid0 => .bits 1

/-- Get the name of a Fifo1 register -/
def Fifo1Reg.name : Fifo1Reg → String
  | .data0 => "data0"
  | .valid0 => "valid0"

/-- A 1-element FIFO with bypass
    - Enqueue on port 0, dequeue on port 1
    - Bypass: can enqueue and dequeue in the same cycle -/
structure Fifo1BypassConfig where
  /-- Element type stored in the FIFO -/
  elemTy : Ty

/-- Register type for Fifo1Bypass -/
inductive Fifo1BypassReg where
  | data0
  | valid0
  deriving DecidableEq, Repr, Inhabited

/-- Get the type of a Fifo1Bypass register -/
def Fifo1BypassReg.ty (cfg : Fifo1BypassConfig) : Fifo1BypassReg → Ty
  | .data0 => cfg.elemTy
  | .valid0 => .bits 1

/-- Get the name of a Fifo1Bypass register -/
def Fifo1BypassReg.name : Fifo1BypassReg → String
  | .data0 => "data0"
  | .valid0 => "valid0"

/-! ## Register File Types

Register files for storing multiple values indexed by address.
-/

/-- Configuration for a power-of-2 sized register file -/
structure RfPow2Config where
  /-- Log2 of the number of registers -/
  idxSz : Nat
  /-- Element type stored in each register -/
  elemTy : Ty
  /-- Initial value for registers -/
  init : elemTy.denote

/-- Number of registers in a RfPow2 -/
def RfPow2Config.size (cfg : RfPow2Config) : Nat := 2 ^ cfg.idxSz

/-- Register type for RfPow2 -/
structure RfPow2Reg (cfg : RfPow2Config) where
  idx : Fin cfg.size
  deriving DecidableEq, Repr

instance (cfg : RfPow2Config) : Inhabited (RfPow2Reg cfg) where
  default := { idx := ⟨0, by
    simp only [RfPow2Config.size]
    exact Nat.one_le_two_pow⟩ }

/-- Get the type of a RfPow2 register -/
def RfPow2Reg.ty (cfg : RfPow2Config) : RfPow2Reg cfg → Ty
  | _ => cfg.elemTy

/-- Get the name of a RfPow2 register -/
def RfPow2Reg.name (cfg : RfPow2Config) (r : RfPow2Reg cfg) : String :=
  s!"rData_{r.idx.val}"

/-- Configuration for an arbitrary-sized register file -/
structure RfConfig where
  /-- Last index (number of registers is lastIdx + 1) -/
  lastIdx : Nat
  /-- Element type stored in each register -/
  elemTy : Ty
  /-- Initial value for registers -/
  init : elemTy.denote

/-- Number of registers in a Rf -/
def RfConfig.size (cfg : RfConfig) : Nat := cfg.lastIdx + 1

/-- Index size (log2 of lastIdx) for addressing -/
def RfConfig.logSz (cfg : RfConfig) : Nat := Nat.log2 cfg.lastIdx

/-- Register type for Rf -/
structure RfReg (cfg : RfConfig) where
  idx : Fin cfg.size
  deriving DecidableEq, Repr

instance (cfg : RfConfig) : Inhabited (RfReg cfg) :=
  ⟨{ idx := ⟨0, Nat.succ_pos _⟩ }⟩

/-- Get the type of a Rf register -/
def RfReg.ty (cfg : RfConfig) : RfReg cfg → Ty
  | _ => cfg.elemTy

/-- Get the name of a Rf register -/
def RfReg.name (cfg : RfConfig) (r : RfReg cfg) : String :=
  s!"rData_{r.idx.val}"

/-! ## EHR Register File

Register file with Ephemeral History Register semantics for
supporting multiple reads/writes per cycle with well-defined ordering.
-/

/-- Configuration for an EHR register file -/
structure RfEhrConfig where
  /-- Last index (number of registers is lastIdx + 1) -/
  lastIdx : Nat
  /-- Element type stored in each register -/
  elemTy : Ty
  /-- Initial value for registers -/
  init : elemTy.denote

/-- Number of registers in a RfEhr -/
def RfEhrConfig.size (cfg : RfEhrConfig) : Nat := cfg.lastIdx + 1

/-- Index size (log2 of lastIdx) for addressing -/
def RfEhrConfig.logSz (cfg : RfEhrConfig) : Nat := Nat.log2 cfg.lastIdx

/-- Register type for RfEhr -/
structure RfEhrReg (cfg : RfEhrConfig) where
  idx : Fin cfg.size
  deriving DecidableEq, Repr

instance (cfg : RfEhrConfig) : Inhabited (RfEhrReg cfg) :=
  ⟨{ idx := ⟨0, Nat.succ_pos _⟩ }⟩

/-- Get the type of a RfEhr register -/
def RfEhrReg.ty (cfg : RfEhrConfig) : RfEhrReg cfg → Ty
  | _ => cfg.elemTy

/-- Get the name of a RfEhr register -/
def RfEhrReg.name (cfg : RfEhrConfig) (r : RfEhrReg cfg) : String :=
  s!"rData_{r.idx.val}"

/-! ## Utility Functions -/

/-- Sign extension: extend an n-bit value to (m+n) bits -/
def signExtend {pos_t var_t fn_name_t reg_t ext_fn_t : Type}
    (n m : Nat) (arg : UAction pos_t var_t fn_name_t reg_t ext_fn_t)
    : UAction pos_t var_t fn_name_t reg_t ext_fn_t :=
  .unop (.bits1 (.sext (m + n))) arg

/-! ## Enumeration Utilities -/

/-- Generate all registers for a RfPow2 -/
def RfPow2Config.allRegs (cfg : RfPow2Config) : List (RfPow2Reg cfg) :=
  List.finRange cfg.size |>.map fun idx => { idx }

/-- Generate all registers for a Rf -/
def RfConfig.allRegs (cfg : RfConfig) : List (RfReg cfg) :=
  List.finRange cfg.size |>.map fun idx => { idx }

/-- Generate all registers for a RfEhr -/
def RfEhrConfig.allRegs (cfg : RfEhrConfig) : List (RfEhrReg cfg) :=
  List.finRange cfg.size |>.map fun idx => { idx }

/-! ## Empty External Function Type -/

/-- Empty external function type for modules that don't use external functions -/
inductive EmptyExtFn
  deriving DecidableEq, Repr

/-- External function signature for empty type -/
def EmptyExtFn.sig : EmptyExtFn → ExternalSig := fun e => nomatch e

end Koika.Std
