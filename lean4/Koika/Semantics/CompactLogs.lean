/-
  Koika/Semantics/CompactLogs.lean - Port of coq/CompactLogs.v
  Alternative implementation of logs using a compact record-based representation

  Original Coq source: coq/CompactLogs.v
  This provides a more efficient log representation where each register has a single
  LogEntry record tracking all read/write activity, rather than a list of entries.
-/

import Koika.Types

namespace Koika

/-! ## Compact Log Entry Structure -/

/-- A compact log entry recording all read/write activity for a single register.
    Using a structure instead of a list of entries makes queries more efficient.

    Primitive projections (Lean 4 default) make rewriting in may_read/may_write easier. -/
structure CompactLogEntry (T : Type) where
  lread0 : Bool
  lread1 : Bool
  lwrite0 : Option T
  lwrite1 : Option T
  deriving Repr

namespace CompactLogEntry

variable {T : Type}

/-- Empty log entry (no reads or writes) -/
def empty : CompactLogEntry T :=
  { lread0 := false
    lread1 := false
    lwrite0 := none
    lwrite1 := none }

/-- Append two log entries (combine their read/write activity).
    Reads are combined with OR.
    Writes are combined with opt_or (first non-None value wins). -/
def append (l1 l2 : CompactLogEntry T) : CompactLogEntry T :=
  { lread0 := l1.lread0 || l2.lread0
    lread1 := l1.lread1 || l2.lread1
    lwrite0 := l1.lwrite0.or l2.lwrite0  -- opt_or: first non-None wins
    lwrite1 := l1.lwrite1.or l2.lwrite1 }

instance : Inhabited (CompactLogEntry T) := ⟨empty⟩

end CompactLogEntry

/-! ## Compact Log Structure -/

/-- A compact log maps each register to a compact log entry.
    This is the Lean 4 equivalent of Coq's `REnv.(env_t) (fun idx => LogEntry (R idx))`. -/
abbrev CompactLog {reg_t : Type} (R : reg_t → Type) :=
  (r : reg_t) → CompactLogEntry (R r)

namespace CompactLog

variable {reg_t : Type} [DecidableEq reg_t] {R : reg_t → Type}

/-! ## Basic Operations -/

/-- Empty log (no activity on any register) -/
def empty : CompactLog R :=
  fun _ => CompactLogEntry.empty

/-- Append two logs pointwise -/
def append (l1 l2 : CompactLog R) : CompactLog R :=
  fun r => (l1 r).append (l2 r)

instance : Inhabited (CompactLog R) := ⟨empty⟩

/-! ## May Read/Write Predicates -/

/-- May read from port 0: allowed if no writes have occurred -/
def mayRead0 (schedLog : CompactLog R) (idx : reg_t) : Bool :=
  match schedLog idx with
  | { lread0 := _, lread1 := _, lwrite0 := none, lwrite1 := none } => true
  | _ => false

/-- May read from port 1: allowed if no write1 has occurred -/
def mayRead1 (schedLog : CompactLog R) (idx : reg_t) : Bool :=
  match schedLog idx with
  | { lread0 := _, lread1 := _, lwrite0 := _, lwrite1 := none } => true
  | _ => false

/-- May write to port 0: allowed if no read1 or any writes have occurred.
    Checks both the schedule log and the current rule log. -/
def mayWrite0 (schedLog ruleLog : CompactLog R) (idx : reg_t) : Bool :=
  match schedLog idx, ruleLog idx with
  | { lread0 := _, lread1 := false, lwrite0 := none, lwrite1 := none },
    { lread0 := _, lread1 := false, lwrite0 := none, lwrite1 := none } => true
  | _, _ => false

/-- May write to port 1: allowed if no write1 has occurred.
    Checks both the schedule log and the current rule log. -/
def mayWrite1 (schedLog ruleLog : CompactLog R) (idx : reg_t) : Bool :=
  match schedLog idx, ruleLog idx with
  | { lread0 := _, lread1 := _, lwrite0 := _, lwrite1 := none },
    { lread0 := _, lread1 := _, lwrite0 := _, lwrite1 := none } => true
  | _, _ => false

/-! ## Commit Updates -/

/-- Commit log writes to register state.
    Priority: write1 > write0 > original value.
    This implements the write port priority scheme. -/
def commitUpdate (r0 : (r : reg_t) → R r) (log : CompactLog R) : (r : reg_t) → R r :=
  fun k =>
    let entry := log k
    match entry.lwrite1, entry.lwrite0 with
    | some v, _ => v      -- Port 1 write has priority
    | _, some v => v      -- Port 0 write if no port 1
    | none, none => r0 k  -- No writes, keep original value

end CompactLog

/-! ## Convenience Aliases -/

/-- Compact log with type-level values (type_denote) -/
abbrev Log {reg_t : Type} (R : reg_t → Ty) :=
  CompactLog fun idx => (R idx).denote

/-- Compact log with bit-level values (for circuit compilation) -/
abbrev CLog {reg_t : Type} (R : reg_t → Nat) :=
  CompactLog fun idx => BitVec (R idx)

end Koika
