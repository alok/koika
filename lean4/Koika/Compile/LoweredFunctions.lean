/-
  Koika/Compile/LoweredFunctions.lean - Port of coq/LoweredSyntaxFunctions.v
  Analysis functions defined on lowered ASTs

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/LoweredSyntaxFunctions.v
-/

import Koika.Compile.Lowered
import Koika.Types
import Koika.Syntax

namespace Koika.Compile.LoweredFunctions

/-! ## Read/Write Event Type -/

/-- Read or write event type for register access tracking -/
inductive LRW where
  | read
  | write
  deriving DecidableEq, Repr, BEq

/-- An event is a read/write tag combined with a port -/
abbrev Event := LRW × Port

/-! ## Action Footprint Analysis -/

/-- A footprint entry: register and the event (read/write + port) -/
abbrev FootprintEntry (reg_t : Type) := reg_t × Event

/-- Footprint type: list of register accesses with their events -/
abbrev Footprint (reg_t : Type) := List (FootprintEntry reg_t)

variable {reg_t ext_fn_t : Type}
variable {R : reg_t → Nat}
variable {CSigma : ext_fn_t → CExternalSig}

/-- Accumulate the footprint of a lowered action.
    Collects all register reads/writes with their ports. -/
def actionFootprint' : (acc : Footprint reg_t) →
    LAction reg_t ext_fn_t R CSigma sig sz → Footprint reg_t
  | acc, .fail _ => acc
  | acc, .var _ _ => acc
  | acc, .const _ => acc
  | acc, .assign _ _ ex => actionFootprint' acc ex
  | acc, .seq r1 r2 => actionFootprint' (actionFootprint' acc r1) r2
  | acc, .bind _ ex body => actionFootprint' (actionFootprint' acc ex) body
  | acc, .«if» cond tbranch fbranch =>
      actionFootprint' (actionFootprint' (actionFootprint' acc cond) tbranch) fbranch
  | acc, .read port reg => (reg, (.read, port)) :: acc
  | acc, .write port reg value => actionFootprint' ((reg, (.write, port)) :: acc) value
  | acc, .unop _ arg => actionFootprint' acc arg
  | acc, .binop _ arg1 arg2 => actionFootprint' (actionFootprint' acc arg1) arg2
  | acc, .extCall _ arg => actionFootprint' acc arg

/-- Get the complete footprint of a lowered action -/
def actionFootprint : LAction reg_t ext_fn_t R CSigma sig sz → Footprint reg_t :=
  actionFootprint' []

/-! ## Register List Extraction -/

/-- Remove duplicates from a list, preserving order of first occurrence.
    Uses an accumulator for tail recursion. -/
def dedup [DecidableEq α] : List α → List α → List α
  | acc, [] => acc
  | acc, a :: l =>
      let alreadySeen := a ∈ acc
      let acc := if alreadySeen then acc else a :: acc
      dedup acc l

/-- Get the list of unique registers accessed by an action -/
def actionRegisters [DecidableEq reg_t] :
    LAction reg_t ext_fn_t R CSigma sig sz → List reg_t :=
  fun a => dedup [] (actionFootprint a |>.map (·.1))

/-! ## Scheduler Path Enumeration -/

/-- Enumerate all possible execution paths through a scheduler.
    Each path is a list of rule names in execution order. -/
def allSchedulerPaths {pos_t rule_name_t : Type} :
    Scheduler pos_t rule_name_t → List (List rule_name_t)
  | .done => [[]]
  | .cons r s =>
      let paths := allSchedulerPaths s
      paths.map (fun rs => r :: rs)
  | .try_ r s1 s2 =>
      let paths1 := allSchedulerPaths s1
      let paths2 := allSchedulerPaths s2
      (paths1.map (fun rs => r :: rs)) ++ (paths2.map (fun rs => r :: rs))
  | .pos _ s => allSchedulerPaths s

/-! ## Register Access Classification -/

/-- Classification of rules by register access pattern.
    For dependency analysis, we track:
    - Rules that read from a register on port 1
    - Rules that write to a register on port 0
-/
structure RegRules (rule_name_t : Type) where
  /-- Rules that read this register on port 1 -/
  rrRead1 : List rule_name_t := []
  /-- Rules that write this register on port 0 -/
  rrWrite0 : List rule_name_t := []
  deriving Repr

namespace RegRules

/-- Add a rule to the read1 list -/
def addRead1 {rule_name_t : Type} (rr : RegRules rule_name_t) (rl : rule_name_t) :
    RegRules rule_name_t :=
  { rr with rrRead1 := rl :: rr.rrRead1 }

/-- Add a rule to the write0 list -/
def addWrite0 {rule_name_t : Type} (rr : RegRules rule_name_t) (rl : rule_name_t) :
    RegRules rule_name_t :=
  { rr with rrWrite0 := rl :: rr.rrWrite0 }

end RegRules

/-! ## Rules-by-Register Map

In the Coq version, this uses an `Env` typeclass to provide a map from registers to values.
In Lean 4, we use a simple function type `reg_t → α` which is more direct.
-/

/-- A map from registers to register rule classifications -/
abbrev RegRulesMap (reg_t rule_name_t : Type) := reg_t → RegRules rule_name_t

/-- Compute which rules access each register and how.
    Takes a list of (rule_name, footprint) pairs and returns a map
    from registers to the rules that read/write them. -/
def computeRulesByRegisters {reg_t rule_name_t : Type} [DecidableEq reg_t]
    (footprints : List (rule_name_t × Footprint reg_t)) :
    RegRulesMap reg_t rule_name_t :=
  -- Initialize the map with empty rule lists for all registers
  let initMap : RegRulesMap reg_t rule_name_t := fun _ => {}
  -- Fold over all (rule, footprint) pairs
  footprints.foldl
    (fun (rbr : RegRulesMap reg_t rule_name_t) (rl, actionFootprint) =>
      -- For each footprint entry in this rule
      actionFootprint.foldl
        (fun (rbr : RegRulesMap reg_t rule_name_t) (reg, evtPort) =>
          match evtPort with
          | (.read, .p1) =>
              -- Update the map at `reg` to add this rule to read1 list
              fun r => if r == reg then (rbr reg).addRead1 rl else rbr r
          | (.write, .p0) =>
              -- Update the map at `reg` to add this rule to write0 list
              fun r => if r == reg then (rbr reg).addWrite0 rl else rbr r
          | _ => rbr)
        rbr)
    initMap

/-! ## Dependency Graph Construction -/

/-- An edge in the dependency graph represents a dependency between two rules -/
abbrev Edge (rule_name_t : Type) := rule_name_t × rule_name_t

/-- Add footprint information to a path by looking up each rule -/
def addFootprints {reg_t ext_fn_t rule_name_t : Type}
    {R : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    (rules : rule_name_t → LRule reg_t ext_fn_t R CSigma)
    (path : List rule_name_t) :
    List (rule_name_t × Footprint reg_t) :=
  path.map fun rl => (rl, actionFootprint (rules rl))

/-- Find all dependencies for a single register's rules.
    For each rule that reads the register (on port 1), and each rule that
    writes the register (on port 0), add an edge from writer to reader. -/
def findDependencies {rule_name_t : Type} (regRules : RegRules rule_name_t) :
    List (Edge rule_name_t) :=
  regRules.rrRead1.foldl
    (fun deps rlR1 =>
      regRules.rrWrite0.foldl
        (fun deps rlW0 =>
          (rlW0, rlR1) :: deps)
        deps)
    []

/-- Compute the dependency graph for a single path through the scheduler.
    Returns a list of (register, edges) pairs showing which rules depend on
    which other rules through each register. -/
def pathDependencyGraph {reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
    {R : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    (rules : rule_name_t → LRule reg_t ext_fn_t R CSigma)
    (path : List rule_name_t) :
    List (reg_t × List (Edge rule_name_t)) :=
  -- Get footprints for all rules in the path
  let pathWithFootprints := addFootprints rules path
  -- Compute rules by register
  let rulesByRegister := computeRulesByRegisters pathWithFootprints
  -- Get all registers mentioned in this path
  let regs := pathWithFootprints.foldl
    (fun acc (_, fp) => acc ++ fp.map (·.1))
    []
  let uniqueRegs := dedup [] regs
  -- For each register, compute its dependencies
  uniqueRegs.map fun reg =>
    (reg, findDependencies (rulesByRegister reg))

/-- Compute dependency graphs for all paths through a scheduler.
    Each path gets its own dependency graph showing rule dependencies. -/
def dependencyGraph {pos_t reg_t ext_fn_t rule_name_t : Type} [DecidableEq reg_t]
    {R : reg_t → Nat} {CSigma : ext_fn_t → CExternalSig}
    (rules : rule_name_t → LRule reg_t ext_fn_t R CSigma)
    (s : Scheduler pos_t rule_name_t) :
    List (List (reg_t × List (Edge rule_name_t))) :=
  let paths := allSchedulerPaths s
  paths.map (pathDependencyGraph rules)

end Koika.Compile.LoweredFunctions
