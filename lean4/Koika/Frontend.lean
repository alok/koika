/-
  Koika/Frontend.lean - Port of coq/Frontend.v
  Top-level module imported by Kôika programs

  Original Coq source: https://github.com/mit-plv/koika/blob/master/coq/Frontend.v
-/

-- Re-export all Koika modules for user programs
import Koika.Types
import Koika.Primitives
import Koika.Syntax
import Koika.SyntaxFunctions
import Koika.Desugaring
import Koika.TypedSyntax
import Koika.TypedSyntaxFunctions
import Koika.TypeInference
import Koika.DSL.Syntax
import Koika.Semantics.Logs
import Koika.Semantics.CompactLogs
import Koika.Semantics.Interp
import Koika.Compile.Lowered
import Koika.Compile.Circuit
import Koika.Compile.CircuitSemantics
import Koika.Compile.Lower
import Koika.Compile.Optimize
import Koika.Backend.Verilog
import Koika.Common
import Koika.Std
import Koika.CPS

namespace Koika

/-! ## Default Position Type -/

/-- Default position type for Kôika programs -/
abbrev pos_t := Unit

/-- Default variable type -/
abbrev var_t := String

/-- Default function name type -/
abbrev fn_name_t := String

/-! ## Type Aliases -/

/-- Untyped action with default type parameters -/
abbrev UActionDefault (reg_t ext_fn_t : Type) :=
  UAction pos_t var_t fn_name_t reg_t ext_fn_t

/-- Typed action with default type parameters -/
abbrev ActionDefault (reg_t ext_fn_t : Type)
    (R : reg_t → Ty) (Sigma : ext_fn_t → ExternalSig)
    (sig : List (String × Ty)) (tau : Ty) :=
  Action reg_t ext_fn_t R Sigma sig tau

/-- Rule (action returning unit) -/
abbrev RuleDefault (reg_t ext_fn_t : Type)
    (R : reg_t → Ty) (Sigma : ext_fn_t → ExternalSig) :=
  Action reg_t ext_fn_t R Sigma [] unitTy

/-- Scheduler with default position type -/
abbrev SchedulerDefault (rule_name_t : Type) :=
  Scheduler Unit rule_name_t

/-! ## DummyPos Class -/

/-- Typeclass for types with a default position value -/
class DummyPos (pos_t : Type) where
  dummyPos : pos_t

instance : DummyPos Unit := ⟨()⟩
instance : DummyPos Path := ⟨.this⟩

end Koika
