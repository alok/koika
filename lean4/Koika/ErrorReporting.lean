/-
  Koika/ErrorReporting.lean - Port of coq/ErrorReporting.v
  Type checking errors and error-reporting functions
-/

import Koika.Types
import Koika.Syntax

namespace Koika

/-! ## Result Type for Type Checking

A simple Either-style result type for type checking operations.
-/

inductive Result (S F : Type) where
  | success (s : S)
  | failure (f : F)
  deriving Repr

/-- Map a function over the failure case -/
def Result.mapFailure {S F1 F2 : Type} (fn : F1 → F2) (r : Result S F1) : Result S F2 :=
  match r with
  | .success s => .success s
  | .failure f => .failure (fn f)

/-- Bind operation for Result -/
def Result.bind {S F A : Type} (r : Result S F) (f : S → Result A F) : Result A F :=
  match r with
  | .success s => f s
  | .failure e => .failure e

/-- Map over success case -/
def Result.map {S F A : Type} (f : S → A) (r : Result S F) : Result A F :=
  match r with
  | .success s => .success (f s)
  | .failure e => .failure e

instance : Functor (Result · F) where
  map := Result.map

instance : Monad (Result · F) where
  pure := Result.success
  bind := Result.bind

/-! ## Function Type Checking Error

Type alias for function type checking errors using types from Syntax.lean
-/

/-- Type checking error for function arguments -/
abbrev FnTcError := FnTcErrorLoc × BasicErrorMsg

/-! ## Kind Assertion

Assert that a type has a particular kind and extract the relevant information.
-/

/-- Assert that a type has the expected kind and extract relevant data.

For example:
- `assertKind .bits arg ty` checks if `ty` is a bits type and returns the size
- `assertKind .enum arg ty` checks if `ty` is an enum and returns the signature
-/
def assertKind (kind : TyKind) (arg : FnTcErrorLoc) (tau : Ty) :
    Result (match kind with
            | .bits => Nat
            | .enum => EnumSig
            | .struct => String × List (String × Ty)
            | .array => Ty × Nat) FnTcError :=
  match kind, tau with
  | .bits, .bits sz => .success sz
  | .enum, .enum sg => .success sg
  | .struct, .struct name fields => .success (name, fields)
  | .array, .array elemType len => .success (elemType, len)
  | _, _ => .failure (arg, .kindMismatch tau.kind kind)

/-! ## Error Source

ErrorSource lives in Prop because it's only useful in interactive mode.
The Lispy Verilog frontend only cares about positions.

Note: Syntax.lean already defines `Error` structure with pos and msg.
This adds the ErrorSource concept which is used in the Coq version.
-/

/-- Source of an error (for interactive debugging) -/
inductive ErrorSource : Prop where
  | errSrc {T : Type} (t : T)

/-! ## Extended Error with Source

The basic Error type from Syntax.lean has pos and msg.
This extended version adds an optional source field for debugging.
-/

/-- Complete error with position, message, and source -/
structure ErrorWithSource (pos_t var_t fn_name_t : Type) extends Error pos_t var_t fn_name_t where
  source : ErrorSource := .errSrc ()
  deriving Repr

/-! ## Error Formatting Helpers

Utilities for formatting error messages (can be extended as needed).
-/

/-- Format a basic error message -/
def BasicErrorMsg.format : BasicErrorMsg → String
  | .outOfBounds pos elemType len =>
      s!"Array index {pos} out of bounds for array of length {len} with element type {repr elemType}"
  | .unboundField f structName =>
      s!"Unbound field '{f}' in struct '{structName}'"
  | .typeMismatch actual expected =>
      s!"Type mismatch: expected {repr expected}, but got {repr actual}"
  | .kindMismatch actual expected =>
      s!"Kind mismatch: expected {repr expected}, but got {repr actual}"

/-- Format an error message -/
def ErrorMsg.format {var_t fn_name_t : Type} [Repr var_t] [Repr fn_name_t] :
    ErrorMsg var_t fn_name_t → String
  | .explicitErrorInAst =>
      "Explicit error node in AST"
  | .sugaredConstructorInAst =>
      "Sugared constructor found in AST (should have been desugared)"
  | .unboundVariable var =>
      s!"Unbound variable: {repr var}"
  | .unboundEnumMember f sig =>
      s!"Unbound enum member '{f}' in enum '{sig.name}'"
  | .basicError msg =>
      msg.format
  | .tooManyArguments fnName nexpected nextra =>
      s!"Too many arguments to function {repr fnName}: expected {nexpected}, got {nexpected + nextra} (extra: {nextra})"
  | .tooFewArguments fnName nexpected nmissing =>
      s!"Too few arguments to function {repr fnName}: expected {nexpected}, missing {nmissing}"

/-- Format a complete error -/
def Error.format {pos_t var_t fn_name_t : Type}
    [Repr pos_t] [Repr var_t] [Repr fn_name_t]
    (err : Error pos_t var_t fn_name_t) : String :=
  s!"Error at {repr err.pos}: {err.msg.format}"

/-- Format an extended error with source -/
def ErrorWithSource.format {pos_t var_t fn_name_t : Type}
    [Repr pos_t] [Repr var_t] [Repr fn_name_t]
    (err : ErrorWithSource pos_t var_t fn_name_t) : String :=
  s!"Error at {repr err.toError.pos}: {err.toError.msg.format}"

/-! ## Convenient Type Aliases

Match the Coq naming conventions with clear implicits.
These aliases help maintain compatibility with the original Coq code structure.
-/

/-- Basic error message (no type parameters) -/
abbrev basic_error_message := BasicErrorMsg

/-- Function type checking error -/
abbrev fn_tc_error := FnTcError

/-- Error message with type parameters -/
abbrev error_message (var_t fn_name_t : Type) := ErrorMsg var_t fn_name_t

/-- Complete error with position (matches Coq's error type) -/
abbrev error (pos_t var_t fn_name_t : Type) := ErrorWithSource pos_t var_t fn_name_t

end Koika
