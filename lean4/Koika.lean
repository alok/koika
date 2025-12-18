-- Koika: A Core Language for Rule-Based Hardware Design
-- Lean 4 port of https://github.com/mit-plv/koika

import Koika.Types
import Koika.Primitives
import Koika.FiniteType
import Koika.Environments
import Koika.Syntax
import Koika.ErrorReporting
import Koika.TypedSyntax
import Koika.TypeInference
import Koika.DSL.Syntax
import Koika.Semantics.Logs
import Koika.Semantics.CompactLogs
import Koika.Semantics.Interp
import Koika.Semantics.CompactInterp
import Koika.Semantics.Properties
import Koika.Semantics.OneRuleAtATime
import Koika.Properties.Primitives
import Koika.Properties.TypedSyntax
import Koika.Compile.Lowered
import Koika.Compile.LoweredFunctions
import Koika.Compile.Circuit
import Koika.Compile.CircuitSemantics
import Koika.Compile.CircuitProperties
import Koika.Compile.Lower
import Koika.Compile.Optimize
import Koika.Compile.Compiler
import Koika.Compile.Correctness.LoweringCorrectness
import Koika.Compile.Correctness.CircuitCorrectness
import Koika.Compile.Correctness.Correctness
import Koika.Backend.Verilog
import Koika.Interop
import Koika.Basic
