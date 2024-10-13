(*! Pipelined instantiation of an RV32I core !*)
Require Import rv_isolation.RVCore rv_isolation.rv32.
Module RV32IPackage := Package.
Definition prog := Interop.Backends.register RV32IPackage.package.
Extraction "rv32i.ml" prog.
(*
Require Import koikaExamples.Enclaves.SimulateBase.
Module RV32IPackage := Package.
Definition prog := Interop.Backends.register RV32IPackage.package.


Extraction "rv32i.ml" prog.
*)
