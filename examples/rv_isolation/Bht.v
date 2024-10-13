(*! Implementation of a Bht !*)
Require Import Coq.Lists.List.

Require Import Koika.Frontend.
Require Import rv_isolation.RegFile.

Module Type Bht_sig.
  Parameter idx_sz:nat.
  Parameter addr:nat.
  Parameter rf_struct_name: string.
  Parameter computeTargetArgs_struct_name: string.
  Parameter ppcDPArgs_struct_name: string.
  Parameter updateArgs_struct_name: string.
End Bht_sig.
Definition write_style := @SequentialSwitchTt var_t.
Definition read_style (nbits: nat) := @OrTreeSwitch var_t nbits.

Module Bht (s:Bht_sig).
  Import s.

  Module RfParamsDirs <: RfPow2_sig.
    Definition idx_sz := idx_sz.
    Definition T := bits_t 2.
    Definition init := Bits.zeroes 2.
    Definition read_style := read_style 2.
    Definition write_style := write_style.
    Definition rf_struct_name := s.rf_struct_name.
  End RfParamsDirs.

  Module Dirs := RfPow2 RfParamsDirs.

  Inductive reg_t :=
    dirs (state: Dirs.reg_t)
  .

  Definition R r :=
    match r with
    | dirs n => Dirs.R n
    end.

  Definition r idx : R idx :=
    match idx with
    | dirs n => Dirs.r n
    end.

  Definition name_reg r :=
    match r with
    | dirs n => String.append "dirs" (Dirs.name_reg n)
    end.

  Definition getIndex : UInternalFunction reg_t empty_ext_fn_t :=
    {{ (* Keep the idx_sz bits of the addr in words - that is drop the bottom two bits *)
        fun getIndex (a: bits_t addr) : bits_t idx_sz =>
          (a >> #(Bits.of_nat (log2 addr) 2))[#(Bits.of_nat (log2 addr) 0) :+ idx_sz] }}.

  Definition computeTargetArgs_t:=
    {| struct_name := s.computeTargetArgs_struct_name;
       struct_fields := [("pc", bits_t s.addr);
                         ("targetPc", bits_t s.addr);
                         ("taken", bits_t 1)]
    |}.

  Definition computeTarget : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun computeTarget (arg: struct_t computeTargetArgs_t) : bits_t addr =>
        let pc := get(arg,pc) in
        let targetPc := get(arg, targetPc) in
        let taken := get(arg, taken) in
        if taken
        then targetPc
        else (pc+ #(Bits.of_nat addr 4))
    }}.

  Definition extractDir : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun extractDir (dp: bits_t 2) : bits_t 1 =>
        (dp == Ob~1~1) || (dp == Ob~1~0)
    }}.
  Definition getEntry1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun getEntry (index: bits_t idx_sz) : bits_t 2 =>
           dirs.(Dirs.read_1)(index)
    }}.

  Definition getEntry0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun getEntry (index: bits_t idx_sz) : bits_t 2 =>
           dirs.(Dirs.read_0)(index)
    }}.

  Definition newDpBitsArg_t:=
    {| struct_name := "dpBitsArgs";
       struct_fields := [("dpBits", bits_t 2);
                         ("taken", bits_t 1)]
    |}.

  Definition newDpBits : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun newDpBits (arg: struct_t newDpBitsArg_t) : bits_t 2 =>
          let taken := get(arg,taken) in
          let dpBits := get(arg,dpBits) in
        if (taken )
        then
          (if dpBits == Ob~1~1 then dpBits else (dpBits + Ob~0~1))
        else
          (if dpBits == Ob~0~0 then dpBits else (dpBits - Ob~0~1))
    }}.

  Definition ppcDPArgs_t:=
    {| struct_name := s.ppcDPArgs_struct_name;
       struct_fields := [("pc", bits_t addr);
                         ("targetPc", bits_t addr)]
    |}.


  Definition ppcDP: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun ppcDP (arg: struct_t ppcDPArgs_t) : bits_t addr =>
          let pc := get(arg,pc) in
          let targetPc := get(arg,targetPc) in
        let index := getIndex(pc) in
        let entry := getEntry1(index) in
        let direction := extractDir(entry) in
        computeTarget(struct computeTargetArgs_t { pc := pc;
                                                   targetPc := targetPc;
                                                   taken := direction} )
    }}.


  Definition updateArgs_t:=
    {| struct_name := s.updateArgs_struct_name;
       struct_fields := [("pc", bits_t addr);
                         ("taken", bits_t 1)]
    |}.

  Definition update: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun update (arg: struct_t updateArgs_t) : unit_t =>
          let pc := get(arg,pc) in
          let taken := get(arg,taken) in
        let index := getIndex(pc) in
        let entry := getEntry0(index) in
        let newDp := newDpBits(struct newDpBitsArg_t  { dpBits := entry;
                                                        taken := taken}) in
        dirs.(Dirs.write_0)(struct Dirs.rf_write_t {arg_idx := index;
                                                    arg_val := newDp})
    }}.

End Bht.
