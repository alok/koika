(*! Implementation of a BTB !*)
Require Import Coq.Lists.List.

Require Import Koika.Frontend.
Require Import rv_isolation.RegFile.

Module Type Btb_sig.
  Parameter idx_sz:nat.
  Parameter tag:nat.
  Parameter addr:nat.
  Parameter rf_targets_struct_name : string.
  Parameter rf_tags_struct_name : string.
  Parameter rf_valid_struct_name : string.
  Parameter updateArgs_struct_name : string.

End Btb_sig.

(* Definition read_style tau := SequentialSwitch tau "tmp". *)
Definition write_style := @SequentialSwitchTt var_t.
Definition read_style (nbits: nat) := @OrTreeSwitch var_t nbits.

Module Btb (s:Btb_sig).
  Import s.

  Module RfParamsTargets <: RfPow2_sig.
    Definition idx_sz := idx_sz.
    Definition T := bits_t addr.
    Definition init := Bits.zeroes addr.
    Definition read_style := read_style addr.
    Definition write_style := write_style.
    Definition rf_struct_name := rf_targets_struct_name.
  End RfParamsTargets.

  Module RfParamsTags <: RfPow2_sig.
    Definition idx_sz := idx_sz.
    Definition T := bits_t tag.
    Definition init := Bits.zeroes tag.
    Definition read_style := read_style tag.
    Definition write_style := write_style.
    Definition rf_struct_name := rf_tags_struct_name.
  End RfParamsTags.

  Module RfParamsValid <: RfPow2_sig.
    Definition idx_sz := idx_sz.
    Definition T := bits_t 1.
    Definition init := Bits.zeroes 1.
    Definition read_style := read_style 1.
    Definition write_style := write_style.
    Definition rf_struct_name := rf_valid_struct_name.
  End RfParamsValid.

  Module Targets := RfPow2 RfParamsTargets.
  Module Tags := RfPow2 RfParamsTags.
  Module Valid := RfPow2 RfParamsValid.

  Inductive reg_t :=
  | targets (state: Targets.reg_t)
  | tags (state: Tags.reg_t)
  | valid (state: Valid.reg_t)
  .

  Definition R r :=
    match r with
    | targets n => Targets.R n
    | tags n => Tags.R n
    | valid n => Valid.R n
    end.

  Definition r idx : R idx :=
    match idx with
    | targets n => Targets.r n
    | tags n => Tags.r n
    | valid n => Valid.r n
    end.

  Definition name_reg r :=
    match r with
    | targets n => String.append "targets" (Targets.name_reg n)
    | tags n => String.append "tags" (Tags.name_reg n)
    | valid n => String.append "valid" (Valid.name_reg n)
    end.

  (* Internal functions *)
  Definition getIndex : UInternalFunction reg_t empty_ext_fn_t :=
    {{ (* Keep the idx_sz bits of the addr in words - that is drop the bottom two bits *)
        fun getIndex (a: bits_t addr) : bits_t idx_sz =>
          (a >> #(Bits.of_nat (log2 addr)  2))[#(Bits.of_nat (log2 addr) 0) :+ idx_sz] }}.

  Definition getTag : UInternalFunction reg_t empty_ext_fn_t :=
    {{ (* keep the `tag`high bits of the addr *)
        fun getIndex (a: bits_t addr) : bits_t tag =>
        a[#(Bits.of_nat (log2 addr) (addr-tag)) :+ tag]
    }}.

  (* Interesting point: the btb should almost never conflict even though it is not an ehr.
     We should investigate that. Indeed the wrong path instruction won't be seen that cycle! *)
  Definition predPc: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun predPc (pc: bits_t addr) : bits_t addr =>
        let index := getIndex(pc) in
        let tag := getTag(pc) in
        let lookup_tag := tags.(Tags.read_1)(index) in
        let lookup_valid := valid.(Valid.read_1)(index) in
        if ((lookup_tag == lookup_tag) && lookup_valid)
        then
           targets.(Targets.read_1)(index)
        else (* Need to check that this would work wihtout the parenthesis, that is we fixed the prirority problem *)
           (pc + #(Bits.of_nat addr 4))
    }}.
  Definition updateArgs_t:=
    {| struct_name := s.updateArgs_struct_name;
       struct_fields := [("pc", bits_t addr);
                         ("nextPc", bits_t addr)]
    |}.

  Definition update: UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun update (arg: struct_t updateArgs_t) : unit_t =>
        let pc := get(arg,pc) in
        let nextPc := get(arg,nextPc) in
        let index := getIndex(pc) in
        let tag := getTag(pc) in
        if (nextPc != (pc + #(Bits.of_nat addr 4))) (* this shuld not be required if we make sure to carry the taken/not taken from execute *)
        then
           valid.(Valid.write_0)(struct Valid.rf_write_t {arg_idx := index;
                                                          arg_val := #(Bits.of_nat 1 1)});
           targets.(Targets.write_0)(struct Targets.rf_write_t {arg_idx := index;
                                                                arg_val := nextPc });
           tags.(Tags.write_0)(struct Tags.rf_write_t {arg_idx := index;
                                                       arg_val := tag})
        else
          (if (tag == tags.(Tags.read_0)(index)) then
             valid.(Valid.write_0)(struct Valid.rf_write_t {arg_idx := index;
                                                            arg_val := #(Bits.of_nat 1 0)})
          else
             pass)
    }}.

End Btb.
