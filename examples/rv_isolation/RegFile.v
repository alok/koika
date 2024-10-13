(*! Implementation of a Register File *)
Require Import Koika.Frontend.

Module Type RfPow2_sig.
  Parameter idx_sz: nat.
  Parameter T: type.
  Parameter init: T.
  Parameter read_style : @switch_style var_t.
  Parameter write_style : @switch_style var_t.
  Parameter rf_struct_name : string.
End RfPow2_sig.

Module RfPow2 (s: RfPow2_sig).
  Definition sz := pow2 s.idx_sz.
  Inductive reg_t := rData (n: Vect.index sz).

  Definition R r :=
    match r with
    | rData _ => s.T
    end.

  Definition r idx : R idx :=
    match idx with
    | rData _ => s.init
    end.

  Definition name_reg r :=
    match r with
    | rData n => String.append "rData_" (show n)
    end.

  Definition rf_write_t:=
    {| struct_name := s.rf_struct_name;
       struct_fields := [("arg_idx", bits_t s.idx_sz);
                         ("arg_val", s.T)
                        ]
    |}.

  Definition read_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_0 (idx : bits_t s.idx_sz) : s.T =>
         `UCompleteSwitch s.read_style s.idx_sz "idx"
              (fun idx => {{ read0(rData idx) }})` }}.

  Definition write_0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_0 (arg: struct_t rf_write_t) : unit_t =>
         let idx := get(arg,arg_idx) in
         let val := get(arg,arg_val) in
         `UCompleteSwitch s.write_style s.idx_sz "idx"
              (fun idx => {{ write0(rData idx, val) }})` }}.

  Definition read_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun read_1 (idx : bits_t s.idx_sz) : s.T =>
         `UCompleteSwitch s.read_style s.idx_sz "idx"
              (fun idx => {{ read1(rData idx) }})` }}.

  Definition write_1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun write_1 (arg: struct_t rf_write_t) : unit_t =>
         let idx := get(arg,arg_idx) in
         let val := get(arg,arg_val) in
         `UCompleteSwitch s.write_style s.idx_sz "idx"
              (fun idx => {{ write1(rData idx, val) }})` }}.
End RfPow2.
