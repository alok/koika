(*! Deprecated *)
(*
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.Lists.List.
Require Import rv_isolation.Common.

Inductive mem_rules_t :=
| Rl_doMemReq (core: ind_core_id)
| Rl_doMemResp (core: ind_core_id)
| Rl_doPurge (core: ind_core_id)
| Rl_doExternalMem
| Rl_tick
| Rl_doInit (core: ind_core_id).

Module Type Memory_sig.
  Parameter _reg_t : Type.
  Parameter _ext_fn_t : Type.
  Parameter R : _reg_t -> type.
  Parameter Sigma : _ext_fn_t -> ExternalSignature.
  Parameter r : bits_t 2 -> forall reg, R reg.
  Parameter rules : mem_rules_t -> rule R Sigma.
  Parameter FiniteType_reg_t : FiniteType _reg_t.
  Parameter Show_reg_t : Show _reg_t.
  Parameter schedule : @Syntax.scheduler Frontend.pos_t mem_rules_t.
End Memory_sig.

Definition NLINES := 512. (* 512 *)
Definition data_sig := bits_t 32.
Definition log_nlines := log2 NLINES.

Definition shreq :=
  {| struct_name := "shreq";
     struct_fields := [("req" , struct_t mem_req);
                       ("sourceType"    , bits_t 1);
                       ("sourceCore"    , bits_t 1);
                       ("valid"    , bits_t 1)
                       ] |}.
Definition shresp :=
  {| struct_name := "shresp";
     struct_fields := [("resp" , struct_t mem_resp);
                       ("sourceType"    , bits_t 1);
                       ("sourceCore"    , bits_t 1);
                       ("valid"    , bits_t 1)
                       ] |}.
Definition mem_input :=
  {| struct_name := "mem_input";
     struct_fields := [("get_ready", bits_t 1);
                      ("put_valid", bits_t 1);
                      ("put_request", struct_t mem_req)] |}.

Definition mem_output :=
  {| struct_name := "mem_output";
     struct_fields := [("get_valid", bits_t 1);
                      ("put_ready", bits_t 1);
                      ("get_response", struct_t mem_resp)] |}.

  Definition cache_req_sig :=
    {| struct_name := "cache_req";
      struct_fields := [("byte_en", bits_t 4); ("addr", bits_t log_nlines); ("data", bits_t 32)] |}.
  Definition cache_input_sig :=
    {| struct_name := "cache_input";
       struct_fields := [("get_ready", bits_t 1); ("put_valid", bits_t 1); ("put_request", struct_t cache_req_sig)]
    |}.
  Definition metadata_sig :=
    {| struct_name := "cache_metadata";
       struct_fields := [("tag", bits_t (log2 NLINES))
                         ;("valid", bits_t 1 )]
    |}.

  Definition metadata_req_sig :=
    {| struct_name := "metadata_req";
       struct_fields := [("is_write", bits_t 1); ("addr", bits_t log_nlines); ("data", struct_t metadata_sig)] |}.

  Definition metadata_input_sig :=
    {| struct_name := "metadata_input";
       struct_fields := [("get_ready", bits_t 1); ("put_valid", bits_t 1); ("put_request", struct_t metadata_req_sig)]
    |}.

  Definition cache_output_sig :=
    {| struct_name := "cache_output";
       struct_fields := [("get_valid", bits_t 1); ("put_ready", bits_t 1); ("get_response", data_sig)]
    |}.
  Definition metadata_output_sig :=
    {| struct_name := "metadata_output";
       struct_fields := [("get_valid", bits_t 1); ("put_ready", bits_t 1); ("get_response", struct_t metadata_sig)]
    |}.

Module Memory <: Memory_sig.
  Inductive mem_type := imem | dmem.

  Inductive ext_fn_t :=
  | ext_cache_imem0
  | ext_cache_imem1
  | ext_cache_dmem0
  | ext_cache_dmem1
  | ext_metacache_imem0
  | ext_metacache_imem1
  | ext_metacache_dmem0
  | ext_metacache_dmem1
  | ext_mainmem
  .

  Definition Sigma (fn: ext_fn_t) :=
  match fn with
  | ext_cache_imem0 => {$ struct_t cache_input_sig ~> struct_t cache_output_sig $}
  | ext_cache_imem1 => {$ struct_t cache_input_sig ~> struct_t cache_output_sig $}
  | ext_cache_dmem0 => {$ struct_t cache_input_sig ~> struct_t cache_output_sig $}
  | ext_cache_dmem1 => {$ struct_t cache_input_sig ~> struct_t cache_output_sig $}
  | ext_metacache_imem0 => {$ struct_t metadata_input_sig ~> struct_t metadata_output_sig $}
  | ext_metacache_imem1 => {$ struct_t metadata_input_sig ~> struct_t metadata_output_sig $}
  | ext_metacache_dmem0 => {$ struct_t metadata_input_sig ~> struct_t metadata_output_sig $}
  | ext_metacache_dmem1 => {$ struct_t metadata_input_sig ~> struct_t metadata_output_sig $}
  | ext_mainmem => {$ struct_t mem_input ~> struct_t mem_output $}
  end.

  Inductive reg_t :=
  | toIMem0 (state: MemReq.reg_t) (* These go to the caches *)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemRespBypass.reg_t)
  | fromIMem1 (state: MemRespBypass.reg_t)
  | fromDMem0 (state: MemRespBypass.reg_t)
  | fromDMem1 (state: MemRespBypass.reg_t)
  | toMainMemIMem0 (state: MemReq.reg_t)
  | toMainMemIMem1 (state: MemReq.reg_t)
  | toMainMemDMem0 (state: MemReq.reg_t)
  | toMainMemDMem1 (state: MemReq.reg_t)
  | fromMainMemIMem0 (state: MemRespBypass.reg_t)
  | fromMainMemIMem1 (state: MemRespBypass.reg_t)
  | fromMainMemDMem0 (state: MemRespBypass.reg_t)
  | fromMainMemDMem1 (state: MemRespBypass.reg_t)
  | SHReq
  | SHResp
  | purge (core: ind_core_id)
  | turn
  | priv_turn (core: ind_core_id)
  .

  Definition R (idx: reg_t) : type :=
    match idx with
    | toIMem0 st => MemReq.R st
    | toIMem1 st => MemReq.R st
    | toDMem0 st => MemReq.R st
    | toDMem1 st => MemReq.R st
    | fromIMem0 st => MemRespBypass.R st
    | fromIMem1 st => MemRespBypass.R st
    | fromDMem0 st => MemRespBypass.R st
    | fromDMem1 st => MemRespBypass.R st
    | toMainMemIMem0 st => MemReq.R st
    | toMainMemIMem1 st => MemReq.R st
    | toMainMemDMem0 st => MemReq.R st
    | toMainMemDMem1 st => MemReq.R st
    | fromMainMemIMem0 st => MemRespBypass.R st
    | fromMainMemIMem1 st => MemRespBypass.R st
    | fromMainMemDMem0 st => MemRespBypass.R st
    | fromMainMemDMem1 st => MemRespBypass.R st
    | SHReq => struct_t shreq
    | SHResp => struct_t shresp
    | purge _ => enum_t purge_state
    | turn => bits_t 2
    (* | reg_metadata_req => maybe (struct_t metadata_input_sig) *)
    (* | reg_metadata_resp => maybe (struct_t metadata_output_sig) *)
    | priv_turn _=> bits_t 1
    end.

  Definition r (turn: bits_t 2) (idx: reg_t) : R idx :=
    match idx with
    | toIMem0 st => MemReq.r st
    | toIMem1 st => MemReq.r st
    | toDMem0 st => MemReq.r st
    | toDMem1 st => MemReq.r st
    | fromIMem0 st => MemRespBypass.r st
    | fromIMem1 st => MemRespBypass.r st
    | fromDMem0 st => MemRespBypass.r st
    | fromDMem1 st => MemRespBypass.r st
    | toMainMemIMem0 st => MemReq.r st
    | toMainMemIMem1 st => MemReq.r st
    | toMainMemDMem0 st => MemReq.r st
    | toMainMemDMem1 st => MemReq.r st
    | fromMainMemIMem0 st => MemRespBypass.r st
    | fromMainMemIMem1 st => MemRespBypass.r st
    | fromMainMemDMem0 st => MemRespBypass.r st
    | fromMainMemDMem1 st => MemRespBypass.r st
    | purge _ => value_of_bits (Bits.zero)
    | turn => turn
    | SHReq  => value_of_bits (Bits.zero)
    | SHResp => value_of_bits (Bits.zero)
    | priv_turn _ => Bits.zero
    end.

  Definition _reg_t := reg_t.
  Instance FiniteType_reg_t : FiniteType _reg_t := _.
  Definition _ext_fn_t := ext_fn_t.
  (* Definition Sigma := Sigma. *)


  Definition coreToCache (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => toIMem0
            | imem, CoreId1 => toIMem1
            | dmem, CoreId0 => toDMem0
            | dmem, CoreId1 => toDMem1
            end) reg.

  Definition toMainMem (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => toMainMemIMem0
            | imem, CoreId1 => toMainMemIMem1
            | dmem, CoreId0 => toMainMemDMem0
            | dmem, CoreId1 => toMainMemDMem1
            end) reg.

  Definition fromMainMem (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => fromMainMemIMem0
            | imem, CoreId1 => fromMainMemIMem1
            | dmem, CoreId0 => fromMainMemDMem0
            | dmem, CoreId1 => fromMainMemDMem1
            end) reg.

  Definition cacheToCore (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => fromIMem0
            | imem, CoreId1 => fromIMem1
            | dmem, CoreId0 => fromDMem0
            | dmem, CoreId1 => fromDMem1
            end) reg.

  Definition doCache (cache: mem_type) (core: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard(read0(purge core) == enum purge_state { Ready });
       pass
    }}.


  Definition do_mem_req (core_id: ind_core_id): uaction reg_t ext_fn_t :=
    let fromIMem := fromIMem core_id in
    let toIMem := toIMem core_id in
    let fromDMem := fromDMem core_id in
    let toDMem := toDMem core_id in
    {{ guard(read0(purge core_id) == enum purge_state { Ready } );
       guard(read0(turn) == #(mem_write_turn core_id));
       (if (read0(priv_turn core_id)) then
         if ( fromIMem.(MemRespBypass.can_enq)() && toIMem.(MemReq.can_deq)())  then
           (let req := toIMem.(MemReq.deq)() in
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~1;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else
           pass
       else (* (read0(priv_turn core_id) == Ob~1 *)
         if ( fromDMem.(MemRespBypass.can_enq)() && toDMem.(MemReq.can_deq)())  then
           (let req := toDMem.(MemReq.deq)() in
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~0;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else pass);
       write0((priv_turn core_id), read0(priv_turn core_id) + Ob~1)
    }}.

  Definition do_mem_resp (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    let fromIMem := fromIMem core_id in
    let toIMem := toIMem core_id in
    let fromDMem := fromDMem core_id in
    let toDMem := toDMem core_id in
    {{ guard(read0(purge core_id) == enum purge_state { Ready } );
       guard(get(read1(SHResp), sourceCore) == #(core_id_to_bits core_id));
       guard(get(read1(SHResp), valid) == Ob~1);
       let resp := read1(SHResp) in
       let iorD := get(resp, sourceType) in (* I is 1, D is 0 *)
       let res := get(resp, resp) in
       (if ((iorD == Ob~0) && fromDMem.(MemRespBypass.can_enq)()) then
          fromDMem.(MemRespBypass.enq)(res)
        else if ((iorD == Ob~1) && fromIMem.(MemRespBypass.can_enq)()) then
          fromIMem.(MemRespBypass.enq)(res)
        else pass)
    }}.

  Definition do_external_mem : uaction reg_t ext_fn_t :=
    {{
        let req := read1(SHReq) in
        let enqueue := get(req, valid) in
        let memory_request := (if enqueue then get(req, req)
                               else `UConst (tau := struct_t mem_req) (value_of_bits Bits.zero)`) in
        let response := extcall ext_mainmem (struct mem_input {get_ready := Ob~1;
                                                               put_valid := enqueue;
                                                               put_request := memory_request }) in
        (if enqueue then
           write1(SHReq, subst (req,valid,Ob~0))
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        write0(SHResp, struct shresp { resp := response;
                                       sourceType := get(req, sourceType);
                                       sourceCore := get(req, sourceCore);
                                       valid := is_response })
    }}.

  Definition do_tick_turn : uaction reg_t ext_fn_t :=
    {{ let turn := read0(turn) in
      (* Tick in memory, every two cycles we can enqueue a new thing *)
      (* write0(public turn, turn  + Ob~0~1); *)
       write0(turn, turn + Ob~0~1)
    }}.

  Definition do_init (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard (read0(purge core_id) == enum purge_state { Init } );
       write0(purge core_id, enum purge_state { Ready } )
    }}.

  Definition do_purge (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    let toIMem := toIMem core_id in
    let toDMem := toDMem core_id in
    {{ guard(read0(purge core_id) == enum purge_state { Purging } );
       guard(read0(turn) == #(cid_to_freeze_cycle core_id));
       (* Reset private state *)
       write0(priv_turn core_id, Ob~0);
       toIMem.(MemReq.reset)();
       toDMem.(MemReq.reset)();
       write0(purge core_id, enum purge_state { Purged })
    }}.

  Definition tc_doMemReq0:= tc_rule R Sigma (do_mem_req CoreId0).
  Definition tc_doMemReq1 := tc_rule R Sigma (do_mem_req CoreId1).
  Definition tc_doMemResp0:= tc_rule R Sigma (do_mem_resp CoreId0).
  Definition tc_doMemResp1 := tc_rule R Sigma (do_mem_resp CoreId1).
  Definition tc_doPurge0:= tc_rule R Sigma (do_purge CoreId0).
  Definition tc_doPurge1 := tc_rule R Sigma (do_purge CoreId1).
  Definition tc_external_mem := tc_rule R Sigma (do_external_mem).
  Definition tc_tick := tc_rule R Sigma do_tick_turn.
  Definition tc_init0 := tc_rule R Sigma (do_init CoreId0).
  Definition tc_init1 := tc_rule R Sigma (do_init CoreId1).

  Definition rules (rl: mem_rules_t) : rule R Sigma :=
    match rl with
    | Rl_doMemReq CoreId0 => tc_doMemReq0
    | Rl_doMemReq CoreId1=> tc_doMemReq1
    | Rl_doMemResp CoreId0 => tc_doMemResp0
    | Rl_doMemResp CoreId1  => tc_doMemResp1
    | Rl_doPurge CoreId0 => tc_doPurge0
    | Rl_doPurge CoreId1 => tc_doPurge1
    | Rl_doExternalMem => tc_external_mem
    | Rl_tick => tc_tick
    | Rl_doInit CoreId0 => tc_init0
    | Rl_doInit CoreId1 => tc_init1
    end.

  Instance Show_reg_t : Show reg_t := _.

  Definition schedule : @Syntax.scheduler Frontend.pos_t mem_rules_t :=
      Rl_doMemReq CoreId0 |> Rl_doMemReq CoreId1
        |> Rl_doPurge CoreId0 |> Rl_doPurge CoreId1 |> Rl_doExternalMem
                   |> Rl_doMemResp CoreId0 |> Rl_doMemResp CoreId1 |> Rl_doInit CoreId0 |> Rl_doInit CoreId1 |> Rl_tick |> done.




  Definition metadataReq: UInternalFunction reg_t ext_fn_t :=
    {{ fun metadataReq (req: (struct_t metadata_input)) : bits_t 0 =>
         write0(reg_metadata_req, { valid (struct_t metadata_input) }(req) )
    }}.

  (* Four reg_metadata_req *)

  Definition do_external_metadata: uaction reg_t ext_fn_t :=
    {{
        let req := read1(reg_metadata_req) in
        let enqueue := get(req, valid) in
        let memory_request := (if enqueue then get(req, req)
                               else `UConst (tau := struct_t metadata_input) (value_of_bits Bits.zero)`) in
        let response := extcall ext_metadata (struct metadata_input {get_ready := Ob~1;
                                                                     put_valid := enqueue;
                                                                     put_request := memory_request }) in
        (if enqueue then
           write1(reg_metadata_req, subst (req,valid,Ob~0))
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        write0(reg_metadata_resp, struct (maybe (struct_t metadata_output))
                                         { valid := is_response;
                                           data := response
                                         })
    }}.
        (if enqueue then
           write1(SHReq, subst (req,valid,Ob~0))
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        write0(SHResp, struct shresp { resp := response;
                                       sourceType := get(req, sourceType);
                                       sourceCore := get(req, sourceCore);
                                       valid := is_response })

        let


  Definition do_external_mem : uaction reg_t ext_fn_t :=
    {{
        let req := read1(SHReq) in
        let enqueue := get(req, valid) in
        let memory_request := (if enqueue then get(req, req)
                               else `UConst (tau := struct_t mem_req) (value_of_bits Bits.zero)`) in
        let response := extcall ext_mainmem (struct mem_input {get_ready := Ob~1;
                                                               put_valid := enqueue;
                                                               put_request := memory_request }) in
        (if enqueue then
           write1(SHReq, subst (req,valid,Ob~0))
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        write0(SHResp, struct shresp { resp := response;
                                       sourceType := get(req, sourceType);
                                       sourceCore := get(req, sourceCore);
                                       valid := is_response })
    }}.

  Definition do_mem_req (core_id: ind_core_id): uaction reg_t ext_fn_t :=
    let fromIMem := fromIMem core_id in
    let toIMem := toIMem core_id in
    let fromDMem := fromDMem core_id in
    let toDMem := toDMem core_id in
    {{ guard(read0(purge core_id) == enum purge_state { Ready } );
       guard(read0(turn) == #(mem_write_turn core_id));
       (if (read0(priv_turn core_id)) then
         if ( fromIMem.(MemRespBypass.can_enq)() && toIMem.(MemReq.can_deq)())  then
           (let req := toIMem.(MemReq.deq)() in
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~1;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else
           pass
       else (* (read0(priv_turn core_id) == Ob~1 *)
         if ( fromDMem.(MemRespBypass.can_enq)() && toDMem.(MemReq.can_deq)())  then
           (let req := toDMem.(MemReq.deq)() in
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~0;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else pass);
       write0((priv_turn core_id), read0(priv_turn core_id) + Ob~1)
    }}.


End Memory.
*)
