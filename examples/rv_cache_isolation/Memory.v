(*! Cache test *)
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.Lists.List.
Require Import rv_cache_isolation.Common.

Inductive mem_rules_t :=
| Rl_doMemReq (core: ind_core_id)
| Rl_doMemResp (core: ind_core_id)
| Rl_doPurge (core: ind_core_id)
| Rl_doExternalMem
| Rl_tick
| Rl_doInit (core: ind_core_id)
| Rl_doFreeze (core: ind_core_id)
| Rl_doCacheReq (cache: mem_type) (core: ind_core_id)
(* | Rl_doCacheResp (cache: mem_type) (core: ind_core_id) *)
| Rl_doExternalMetadata (cache: mem_type) (core: ind_core_id)
| Rl_doExternalCache (cache: mem_type) (core: ind_core_id)
.

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

Definition cache_index_t := bits_t log_nlines.
Definition tag_size := Eval vm_compute in (32 - log_nlines - 2).
Definition cache_tag_t := bits_t tag_size.

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

(* Ready -> ProcessRequest -> SendFillReq -> WaitFillResp -> Ready *)
Definition cache_fsm_sig :=
  {| enum_name := "cache_fsm";
     enum_members :=
      ["Ready"; "ProcessRequest"; "SendFillReq"; "WaitFillResp";
       "FlushLineReady"; "FlushLineProcess"; "FlushPrivateData"; "Flushed"];
     enum_bitpatterns := vect_map (Bits.of_nat 3) [0;1;2;3;4;5;6; 7]
  |}%vect.


Module FifoMetadataReq <: Fifo.
  Definition T:= struct_t metadata_req_sig.
End FifoMetadataReq.
Module MetadataReqBypass := Fifo1Bypass FifoMetadataReq.
Module FifoCacheReq<: Fifo.
  Definition T:= struct_t cache_req_sig.
End FifoCacheReq.
Module CacheReqBypass := Fifo1Bypass FifoCacheReq.

Module FifoMetadataResp <: Fifo.
  Definition T:= struct_t metadata_sig.
End FifoMetadataResp.
Module MetadataResp := Fifo1 FifoMetadataResp.
Module FifoCacheResp <: Fifo.
  Definition T:= data_sig.
End FifoCacheResp.
Module CacheResp := Fifo1 FifoCacheResp.

Module CacheState.
  Inductive reg_t :=
  | line_flush_idx
  | SH_metadata_req (st: MetadataReqBypass.reg_t)
  | SH_metadata_resp (st: MetadataResp.reg_t)
  | SH_cache_req (st: CacheReqBypass.reg_t)
  | SH_cache_resp (st: CacheResp.reg_t)
  | toMainMem (st: MemReqBypass.reg_t)
  | fromMainMem (st: MemResp.reg_t)
  | cache_fsm.

  Definition R (idx: reg_t) : type :=
    match idx with
    | line_flush_idx => bits_t (log_nlines) (* +1? *)
    | SH_metadata_req st => MetadataReqBypass.R st
    | SH_metadata_resp st => MetadataResp.R st
    | SH_cache_req st => CacheReqBypass.R st
    | SH_cache_resp st => CacheResp.R st
    | toMainMem st => MemReqBypass.R st
    | fromMainMem st => MemResp.R st
    | cache_fsm => enum_t cache_fsm_sig
    end.
  Definition r (idx: reg_t) : R idx :=
    match idx with
    | line_flush_idx => Bits.zero
    | SH_metadata_req st => MetadataReqBypass.r st
    | SH_metadata_resp st => MetadataResp.r st
    | SH_cache_req st => CacheReqBypass.r st
    | SH_cache_resp st => CacheResp.r st
    | toMainMem st => MemReqBypass.r st
    | fromMainMem st => MemResp.r st
    | cache_fsm => value_of_bits (Bits.zero)
    end.

End CacheState.
Instance FiniteType_CacheState : FiniteType CacheState.reg_t := _.

Module Memory <: Memory_sig.

  Inductive reg_t :=
  | toIMem0 (state: MemReq.reg_t) (* These go to the caches *)
  | toIMem1 (state: MemReq.reg_t)
  | toDMem0 (state: MemReq.reg_t)
  | toDMem1 (state: MemReq.reg_t)
  | fromIMem0 (state: MemRespBypass.reg_t)
  | fromIMem1 (state: MemRespBypass.reg_t)
  | fromDMem0 (state: MemRespBypass.reg_t)
  | fromDMem1 (state: MemRespBypass.reg_t)
  | SHReq
  | SHResp
  | purge (core: ind_core_id)
  | turn
  | priv_turn (core: ind_core_id)
  | freeze (core: ind_core_id) (* Track whether we sent a req to memory this turn and shouldn't purge just yet *)
  | cache_imem0 (state: CacheState.reg_t)
  | cache_dmem0 (state: CacheState.reg_t)
  | cache_imem1 (state: CacheState.reg_t)
  | cache_dmem1 (state: CacheState.reg_t)
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
    | SHReq => struct_t shreq
    | SHResp => struct_t shresp
    | purge _ => enum_t purge_state
    | turn => bits_t 2
    | priv_turn _=> bits_t 1
    | cache_imem0 st => CacheState.R st
    | cache_dmem0 st => CacheState.R st
    | cache_imem1 st => CacheState.R st
    | cache_dmem1 st => CacheState.R st
    | freeze _ => bits_t 1
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
    | purge _ => value_of_bits (Bits.zero)
    | turn => turn
    | SHReq  => value_of_bits (Bits.zero)
    | SHResp => value_of_bits (Bits.zero)
    | priv_turn _ => Bits.zero
    | cache_imem0 st => CacheState.r st
    | cache_dmem0 st => CacheState.r st
    | cache_imem1 st => CacheState.r st
    | cache_dmem1 st => CacheState.r st
    | freeze _ => Bits.zero
    end.

  Definition _reg_t := reg_t.
  Instance FiniteType_reg_t : FiniteType _reg_t := _.
  Definition _ext_fn_t := ext_fn_t.
  Definition Sigma := Sigma.

  Definition coreToCache (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => toIMem0
            | imem, CoreId1 => toIMem1
            | dmem, CoreId0 => toDMem0
            | dmem, CoreId1 => toDMem1
            end) reg.

  Definition cache_reg (cache: mem_type) (core: ind_core_id) :=
    fun reg => match cache, core with
            | imem, CoreId0 => cache_imem0
            | dmem, CoreId0 => cache_dmem0
            | imem, CoreId1 => cache_imem1
            | dmem, CoreId1 => cache_dmem1
            end reg.

  Definition toMainMem (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.toMainMem reg).

  Definition fromMainMem (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.fromMainMem reg).

  Definition cacheToCore (cache: mem_type) (core: ind_core_id) :=
    fun reg => (match cache, core with
            | imem, CoreId0 => fromIMem0
            | imem, CoreId1 => fromIMem1
            | dmem, CoreId0 => fromDMem0
            | dmem, CoreId1 => fromDMem1
            end) reg.

  Definition cacheState (cache: mem_type) (core: ind_core_id) :=
    cache_reg cache core (CacheState.cache_fsm).

  Definition SH_metadata_req (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.SH_metadata_req reg).
  Definition SH_metadata_resp (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.SH_metadata_resp reg).
  Definition SH_cache_req (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.SH_cache_req reg).
  Definition SH_cache_resp (cache: mem_type) (core: ind_core_id) :=
    fun reg => cache_reg cache core (CacheState.SH_cache_resp reg).

  Definition read1_purge0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun read1_purge0 () : enum_t purge_state =>
          read1(purge CoreId0)
    }}.

  Definition read1_purge1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun read1_purge1 () : enum_t purge_state =>
          read1(purge CoreId1)
    }}.

  Definition read1_purge (core: ind_core_id) : UInternalFunction reg_t empty_ext_fn_t :=
    match core with
    | CoreId0 => read1_purge0
    | CoreId1 => read1_purge1
    end.


  Definition write1_purge0 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun write1_purge0 (arg: enum_t purge_state) : bits_t 0 =>
          write1(purge CoreId0, arg)
    }}.

  Definition write1_purge1 : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun write1_purge1 (arg: enum_t purge_state) : bits_t 0 =>
          write1(purge CoreId1, arg)
    }}.

  Definition write1_purge (core: ind_core_id) : UInternalFunction reg_t empty_ext_fn_t :=
    match core with
    | CoreId0 => write1_purge0
    | CoreId1 => write1_purge1
    end.

  Definition getIndex : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun getIndex (addr: bits_t 32) : cache_index_t =>
         addr[|5`d2|:+log_nlines]
    }}.

  Definition getTag : UInternalFunction reg_t empty_ext_fn_t :=
    (* let base := (USugar (UConstBits (Bits.of_N (5<:nat) (N.of_nat log_nlines + 2)%N))) in *)
    {{ fun getTag (addr: bits_t 32) : cache_tag_t =>
         addr[|5`d(N.of_nat log_nlines + 2)|:+tag_size]
    }}.

  (*
  Definition respondToCore (cache: mem_type) (core: ind_core_id)
    (cond: uaction reg_t ext_fn_t) (value: uaction reg_t ext_fn_t) : uaction reg_t ext_fn_t :=
    let toCore := cacheToCore cache core in
    {{ if `cond` then
         toCore.(MemRespBypass.enq)(struct mem_resp { byte_en := get(mem_req, byte_en);
                                                      addr := get(mem_req,addr);
                                                      data := |32`d0|
                                                    })
  *)

  Definition load_meta_and_cache (cache: mem_type) (core: ind_core_id)
                       (index: uaction reg_t ext_fn_t)
                       : uaction reg_t ext_fn_t :=
    let metadataReq := SH_metadata_req cache core in
    let cacheReq := SH_cache_req cache core in
    {{ let index := `index` in
        let meta_req := struct metadata_req_sig { is_write := Ob~0;
                                                 addr := index;
                                                 data := `UConst (tau := struct_t metadata_sig) (value_of_bits Bits.zero)` } in
       let cache_req := struct cache_req_sig { byte_en := Ob~0~0~0~0;
                                                   addr := index;
                                                   data := |32`d0|
                                                 } in
       metadataReq.(MetadataReqBypass.enq)(meta_req);
       cacheReq.(CacheReqBypass.enq)(cache_req)
    }}.
  Definition do_cache_req (cache: mem_type) (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let fromCore := coreToCache cache core in
    let toMainMem := toMainMem cache core in
    let fromMainMem := fromMainMem cache core in
    let toCore := cacheToCore cache core in
    let metadataReq := SH_metadata_req cache core in
    let cacheReq := SH_cache_req cache core in
    let metadataResp := SH_metadata_resp cache core in
    let cacheResp := SH_cache_resp cache core in
    let line_flush_idx := cache_reg cache core CacheState.line_flush_idx in
    let cacheStateReg := cacheState cache core in
    {{ guard(read0(freeze core) == Ob~0);
       guard(read0(purge core) == enum purge_state { Ready } || read0(purge core) == enum purge_state { Purging });
       guard(read0(cacheStateReg) != enum cache_fsm_sig { Flushed });
       let cache_state := read0(cacheStateReg) in
       let maybe_mem_req := fromCore.(MemReq.peek)() in
       let mem_req := get(maybe_mem_req, data) in
       if (cache_state == enum cache_fsm_sig { Ready } && fromCore.(MemReq.can_deq)()) then
         `load_meta_and_cache cache core {{ getIndex(get(mem_req,addr)) }}`;
         write0(cacheStateReg, enum cache_fsm_sig { ProcessRequest })
       else if (read0(purge core) == enum purge_state {Purging} &&
                cache_state == enum cache_fsm_sig { Ready } &&
                !fromCore.(MemReq.can_deq)()) then
          write0(cacheStateReg, enum cache_fsm_sig { FlushLineReady });
          write0(line_flush_idx, |(log_nlines)`d0|)
       else if (cache_state == enum cache_fsm_sig { ProcessRequest }) then
         ( let meta_resp := metadataResp.(MetadataResp.deq)() in
           let cache_resp := cacheResp.(CacheResp.deq)() in
           if (get(meta_resp,valid) && (get(meta_resp,tag) == getTag(get(mem_req,addr)))) then
             (* HIT: If store: send request to cache. If load: return data *)
             (ignore(fromCore.(MemReq.deq)());
              write0(cacheStateReg, enum cache_fsm_sig { Ready });
              let data := |32`d0| in
              (if get(mem_req, byte_en) != Ob~0~0~0~0 then (* is store? *)
                 set data := |32`d0|;
                 cacheReq.(CacheReqBypass.enq)(struct cache_req_sig
                            { byte_en := get(mem_req, byte_en);
                              addr := getIndex(get(mem_req,addr));
                              data := get(mem_req,data)})
               else
                 set data := cache_resp);
              (when (read0(purge core) == enum purge_state { Ready }) do
                  toCore.(MemRespBypass.enq)(struct mem_resp { byte_en := get(mem_req, byte_en);
                                                               addr := get(mem_req,addr);
                                                               data := data
                                                             }))
              )
           else if (get(meta_resp,valid)) then
              (* DIRTY MISS: writeback to main memory; fill cache *)
              let addr := get(meta_resp,tag) ++ getIndex(get(mem_req,addr)) ++ Ob~0~0 in
              toMainMem.(MemReqBypass.enq)(struct mem_req { byte_en := Ob~1~1~1~1;
                                                            addr := addr;
                                                            data := cache_resp});
              write0(cacheStateReg, enum cache_fsm_sig { SendFillReq })
           else
             (* Clean miss! *)
             (write0(cacheStateReg, enum cache_fsm_sig { WaitFillResp });
              toMainMem.(MemReqBypass.enq)(struct mem_req {byte_en := Ob~0~0~0~0;
                                                           addr := get(mem_req,addr);
                                                           data := |32`d0|}))
         )
       else if (cache_state == enum cache_fsm_sig { SendFillReq }) then
           write0(cacheStateReg, enum cache_fsm_sig { WaitFillResp });
           toMainMem.(MemReqBypass.enq)(struct mem_req {byte_en := Ob~0~0~0~0;
                                                         addr := get(mem_req,addr);
                                                         data := |32`d0|})
       else if (cache_state == enum cache_fsm_sig { WaitFillResp }) then
           (write0(cacheStateReg, enum cache_fsm_sig { Ready });
            ignore(fromCore.(MemReq.deq)());
            let mem_resp := fromMainMem.(MemResp.deq)() in
            let meta_req := struct metadata_req_sig {
                                is_write := Ob~1;
                                addr := getIndex(get(mem_req,addr));
                                data := struct metadata_sig { tag := getTag(get(mem_req,addr));
                                                              valid := Ob~1} } in
            metadataReq.(MetadataReqBypass.enq)(meta_req);
            let byte_en := get(mem_req, byte_en) in
            let current_data := get(mem_resp,data) in
            let req_data := get(mem_req,data) in
            let to_core_data := |32`d0| in
            (if byte_en != Ob~0~0~0~0 then (* Store *)
              ((* Gross *)
                let new_data :=
                  ((if byte_en[|2`d3|] then req_data else current_data)[|5`d24|:+8]) ++
                  ((if byte_en[|2`d2|] then req_data else current_data)[|5`d16|:+8]) ++
                  ((if byte_en[|2`d1|] then req_data else current_data)[|5`d8|:+8]) ++
                  ((if byte_en[|2`d0|] then req_data else current_data)[|5`d0|:+8])  in
               let cache_req := struct cache_req_sig { byte_en := Ob~1~1~1~1;
                                                       addr := getIndex(get(mem_req,addr));
                                                       data := new_data
                                                     } in
                cacheReq.(CacheReqBypass.enq)(cache_req)
              )
            else (* Load *)
              (let cache_req := struct cache_req_sig { byte_en := Ob~1~1~1~1;
                                                       addr := getIndex(get(mem_req,addr));
                                                       data := current_data
                                                      } in
               cacheReq.(CacheReqBypass.enq)(cache_req);
               set to_core_data := current_data
              ));
            (when (read0(purge core) == enum purge_state { Ready }) do
                 toCore.(MemRespBypass.enq)(struct mem_resp { byte_en := get(mem_req, byte_en);
                                                              addr := get(mem_req,addr);
                                                              data := to_core_data
                                                      }))
           )
       else if (cache_state == enum cache_fsm_sig { FlushLineReady }) then
         let line := read0(line_flush_idx) in
         `load_meta_and_cache cache core {{ line }}`;
          write0(cacheStateReg, enum cache_fsm_sig { FlushLineProcess })
       else if (cache_state == enum cache_fsm_sig { FlushLineProcess }) then
         let line := read0(line_flush_idx) in
         let meta_resp := metadataResp.(MetadataResp.deq)() in
         let cache_resp := cacheResp.(CacheResp.deq)() in
         (* Invalidate metadata *)
         (if (get(meta_resp,valid)) then
              (* Dirty: need to writeback to main memory *)
           let addr := get(meta_resp,tag) ++ line ++ Ob~0~0 in
           toMainMem.(MemReqBypass.enq)(struct mem_req { byte_en := Ob~1~1~1~1;
                                                         addr := addr;
                                                         data := cache_resp})
           (* metadataReq.(MetadataReqBypass.enq)(struct metadata_req_sig *)
           (*   { is_write := Ob~1; addr := line; *)
           (*     data := `UConst (tau := struct_t metadata_sig) (value_of_bits Bits.zero)`}); *)
           (* (* TODO: not necessary really *) *)
           (* cacheReq.(CacheReqBypass.enq)(struct cache_req_sig *)
           (*   { byte_en := Ob~1~1~1~1; addr := line; data := |32`d0|  }) *)
          else
             (* Don't have to do anything *)
           pass
         );
         metadataReq.(MetadataReqBypass.enq)(struct metadata_req_sig
           { is_write := Ob~1; addr := line;
             data := `UConst (tau := struct_t metadata_sig) (value_of_bits Bits.zero)`});
         (* TODO: not necessary really *)
         cacheReq.(CacheReqBypass.enq)(struct cache_req_sig
           { byte_en := Ob~1~1~1~1; addr := line; data := |32`d0|  });
         let next_line := line + |(log_nlines)`d1| in
         write0(line_flush_idx, next_line);
         (if next_line == |(log_nlines)`d0| then (* Done flushing lines *)
            write0(cacheStateReg, enum cache_fsm_sig { FlushPrivateData })
          else
            write0(cacheStateReg, enum cache_fsm_sig { FlushLineReady })
         )
       else if (cache_state == enum cache_fsm_sig { FlushPrivateData } &&
                toMainMem.(MemReqBypass.can_enq)()  &&
                metadataReq.(MetadataReqBypass.can_enq)()  &&
                cacheReq.(CacheReqBypass.can_enq)()
               ) then
          write0(line_flush_idx, |(log_nlines)`d0|);
          metadataResp.(MetadataResp.reset_all)();
          cacheResp.(CacheResp.reset_all)();
          fromMainMem.(MemResp.reset_all)();
          write0(cacheStateReg, enum cache_fsm_sig { Flushed })
       else pass
    }}.

  Definition ext_metadata (cache: mem_type) (core: ind_core_id) : ext_fn_t :=
    match cache with
    | imem => ext_metadata_imem core
    | dmem => ext_metadata_dmem core
    end.
  Definition ext_cache (cache: mem_type) (core: ind_core_id) : ext_fn_t :=
    match cache with
    | imem => ext_cache_imem core
    | dmem => ext_cache_dmem core
    end.

  Definition do_external_metadata (cache: mem_type) (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let metadataReq := SH_metadata_req cache core in
    let metadataResp := SH_metadata_resp cache core in

    {{ let req := metadataReq.(MetadataReqBypass.peek)() in
       let enqueue := get(req, valid) in
       let memory_request := (if enqueue then get(req, data)
                              else `UConst (tau := struct_t metadata_req_sig) (value_of_bits Bits.zero)`) in
       let get_ready := metadataResp.(MetadataResp.can_enq)() in
       let response := extcall (ext_metadata cache core) (struct metadata_input_sig {get_ready := get_ready;
                                                                                     put_valid := enqueue;
                                                                                     put_request := memory_request }) in
        (if enqueue && get(response,put_ready) then
           metadataReq.(MetadataReqBypass.reset_all)()
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        if is_response then
          metadataResp.(MetadataResp.enq)(response)
        else pass
    }}.

  Definition do_external_cache (cache: mem_type) (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let cacheReq := SH_cache_req cache core in
    let cacheResp := SH_cache_resp cache core in

    {{ let req := cacheReq.(CacheReqBypass.peek)() in
       let enqueue := get(req, valid) in
       let memory_request := (if enqueue then get(req, data)
                              else `UConst (tau := struct_t cache_req_sig) (value_of_bits Bits.zero)`) in
       let get_ready := cacheResp.(CacheResp.can_enq)() in
       let response := extcall (ext_cache cache core) (struct cache_input_sig {get_ready := get_ready;
                                                                               put_valid := enqueue;
                                                                               put_request := memory_request }) in
        (if enqueue && get(response,put_ready) then
           cacheReq.(CacheReqBypass.reset_all)()
         else pass);
        let is_response := get(response, get_valid) in
        let response := get(response, get_response) in
        if is_response then
          cacheResp.(CacheResp.enq)(response)
        else pass
    }}.


  Definition mem_write_turn (core: ind_core_id) : bits_t 2 :=
    match core with
    | CoreId0 => Ob~0~0
    | CoreId1 => Ob~1~0
    end.

  Definition cid_to_freeze_cycle (core_id: ind_core_id): bits_t 2 :=
    match core_id with
    | CoreId0 => Ob~1~1
    | CoreId1 => Ob~0~1
    end.

  Definition do_mem_req (core_id: ind_core_id): uaction reg_t ext_fn_t :=
    let fromIMem := fromMainMem imem core_id in
    let toIMem := toMainMem imem core_id in
    let fromDMem := fromMainMem dmem core_id in
    let toDMem := toMainMem dmem core_id in
    {{ guard(read0(freeze core_id) == Ob~0);
       guard(read0(turn) == #(mem_write_turn core_id));
       guard(read0(purge core_id) == enum purge_state { Ready } ||
             read0(purge core_id) == enum purge_state { Purging }
            );
       let wrote_this_turn := Ob~0 in
       (if (read0(priv_turn core_id)) then
         if ( fromIMem.(MemResp.can_enq)() && toIMem.(MemReqBypass.can_deq)())  then
           (let req := toIMem.(MemReqBypass.deq)() in
            set wrote_this_turn := Ob~1;
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~1;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else
           pass
       else (* (read0(priv_turn core_id) == Ob~1 *)
         if ( fromDMem.(MemResp.can_enq)() && toDMem.(MemReqBypass.can_deq)())  then
           (let req := toDMem.(MemReqBypass.deq)() in
            set wrote_this_turn := Ob~1;
            write0(SHReq, struct shreq { req := req;
                                         sourceType := Ob~0;
                                         sourceCore := (#(core_id_to_bits core_id));
                                         valid := Ob~1
                                        })
           )
         else pass);
       (* write0(priv_sent_req core_id, wrote_this_turn); *)
       write0((priv_turn core_id), read0(priv_turn core_id) + Ob~1)
    }}.

  Definition do_mem_resp (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    let fromIMem := fromMainMem imem core_id in
    let toIMem := toMainMem imem core_id in
    let fromDMem := fromMainMem dmem core_id in
    let toDMem := toMainMem dmem core_id in
    {{ guard(read0(freeze core_id) == Ob~0);
        guard(read0(purge core_id) == enum purge_state { Ready } ||
             read0(purge core_id) == enum purge_state { Purging }
            );
       guard(get(read1(SHResp), sourceCore) == #(core_id_to_bits core_id));
       guard(get(read1(SHResp), valid) == Ob~1);
       let resp := read1(SHResp) in
       let iorD := get(resp, sourceType) in (* I is 1, D is 0 *)
       let res := get(resp, resp) in
       (if ((iorD == Ob~0) && fromDMem.(MemResp.can_enq)()) then
          fromDMem.(MemResp.enq)(res)
        else if ((iorD == Ob~1) && fromIMem.(MemResp.can_enq)()) then
          fromIMem.(MemResp.enq)(res)
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

  Definition do_freeze (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard(read0(freeze core_id) == Ob~0);
       guard(read1(cacheState imem core_id) == enum cache_fsm_sig { Flushed });
       guard(read1(cacheState dmem core_id) == enum cache_fsm_sig { Flushed });
       write0(freeze core_id, Ob~1)
    }}.

  Definition do_init (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard (read0(purge core_id) == enum purge_state { Init } );
       write0(purge core_id, enum purge_state { Ready } )
    }}.

  Definition do_purge (core_id: ind_core_id) : uaction reg_t ext_fn_t :=
    let toIMem := coreToCache imem core_id in
    let toDMem := coreToCache dmem core_id in
    let fromMainMemImem := fromMainMem imem core_id in
    let fromMainMemDmem := fromMainMem dmem core_id in
    let toMainMemImem := toMainMem imem core_id in
    let toMainMemDmem := toMainMem dmem core_id in
    {{ guard(read0(freeze core_id) == Ob~1);
       guard(read0(purge core_id) == enum purge_state { Purging } );
       guard(read0(turn) == #(cid_to_freeze_cycle core_id));
       (* guard(!read1(priv_sent_req core_id)); *)
       guard(read1(cacheState imem core_id) == enum cache_fsm_sig { Flushed });
       guard(read1(cacheState dmem core_id) == enum cache_fsm_sig { Flushed });
       (* Need to be careful about backpressure *)
       if (!toIMem.(MemReq.can_deq)() &&
           (!toDMem.(MemReq.can_deq)()) &&
           (!toMainMemImem.(MemReqBypass.can_deq)()) &&
           (!toMainMemDmem.(MemReqBypass.can_deq)())) then
         (
           (* Reset private state *)
          write1(priv_turn core_id, Ob~0);
          toIMem.(MemReq.reset_all)();
          toDMem.(MemReq.reset_all)();
          toMainMemImem.(MemReqBypass.reset_all)();
          toMainMemDmem.(MemReqBypass.reset_all)();
          write1(cacheState imem core_id, enum cache_fsm_sig { Ready });
          write1(cacheState dmem core_id, enum cache_fsm_sig { Ready });
          write0(purge core_id, enum purge_state { Purged });
          write0(freeze core_id, Ob~0)

         ) else
           pass
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
  Definition tc_freeze0 := tc_rule R Sigma (do_freeze CoreId0).
  Definition tc_freeze1 := tc_rule R Sigma (do_freeze CoreId1).
  Definition tc_cache_req_imem0 := tc_rule R Sigma (do_cache_req imem CoreId0).
  Definition tc_cache_req_dmem0 := tc_rule R Sigma (do_cache_req dmem CoreId0).
  Definition tc_cache_req_imem1 := tc_rule R Sigma (do_cache_req imem CoreId1).
  Definition tc_cache_req_dmem1 := tc_rule R Sigma (do_cache_req dmem CoreId1).
  (* Definition tc_cache_resp_imem0 := tc_rule R Sigma (do_cache_resp imem CoreId0). *)
  (* Definition tc_cache_resp_dmem0 := tc_rule R Sigma (do_cache_resp dmem CoreId0). *)
  (* Definition tc_cache_resp_imem1 := tc_rule R Sigma (do_cache_resp imem CoreId1). *)
  (* Definition tc_cache_resp_dmem1 := tc_rule R Sigma (do_cache_resp dmem CoreId1). *)

  Definition tc_external_metadata_imem0 := tc_rule R Sigma (do_external_metadata imem CoreId0).
  Definition tc_external_metadata_imem1 := tc_rule R Sigma (do_external_metadata imem CoreId1).
  Definition tc_external_metadata_dmem0 := tc_rule R Sigma (do_external_metadata dmem CoreId0).
  Definition tc_external_metadata_dmem1 := tc_rule R Sigma (do_external_metadata dmem CoreId1).
  Definition tc_external_cache_imem0 := tc_rule R Sigma (do_external_cache imem CoreId0).
  Definition tc_external_cache_imem1 := tc_rule R Sigma (do_external_cache imem CoreId1).
  Definition tc_external_cache_dmem0 := tc_rule R Sigma (do_external_cache dmem CoreId0).
  Definition tc_external_cache_dmem1 := tc_rule R Sigma (do_external_cache dmem CoreId1).

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
    | Rl_doFreeze CoreId0 => tc_freeze0
    | Rl_doFreeze CoreId1 => tc_freeze1
    | Rl_doCacheReq imem CoreId0 => tc_cache_req_imem0
    | Rl_doCacheReq dmem CoreId0 => tc_cache_req_dmem0
    | Rl_doCacheReq imem CoreId1 => tc_cache_req_imem1
    | Rl_doCacheReq dmem CoreId1 => tc_cache_req_dmem1
    (* | Rl_doCacheResp imem CoreId0 => tc_cache_resp_imem0 *)
    (* | Rl_doCacheResp dmem CoreId0 => tc_cache_resp_dmem0 *)
    (* | Rl_doCacheResp imem CoreId1 => tc_cache_resp_imem1 *)
    (* | Rl_doCacheResp dmem CoreId1 => tc_cache_resp_dmem1 *)
    | Rl_doExternalMetadata imem CoreId0 => tc_external_metadata_imem0
    | Rl_doExternalMetadata dmem CoreId0 => tc_external_metadata_dmem0
    | Rl_doExternalMetadata imem CoreId1 => tc_external_metadata_imem1
    | Rl_doExternalMetadata dmem CoreId1 => tc_external_metadata_dmem1
    | Rl_doExternalCache imem CoreId0 => tc_external_cache_imem0
    | Rl_doExternalCache dmem CoreId0 => tc_external_cache_dmem0
    | Rl_doExternalCache imem CoreId1 => tc_external_cache_imem1
    | Rl_doExternalCache dmem CoreId1 => tc_external_cache_dmem1
    end.

  Instance Show_reg_t : Show reg_t := _.

  Definition schedule : @Syntax.scheduler Frontend.pos_t mem_rules_t :=
     Rl_doCacheReq imem CoreId0 |> Rl_doCacheReq dmem CoreId0 |>
     Rl_doCacheReq imem CoreId1 |> Rl_doCacheReq dmem CoreId1 |>
     Rl_doMemReq CoreId0 |>
     Rl_doMemReq CoreId1 |>
     Rl_doPurge CoreId0 |>
     Rl_doPurge CoreId1|>
     Rl_doExternalMetadata imem CoreId0 |> Rl_doExternalMetadata dmem CoreId0 |>
     Rl_doExternalMetadata imem CoreId1 |> Rl_doExternalMetadata dmem CoreId1 |>
     Rl_doExternalCache imem CoreId0 |> Rl_doExternalCache dmem CoreId0 |>
     Rl_doExternalCache imem CoreId1 |> Rl_doExternalCache dmem CoreId1 |>
     Rl_doExternalMem |>
     Rl_doMemResp CoreId0 |>
     Rl_doMemResp CoreId1 |>
     (* Rl_doCacheResp imem CoreId0 |> Rl_doCacheResp dmem CoreId0 |> *)
     (* Rl_doCacheResp imem CoreId1 |> Rl_doCacheResp dmem CoreId1 |> *)
     Rl_doInit CoreId0 |>
     Rl_doInit CoreId1 |>
     Rl_doFreeze CoreId0 |>
     Rl_doFreeze CoreId1 |>
     Rl_tick |> done.

End Memory.
