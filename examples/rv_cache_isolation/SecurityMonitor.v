Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.Lists.List.
Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Memory.
Require Import rv_cache_isolation.FiniteType.

Inductive sm_rules_t :=
| Rl_UpdateEnclave (core: ind_core_id)
| Rl_FilterReqs (core: ind_core_id)
| Rl_ForwardResps (core: ind_core_id)
| Rl_ExitEnclave (core: ind_core_id)
| Rl_EnterEnclave (core: ind_core_id)
| Rl_DoMMIO
| Rl_DoClk.

Section Helpers.
End Helpers.

Inductive sm_reg_t :=
| toMMIO0 (state: MemReqBypass.reg_t)
| toMMIO1 (state: MemReqBypass.reg_t)
| fromMMIO0 (state: MemRespBypass.reg_t)
| fromMMIO1 (state: MemRespBypass.reg_t)
| state (core: ind_core_id)
| enc_req (core: ind_core_id)
| enc_data (core: ind_core_id)
| sm_reset (core: ind_core_id)
| clk
.
Inductive reg_t :=
| Core0 (reg: Core._reg_t)
| Core1 (reg: Core._reg_t)
| Memory (reg: Memory._reg_t)
| SM (reg: sm_reg_t).
  Definition core_reg (core: ind_core_id) :=
    (match core with
     | CoreId0 => Core0
     | CoreId1 => Core1
     end).
  Definition toMemMMIO (core: ind_core_id) :=
    fun reg => SM ((match core with
                 | CoreId0 => toMMIO0
                 | CoreId1 => toMMIO1
                 end) reg).

  Definition fromMemMMIO (core: ind_core_id) :=
    fun reg => SM ((match core with
                 | CoreId0 => fromMMIO0
                 | CoreId1 => fromMMIO1
                 end) reg).


Existing Instance Core.FiniteType_reg_t.
Existing Instance Memory.FiniteType_reg_t.
Instance FiniteType_core: FiniteType ind_core_id := _.
Instance FiniteType_sm_reg_t : FiniteType sm_reg_t := _.
Import FiniteTypeHelpers.
Instance FiniteType_reg_t : FiniteType reg_t := ltac:(FiniteTypeHelpers.FiniteType_t'').
Instance Show_reg_t : Show reg_t := _.
Definition Show_ext_fn_t : Show ext_fn_t := Show_ext_fn_t.

Module Type SM_sig.
  Parameter _reg_t : Type.
  Parameter _ext_fn_t : Type.
  Parameter R : _reg_t -> type.
  Parameter Sigma : _ext_fn_t -> ExternalSignature.
  Parameter r : bits_t 32 -> bits_t 32 -> struct_t enclave_data -> struct_t enclave_data -> bits_t 2 -> bits_t 1 -> forall reg, R reg.
  Parameter rules : sm_rules_t -> rule R Sigma.
  Parameter FiniteType_reg_t : FiniteType _reg_t.
  Parameter Show_reg_t : Show _reg_t.
  Parameter Show_ext_fn_t : Show _ext_fn_t.
End SM_sig.


Module SM (Params: EnclaveParams_sig) <: SM_sig.



  Definition R_sm (r: sm_reg_t) : type :=
    match r with
    | toMMIO0 r => MemReqBypass.R r
    | toMMIO1 r => MemReqBypass.R r
    | fromMMIO0 r => MemRespBypass.R r
    | fromMMIO1 r => MemRespBypass.R r
    | state _ => enum_t enum_core_state
    | enc_req _ => struct_t enclave_data
    | enc_data _ => struct_t enclave_data
    | sm_reset _ => bits_t 1
    | clk => bits_t 1
    end.

  Definition r_sm enc_data0 enc_data1 (clk: bits_t 1) (idx: sm_reg_t) : R_sm idx :=
    match idx with
    | toMMIO0 r => MemReqBypass.r r
    | toMMIO1 r => MemReqBypass.r r
    | fromMMIO0 r => MemRespBypass.r r
    | fromMMIO1 r => MemRespBypass.r r
    | state _ => value_of_bits Bits.zero
    | enc_req _ => value_of_bits Bits.zero
    | sm_reset _ => Bits.zero
    | enc_data CoreId0 => enc_data0
    | enc_data CoreId1 => enc_data1
    | clk => clk
    end.



  Definition R (r: reg_t) : type :=
    match r with
    | Core0 r => Core.R r
    | Core1 r => Core.R r
    | Memory r => Memory.R r
    | SM r => R_sm r
    end.

  Definition r (init_pc0: bits_t 32) (init_pc1: bits_t 32) enc_data0 enc_data1 (turn: bits_t 2) (sm_turn: bits_t 1) (idx: reg_t) : R idx :=
    match idx with
    | Core0 idx => Core.r Ob~0 init_pc0 idx
    | Core1 idx => Core.r Ob~1 init_pc1 idx
    | Memory idx =>  Memory.r turn idx
    | SM idx => r_sm enc_data0 enc_data1 sm_turn idx
    end.

  Local Notation "'__core0__' instance " :=
    (fun reg => Core0 ((instance) reg)) (in custom koika at level 1, instance constr at level 99).
  Local Notation "'__sm__' instance " :=
    (fun reg => SM ((instance) reg)) (in custom koika at level 1, instance constr at level 99).

  Local Notation "'(' instance ').(' method ')' args" :=
      (USugar (UCallModule (instance) _ method args))
        (in custom koika at level 1, method constr, args custom koika_args at level 99).

  Definition fromCoreDmem (core: ind_core_id) :=
    fun reg => core_reg core (Core.toDMem reg).

  Definition fromCoreImem (core: ind_core_id) :=
    fun reg => core_reg core (Core.toIMem reg).

  Definition fromCoreEnclave (core: ind_core_id) :=
    fun reg => core_reg core (Core.toSM reg).


  Definition toCoreDmem (core: ind_core_id) :=
    fun reg => core_reg core (Core.fromDMem reg).

  Definition toCoreImem (core: ind_core_id) :=
    fun reg => core_reg core (Core.fromIMem reg).

  Definition fromCoreMMIO (core: ind_core_id) :=
    fun reg => core_reg core (Core.toMMIO reg).

  Definition toCoreMMIO (core: ind_core_id) :=
    fun reg => core_reg core (Core.fromMMIO reg).


  Definition toMemDmem (core: ind_core_id) :=
    fun reg => Memory ((match core with
                     | CoreId0 => Memory.toDMem0
                     | CoreId1 => Memory.toDMem1
                     end) reg).

  Definition toMemImem (core: ind_core_id) :=
    fun reg => Memory ((match core with
                     | CoreId0 => Memory.toIMem0
                     | CoreId1 => Memory.toIMem1
                     end) reg).

  Definition fromMemDmem (core: ind_core_id) :=
    fun reg => Memory ((match core with
                     | CoreId0 => Memory.fromDMem0
                     | CoreId1 => Memory.fromDMem1
                     end) reg).

  Definition fromMemImem (core: ind_core_id) :=
    fun reg => Memory ((match core with
                     | CoreId0 => Memory.fromIMem0
                     | CoreId1 => Memory.fromIMem1
                     end) reg).

  Definition enclave_req_and_addr :=
    {| struct_name := "enclave_req_and_addr";
       struct_fields := [("req" , struct_t enclave_req);
                         ("addr"     , bits_t 32)
                        ]
    |}.

  Definition sm_filter_reqs' {T1 T2}
    (filter_fn: UInternalFunction reg_t empty_ext_fn_t) (reg_enc: reg_t)
    (fromCore : T1 -> reg_t) (can_deq: UInternalFunction T1 empty_ext_fn_t)
                            (deq: UInternalFunction T1 empty_ext_fn_t)
    (toMem: T2 -> reg_t) (can_enq: UInternalFunction T2 empty_ext_fn_t)
                        (enq: UInternalFunction T2 empty_ext_fn_t)
    : uaction reg_t ext_fn_t :=
    {{ if (fromCore.(can_deq)() && toMem.(can_enq)()) then
         let request := fromCore.(deq)() in
         let address := get(request, addr) in
         let enc_data := read0(reg_enc) in
         let enc_valid := get(enc_data, valid) in
         let enc_data_and_addr :=
           struct enclave_req_and_addr { req := get(enc_data, data);
                                         addr := address } in
         if (filter_fn (enc_data_and_addr) && enc_valid) then (* TODO! *)
           toMem.(enq)(request)
         else pass
       else pass
    }}.


  Definition sm_forward_resps'
    (fromMem : MemRespBypass.reg_t -> reg_t) (toCore: MemResp.reg_t -> reg_t) : uaction reg_t ext_fn_t :=
    {{ if (fromMem.(MemRespBypass.can_deq)() && toCore.(MemResp.can_enq)()) then
         let request := fromMem.(MemRespBypass.deq)() in
         toCore.(MemResp.enq)(request)
       else pass
    }}.

  Definition addr_in_eid_range : UInternalFunction reg_t empty_ext_fn_t :=
    let enclave_base := Params.enclave_params.(_enclave_base) in
    {{ fun addr_in_eid_range (arg: struct_t enclave_req_and_addr) : bits_t 1 =>
       let req := get(arg,req) in
       let addr := get(arg,addr) in
       let eid := get(req, eid) in
       match eid with
       | #Ob~0~0 =>
           let addr_min := #(Params.enclave_params.(_enclave_base) Enclave0) in
           let addr_max := #(Params.enclave_params.(_enclave_size) Enclave0) + addr_min in
           (addr_min <= addr) && (addr < addr_max)
       | #Ob~0~1 =>
           let addr_min := #(Params.enclave_params.(_enclave_base) Enclave1) in
           let addr_max := #(Params.enclave_params.(_enclave_size) Enclave1) + addr_min in
           (addr_min <= addr) && (addr < addr_max)
       | #Ob~1~0 =>
           let addr_min := #(Params.enclave_params.(_enclave_base) Enclave2) in
           let addr_max := #(Params.enclave_params.(_enclave_size) Enclave2) + addr_min in
           (addr_min <= addr) && (addr < addr_max)
       | #Ob~1~1 =>
           let addr_min := #(Params.enclave_params.(_enclave_base) Enclave3) in
           let addr_max := #(Params.enclave_params.(_enclave_size) Enclave3) + addr_min in
           (addr_min <= addr) && (addr < addr_max)
       return default:Ob~0
       end
    }}.

  Definition addr_in_shared_range : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun addr_in_shared_range (arg: struct_t enclave_req_and_addr) : bits_t 1 =>
       let req := get(arg,req) in
       let addr := get(arg,addr) in
       let shared := get(req, shared_regions) in
       let shared01_base := #(Params.enclave_params.(_shared_region_base) Shared01) in
       let shared02_base := #(Params.enclave_params.(_shared_region_base) Shared02) in
       let shared03_base := #(Params.enclave_params.(_shared_region_base) Shared03) in
       let shared12_base := #(Params.enclave_params.(_shared_region_base) Shared12) in
       let shared13_base := #(Params.enclave_params.(_shared_region_base) Shared13) in
       let shared23_base := #(Params.enclave_params.(_shared_region_base) Shared23) in
       let shared_size := #(Params.enclave_params.(_shared_region_size)) in
       (shared[|3`d0|] && (shared01_base <= addr) && (addr < (shared01_base + shared_size))) ||
       (shared[|3`d1|] && (shared02_base <= addr) && (addr < (shared02_base + shared_size))) ||
       (shared[|3`d2|] && (shared03_base <= addr) && (addr < (shared03_base + shared_size))) ||
       (shared[|3`d3|] && (shared12_base <= addr) && (addr < (shared12_base + shared_size))) ||
       (shared[|3`d4|] && (shared13_base <= addr) && (addr < (shared13_base + shared_size))) ||
       (shared[|3`d5|] && (shared23_base <= addr) && (addr < (shared23_base + shared_size)))
    }}.

  Definition valid_addr_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{
        fun valid_addr_req (arg: struct_t enclave_req_and_addr) : bits_t 1 =>
          addr_in_eid_range(arg) || addr_in_shared_range (arg)
    }}.

  Definition addr_in_ext_range : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun addr_in_ext_range (arg: struct_t enclave_req_and_addr) : bits_t 1 =>
         let req := get(arg,req) in
         let addr := get(arg,addr) in
         let ok_uart := get(req, ext_uart) in
         let ok_led := get(req, ext_led) in
         let ok_finish := get(req, ext_finish) in
         (ok_uart && (addr == #MMIO_UART_ADDRESS)) ||
         (ok_led && (addr == #MMIO_LED_ADDRESS)) ||
         (ok_finish && (addr == #MMIO_EXIT_ADDRESS))
    }}.

  Definition sm_filter_reqs (core: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard(read0(SM(state core)) == enum enum_core_state { Running });
       `sm_filter_reqs' valid_addr_req (SM (enc_data core))
                        (fromCoreDmem core) MemReqBypass.can_deq MemReqBypass.deq
                        (toMemDmem core) MemReq.can_enq MemReq.enq `;
       `sm_filter_reqs' valid_addr_req (SM (enc_data core))
                        (fromCoreImem core) MemReqBypass.can_deq MemReqBypass.deq
                        (toMemImem core) MemReq.can_enq MemReq.enq `;
       `sm_filter_reqs' addr_in_ext_range (SM (enc_data core))
                        (fromCoreMMIO core) MemReqBypass.can_deq MemReqBypass.deq
                        (toMemMMIO core) MemReqBypass.can_enq MemReqBypass.enq`
    }}.

  Definition sm_forward_resps (core: ind_core_id) : uaction reg_t ext_fn_t :=
    {{ guard(read0(SM(state core)) == enum enum_core_state { Running });
       `sm_forward_resps' (fromMemDmem core) (toCoreDmem core)`;
       `sm_forward_resps' (fromMemImem core) (toCoreImem core)`;
       `sm_forward_resps' (fromMemMMIO core) (toCoreMMIO core)`
    }}.

  Definition mmioBus : UInternalFunction reg_t ext_fn_t :=
    {{ fun mmioBus (arg: struct_t memoryBus_arg_sig) : struct_t mem_output =>
         let get_ready := get(arg, get_ready) in
         let put_valid := get(arg, put_valid) in
         let put_request := get(arg, put_request) in
         let addr := get(put_request, addr) in
         let byte_en := get(put_request, byte_en) in
         let is_write := byte_en == Ob~1~1~1~1 in
         let is_uart := addr == #MMIO_UART_ADDRESS in
         let is_uart_read := is_uart && !is_write in
         let is_uart_write := is_uart && is_write in

         let is_led := addr == #MMIO_LED_ADDRESS in
         let is_led_write := is_led && is_write in

         let is_finish := addr == #MMIO_EXIT_ADDRESS in
         let is_finish_write := is_finish && is_write in

         if is_uart_write then
           let char := get(put_request, data)[|5`d0| :+ 8] in
           let may_run := get_ready && put_valid && is_uart_write in
           let ready := extcall ext_uart_write (struct (Maybe (bits_t 8)) {
             valid := may_run; data := char }) in
           struct mem_output { get_valid := may_run && ready;
                               put_ready := may_run && ready;
                               get_response := struct mem_resp {
                                  byte_en := byte_en; addr := addr;
                                  data := |32`d0| } }

         else if is_uart_read then
           let may_run := get_ready && put_valid && is_uart_read in
           let opt_char := extcall ext_uart_read (may_run) in
           let ready := get(opt_char, valid) in
           struct mem_output { get_valid := may_run && ready;
                               put_ready := may_run && ready;
                               get_response := struct mem_resp {
                                  byte_en := byte_en; addr := addr;
                                  data := zeroExtend(get(opt_char, data), 32) } }

         else if is_led then
           let on := get(put_request, data)[|5`d0|] in
           let may_run := get_ready && put_valid && is_led_write in
           let current := extcall ext_led (struct (Maybe (bits_t 1)) {
             valid := may_run; data := on }) in
           let ready := Ob~1 in
           struct mem_output { get_valid := may_run && ready;
                               put_ready := may_run && ready;
                               get_response := struct mem_resp {
                                 byte_en := byte_en; addr := addr;
                                 data := zeroExtend(current, 32) } }
         else if is_finish then
           let char := get(put_request, data)[|5`d0| :+ 8] in
           let may_run := get_ready && put_valid && is_finish_write in
           let response := extcall ext_finish (struct (Maybe (bits_t 8)) {
             valid := may_run; data := char }) in
           let ready := Ob~1 in
           struct mem_output { get_valid := may_run && ready;
                               put_ready := may_run && ready;
                               get_response := struct mem_resp {
                                 byte_en := byte_en; addr := addr;
                                 data := zeroExtend(response, 32) } }
         else
           struct mem_output { get_valid := Ob~0;
                               put_ready := Ob~0;
                               get_response := `UConst (tau := struct_t mem_resp) (value_of_bits Bits.zero)`
                             }
    }}.

  Definition sm_do_mmio : uaction reg_t ext_fn_t :=
    {{ let put_request_opt := `UConst (tau := maybe (struct_t mem_req)) (value_of_bits Bits.zero)` in
       let get_ready := Ob~0 in
       let from_core0 :=
         (read0(SM clk) == Ob~0) &&
         (read0(SM (state CoreId0)) == enum enum_core_state { Running }) &&
         ((__sm__ toMMIO0).(MemReqBypass.can_deq)()) &&
         ((__sm__ fromMMIO0).(MemRespBypass.can_enq)()) in
       let from_core1 :=
         (read0(SM clk) == Ob~1) &&
         (read0(SM (state CoreId1)) == enum enum_core_state { Running }) &&
         ((__sm__ toMMIO1).(MemReqBypass.can_deq)()) &&
         ((__sm__ fromMMIO1).(MemRespBypass.can_enq)()) in
       (if from_core0 then
          (set put_request_opt := (__sm__ toMMIO0).(MemReqBypass.peek)();
           set get_ready := Ob~1)
        else if from_core1 then
          (set put_request_opt := (__sm__ toMMIO1).(MemReqBypass.peek)();
           set get_ready := Ob~1)
        else pass);
        let put_request := get(put_request_opt, data) in
        let put_valid := get(put_request_opt, valid) in
        let response := mmioBus(struct memoryBus_arg_sig { get_ready := get_ready;
                                                           put_valid := put_valid;
                                                           put_request := put_request }) in
        let is_response := get(response, get_valid) in
        (if (is_response && from_core0) then
             ( ignore((__sm__ toMMIO0).(MemReqBypass.deq)());
             (__sm__ fromMMIO0).(MemRespBypass.enq)(get(response, get_response)))
         else if (is_response && from_core1) then
             ( ignore((__sm__ toMMIO1).(MemReqBypass.deq)());
             (__sm__ fromMMIO1).(MemRespBypass.enq)(get(response, get_response)))
         else if ((read0(SM clk) == Ob~0) &&
           (read0 (SM (state CoreId0)) == enum enum_core_state { Purging })) then
           (write0(SM (sm_reset (CoreId0)), Ob~1);
            (__sm__ toMMIO0).(MemReqBypass.reset_all)())
         else if ((read0(SM clk) == Ob~1) &&
                  (read0 (SM (state CoreId1)) == enum enum_core_state { Purging })) then
           (write0(SM (sm_reset (CoreId1)), Ob~1);
            (__sm__ toMMIO1).(MemReqBypass.reset_all)())
       else pass)
    }}.

  Definition sm_do_clk : uaction reg_t ext_fn_t :=
   {{ write0 (SM clk, !read0(SM clk)) }}.

  Definition valid_shared_regions : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun valid_shared_regions (arg: struct_t enclave_req ) : bits_t 1  =>
         let eid := get(arg, eid) in
         let shared_regions := get(arg, shared_regions) in
         match eid with
         | #Ob~0~0 => shared_regions[|3`d3|:+3] == Ob~0~0~0
         | #Ob~0~1 => (shared_regions[|3`d1|] ++ shared_regions[|3`d2|] ++ shared_regions[|3`d5|]) == Ob~0~0~0
         | #Ob~1~0 => (shared_regions[|3`d0|] ++ shared_regions[|3`d2|] ++ shared_regions[|3`d4|]) == Ob~0~0~0
         | #Ob~1~1 => (shared_regions[|3`d0|] ++ shared_regions[|3`d1|] ++ shared_regions[|3`d3|]) == Ob~0~0~0
         return default:Ob~0
         end
    }}.

  Definition valid_enclave_req : UInternalFunction reg_t empty_ext_fn_t :=
    {{ fun valid_enclave_req (arg: struct_t enclave_req) : bits_t 1 =>
         valid_shared_regions (arg)
    }}.

  Definition core_enter_clk (core: ind_core_id) :=
    match core with
    | CoreId0 => Ob~0
    | CoreId1 => Ob~1
    end.

  Definition other_core (core: ind_core_id) : ind_core_id :=
    match core with
    | CoreId0 => CoreId1
    | CoreId1 => CoreId0
    end.

  Definition eid_to_bootloader_addr: UInternalFunction reg_t empty_ext_fn_t :=
     {{ fun eid_to_bootloader_addr (eid: bits_t 2) : bits_t 32 =>
          match eid with
          | #Ob~0~0 => #(Params.enclave_params.(_enclave_bootloader_addr) Enclave0)
          | #Ob~0~1 => #(Params.enclave_params.(_enclave_bootloader_addr) Enclave1)
          | #Ob~1~0 => #(Params.enclave_params.(_enclave_bootloader_addr) Enclave2)
          | #Ob~1~1 => #(Params.enclave_params.(_enclave_bootloader_addr) Enclave3)
          return default : |32`d0|
          end
    }}.


  Definition sm_enter_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let core_lift := core_reg core in
    {{
        guard(read0(SM (state core)) == enum enum_core_state { Waiting } );
        guard(read0(SM clk) == #(core_enter_clk core));
        let enc_req := read0(SM(enc_req core)) in
        let enc_data := get(enc_req,data) in
        let eid := get(enc_data, eid) in
        let shared_req := get(enc_data, shared_regions) in
        let ext_uart := get(enc_data, ext_uart) in
        let ext_led := get(enc_data, ext_led) in
        let ext_finish := get(enc_data, ext_finish) in

        let canSwitchToEnc :=
          (let other_enc_data := read0(SM (enc_data (other_core core))) in
           let other_enc_config := get(other_enc_data, data) in
           (* Enclave is not valid or regions are disjoint *)
           ((!get(other_enc_data, valid)) ||
            ((get(other_enc_config, eid) != eid) &&
             ((get(other_enc_config, shared_regions)  &&  shared_req) == Ob~0~0~0~0~0~0) &&
             (!(get(other_enc_config, ext_uart) && ext_uart)) &&
             (!(get(other_enc_config, ext_led) && ext_led)) &&
             (!(get(other_enc_config, ext_finish) && ext_finish))
            ))) in
        if canSwitchToEnc then
          (write0(SM(enc_data core), enc_req);
           write0(SM(enc_req core), `UConst (tau := struct_t enclave_data) (value_of_bits Bits.zero)`);
           write0(SM(state core), enum enum_core_state { Running });
           core_lift.(Core.write1_purge)(enum purge_state { Init });
           Memory.(Memory.write1_purge core)(enum purge_state {Init});
           (* set initial pc *)
           core_lift.(Core.write1_init_pc)(eid_to_bootloader_addr(eid))
          )
        else pass
    }}.

  Definition sm_update_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let fromCoreEnclave := fromCoreEnclave core in
    let core_lift := core_reg core in
    {{
        guard(read0(SM (state core)) == enum enum_core_state { Running });
        let enclaveReq := fromCoreEnclave.(Core.toSMEnc.deq)() in
        if valid_enclave_req(enclaveReq) then
          (write0(SM (state core), enum enum_core_state { Purging });
           write0(SM (enc_req core), struct enclave_data { data := enclaveReq;
                                                           valid := Ob~1 });
           core_lift.(Core.write1_purge)(enum purge_state { Purging } );
           Memory.(Memory.write1_purge core)(enum purge_state {Purging})
          )
        else
          pass
    }}.

  Definition reset_fifos (core: ind_core_id): uaction reg_t ext_fn_t :=
    let fromCoreImem := fromCoreImem core in
    let fromCoreDmem := fromCoreDmem core in
    let fromCoreMMIO := fromCoreMMIO core in
    let fromCoreEnclave := fromCoreEnclave core in
    let fromMemImem := fromMemImem core in
    let fromMemDmem := fromMemDmem core in
    let fromMemMMIO := fromMemMMIO core in
    {{
        fromCoreImem.(MemReqBypass.reset_all)();
        fromCoreDmem.(MemReqBypass.reset_all)();
        fromCoreMMIO.(MemReqBypass.reset_all)();
        fromCoreEnclave.(Core.toSMEnc.reset_all)();
        fromMemImem.(MemRespBypass.reset_all)();
        fromMemDmem.(MemRespBypass.reset_all)();
        fromMemMMIO.(MemRespBypass.reset_all)()
    }}.


  Definition sm_exit_enclave (core: ind_core_id) : uaction reg_t ext_fn_t :=
    let core_lift := core_reg core in
    {{ guard(read0(SM (state core)) == enum enum_core_state { Purging });
       guard(core_lift.(Core.read1_purge)() == enum purge_state { Purged });
       guard(Memory.(Memory.read1_purge core)() == enum purge_state { Purged });
       guard(read1(SM (sm_reset core)));
       (* TODO: RESET FIFOS *)
       `reset_fifos core`;
       (* Exit enclave *)
       write0(SM (state core), enum enum_core_state { Waiting });
       write0(SM (enc_data core), `UConst (tau := struct_t enclave_data) (value_of_bits Bits.zero)`);
       write1(SM (sm_reset core), Ob~0)
    }}.



  Definition _reg_t := reg_t.
  Definition _ext_fn_t := ext_fn_t.


  Definition uart_input := maybe (bits_t 8).
  Definition uart_output := maybe (bits_t 8).
  Definition led_input := maybe (bits_t 1).
  Definition finish_input := maybe (bits_t 8).

  Definition tc_update_enclave0:= tc_rule R Sigma (sm_update_enclave (CoreId0)).
  Definition tc_update_enclave1 := tc_rule R Sigma (sm_update_enclave (CoreId1)).
  Definition tc_filter_reqs0 := tc_rule R Sigma (sm_filter_reqs (CoreId0)).
  Definition tc_filter_reqs1 := tc_rule R Sigma (sm_filter_reqs (CoreId1)).
  Definition tc_forward_resps0 := tc_rule R Sigma (sm_forward_resps (CoreId0)).
  Definition tc_forward_resps1 := tc_rule R Sigma (sm_forward_resps (CoreId1)).
  Definition tc_exit_enclave0:= tc_rule R Sigma (sm_exit_enclave (CoreId0)).
  Definition tc_exit_enclave1 := tc_rule R Sigma (sm_exit_enclave (CoreId1)).
  Definition tc_enter_enclave0:= tc_rule R Sigma (sm_enter_enclave (CoreId0)).
  Definition tc_enter_enclave1 := tc_rule R Sigma (sm_enter_enclave (CoreId1)).
  Definition tc_do_mmio := tc_rule R Sigma sm_do_mmio.
  Definition tc_do_clk := tc_rule R Sigma sm_do_clk.

  Definition rules (rl: sm_rules_t) : rule R Sigma :=
    match rl with
    | Rl_UpdateEnclave CoreId0 => tc_update_enclave0
    | Rl_UpdateEnclave CoreId1 => tc_update_enclave1
    | Rl_FilterReqs CoreId0 => tc_filter_reqs0
    | Rl_FilterReqs CoreId1 => tc_filter_reqs1
    | Rl_ForwardResps CoreId0 => tc_forward_resps0
    | Rl_ForwardResps CoreId1 => tc_forward_resps1
    | Rl_ExitEnclave CoreId0 => tc_exit_enclave0
    | Rl_ExitEnclave CoreId1 => tc_exit_enclave1
    | Rl_EnterEnclave CoreId0 => tc_enter_enclave0
    | Rl_EnterEnclave CoreId1 => tc_enter_enclave1
    | Rl_DoMMIO => tc_do_mmio
    | Rl_DoClk => tc_do_clk
    end.


  Definition schedule : @Syntax.scheduler Frontend.pos_t sm_rules_t :=
         Rl_FilterReqs CoreId0 |> Rl_FilterReqs CoreId1
      |> Rl_DoMMIO
      |> Rl_ForwardResps CoreId0 |> Rl_ForwardResps CoreId1
      |> Rl_UpdateEnclave CoreId0 |> Rl_UpdateEnclave CoreId1
      |> Rl_EnterEnclave CoreId0 |> Rl_EnterEnclave CoreId1
      |> Rl_ExitEnclave CoreId0 |> Rl_ExitEnclave CoreId1
      |> Rl_DoClk
      |> done.
  Definition Sigma := Sigma.

  Definition FiniteType_reg_t := FiniteType_reg_t.
  Definition Show_reg_t := Show_reg_t.
  Definition Show_ext_fn_t := Show_ext_fn_t.
End SM.
