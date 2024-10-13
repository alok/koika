(*! Common definitions *)
Require Import Koika.Frontend.
Require Import Coq.Lists.List.
Require Import Koika.Std.

Notation "r '||>' s" := (schedule_app r s)
      (at level 99, s at level 99, right associativity).


(*! Type defs *)
Definition purge_state :=
  {| enum_name := "purge_state";
     enum_members := ["Init"; "Ready"; "Purging"; "Purged"];
     enum_bitpatterns := vect_map (Bits.of_nat 2) [0; 1; 2; 3]
  |}%vect.

Definition mem_req :=
  {| struct_name := "mem_req";
     struct_fields := [("byte_en" , bits_t 4);
                       ("addr"     , bits_t 32);
                       ("data"     , bits_t 32)] |}.
Definition mem_resp :=
  {| struct_name := "mem_resp";
     struct_fields := [("byte_en", bits_t 4); ("addr", bits_t 32); ("data", bits_t 32)] |}.

Definition enclave_req :=
  {| struct_name := "enclave_req";
     struct_fields := [("eid", bits_t 2);
                       ("shared_regions", bits_t 6);
                       ("ext_uart", bits_t 1);
                       ("ext_led", bits_t 1);
                       ("ext_finish", bits_t 1)
                      ]
  |}.

Definition enclave_data:=
  {| struct_name := "enclave_data";
     struct_fields := [("data", struct_t enclave_req);
                       ("valid", bits_t 1)
                      ]
  |}.


Module FifoMemReq <: Fifo.
  Definition T:= struct_t mem_req.
End FifoMemReq.
Module MemReqBypass := Fifo1Bypass FifoMemReq.
Module MemReq:= Fifo1 FifoMemReq.

Module FifoMemResp <: Fifo.
  Definition T:= struct_t mem_resp.
End FifoMemResp.
Module MemRespBypass := Fifo1Bypass FifoMemResp.
Module MemResp := Fifo1 FifoMemResp.

(*! Helpers *)
Inductive ind_core_id :=
| CoreId0
| CoreId1.

(* External functions *)
Inductive ext_fn_t :=
| ext_mainmem
| ext_uart_read
| ext_uart_write
| ext_led
| ext_finish.

Definition FiniteType_ext_fn_t : FiniteType ext_fn_t := _.

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

Definition enum_core_state:=
  {| enum_name := "coreState";
     enum_members := ["Running"; "Purging"; "Purged"; "Waiting"];
     enum_bitpatterns := vect_map (Bits.of_nat 2) [0; 1; 2; 3]
  |}%vect.

Definition memoryBus_arg_sig :=
    {| struct_name := "memoryBus_arg";
       struct_fields := [("get_ready" , bits_t 1);
                         ("put_valid"     , bits_t 1);
                         ("put_request"     , struct_t mem_req)] |}.


Definition uart_input := maybe (bits_t 8).
Definition uart_output := maybe (bits_t 8).
Definition led_input := maybe (bits_t 1).
Definition finish_input := maybe (bits_t 8).

Definition Sigma (fn: ext_fn_t) :=
  match fn with
  | ext_mainmem => {$ struct_t mem_input ~> struct_t mem_output $}
  | ext_uart_read => {$ bits_t 1 ~> uart_output $}
  | ext_uart_write => {$ uart_input ~> bits_t 1 $}
  | ext_led => {$ led_input ~> bits_t 1 $}
  | ext_finish => {$ finish_input ~> bits_t 1 $}
  end.
Instance Show_ext_fn_t : Show ext_fn_t := _.

Definition core_id_to_bits (id: ind_core_id) : bits_t 1 :=
  match id with
  | CoreId0 => Ob~0
  | CoreId1 => Ob~1
  end.

(*! Enclave Config *)
Definition MMIO_UART_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0.
Definition MMIO_LED_ADDRESS  := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0.
Definition MMIO_EXIT_ADDRESS := Ob~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0.

Section EnclaveParams.
  Inductive enclave_id :=
  | Enclave0
  | Enclave1
  | Enclave2
  | Enclave3.

  Scheme Equality for enclave_id.

  Inductive shared_id :=
  | Shared01
  | Shared02
  | Shared03
  | Shared12
  | Shared13
  | Shared23
  .

  Definition addr_t : Type := bits_t 32.

  Record enclave_config :=
    { config_eid : enclave_id;
      config_shared_regions : shared_id -> bool;
      config_ext_uart: bool;
      config_ext_led: bool;
      config_ext_finish: bool
    }.
  Record core_init_params_t : Type :=
    { machine_pc: bits_t 32;
      (* machine_rf: reg_file_t; *)
      machine_config: option enclave_config
    }.

  Record enclave_params_sig :=
    { _enclave_base : enclave_id -> bits_t 32 (* Map from enclave ID to starting address *)
    ; _enclave_size : enclave_id -> bits_t 32 (* Size of each enclave region *)
    ; _enclave_bootloader_addr : enclave_id -> bits_t 32 (* Address when entering an enclave *)
    ; _shared_region_base : shared_id -> bits_t 32 (* Base address of each shared region *)
    ; _shared_region_size : bits_t 32 (* Size of each shared region *)
    ; _core_init0 : core_init_params_t (* Initial enclave config of Core0 *)
    ; _core_init1: core_init_params_t (* Initial enclave config of Core1 *)
    }.

  Definition enclave_id_to_bits (eid: enclave_id) : bits_t 2 :=
    match eid with
    | Enclave0 => Ob~0~0
    | Enclave1 => Ob~0~1
    | Enclave2 => Ob~1~0
    | Enclave3 => Ob~1~1
    end.

  Definition shared_regions_to_bits (regions: shared_id -> bool) : bits_t 6 :=
    Ob~(regions Shared23)~(regions Shared13)~(regions Shared12)~(regions Shared03)~(regions Shared02)~(regions Shared01).

  Definition enclave_config_to_enclave_request (config: enclave_config) : struct_t enclave_req :=
    (enclave_id_to_bits config.(config_eid),
      (shared_regions_to_bits config.(config_shared_regions),
        (Ob~config.(config_ext_uart), (Ob~config.(config_ext_led), (Ob~config.(config_ext_finish), tt))))).

 Definition opt_enclave_config_to_enclave_data (opt_config: option enclave_config) : struct_t enclave_data :=
   match opt_config with
   | Some config => (enclave_config_to_enclave_request config, (Ob~1, tt))
   | None => value_of_bits Bits.zero
   end.


End EnclaveParams.

Module Type EnclaveParams_sig.
  Parameter enclave_params : enclave_params_sig.
End EnclaveParams_sig.
