Require Import Koika.Frontend.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Common.
Require Import rv_isolation.Machine.


Module EnclaveParams <: EnclaveParams_sig.
  Definition enclave_base (eid: enclave_id) : addr_t :=
    Eval vm_compute in (
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end).
 Definition enclave_size (eid: enclave_id) : bits_t 32 :=
    Eval vm_compute in (
                 Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0).
 Definition enclave_bootloader_addr (eid: enclave_id) : addr_t :=
    Eval vm_compute in (
    match eid with
    | Enclave0 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0
    | Enclave1 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~1~0~0~0~0~0~0~0~0
    | Enclave2 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Enclave3 => Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end).

  Definition shared_region_base (id: shared_id) : addr_t :=
    Eval vm_compute in (
    match id with
    | Shared01 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared02 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared03 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared12 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared13 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    | Shared23 =>
        Ob~0~0~0~0~0~0~0~1~0~0~0~0~0~0~1~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0
    end).

  Definition shared_region_size : bits_t 32 :=
    Eval vm_compute in (
        Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0).

  Definition core_init0 : core_init_params_t :=
    Eval vm_compute in (
    {| machine_pc := Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
       machine_config := Some {| config_eid := Enclave0;
                                 config_shared_regions := fun sid =>
                                                            match sid with
                                                            | Shared01 => true
                                                            | Shared02 => true
                                                            | Shared03 => true
                                                            | _ => false
                                                            end;
                                 config_ext_uart := true;
                                 config_ext_led := true;
                                 config_ext_finish := true
                              |}
    |}).

  Definition core_init1 : core_init_params_t :=
    Eval vm_compute in (
    {| machine_pc := Ob~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
       machine_config := Some {| config_eid := Enclave1;
                                 config_shared_regions := fun _ => false;
                                 config_ext_uart := false;
                                 config_ext_led := false;
                                 config_ext_finish := false
                              |}
    |}).

  Definition enclave_params: enclave_params_sig :=
  {| _enclave_base := enclave_base;
     _enclave_size := enclave_size;
     _enclave_bootloader_addr := enclave_bootloader_addr;
     _shared_region_base :=shared_region_base;
     _shared_region_size := shared_region_size;
     _core_init0 := core_init0;
     _core_init1 :=  core_init1;
  |}.


End EnclaveParams.
