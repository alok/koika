(*! RV32 machine with two cores, a security monitor, and memory subsystem *)
Require Import Koika.Frontend.
Require Import Koika.Std.
Require Import Coq.Lists.List.
Require Import rv_isolation.Common.
Require Import rv_isolation.RVCore.
Require Import rv_isolation.Memory.
Require Import rv_isolation.SecurityMonitor.
Require Import rv_isolation.Lift.
Require Import rv_isolation.FiniteType.


Inductive rule_name_t :=
| RlCore0 (rl: rv_rules_t)
| RlCore1 (rl: rv_rules_t)
| RlSm (rl: sm_rules_t)
| RlMem (rl: mem_rules_t)
.

Module Type Machine_sig.
  (* Registers in the machine *)
  Parameter _reg_t : Type.
  (* External functions in the machine *)
  Parameter _ext_fn_t : Type.
  (* Type of each register *)
  Parameter R : _reg_t -> type.
  (* Type of each external function *)
  Parameter Sigma : _ext_fn_t -> ExternalSignature.
  (* Initial register state for simulation, as a function of Core0 and Core1's initial PCs, Core0 and Core1's enclave configuration, the Memory turn register, and the SM turn register. *)
  Parameter r : bits_t 32 -> bits_t 32 -> struct_t enclave_data -> struct_t enclave_data -> bits_t 2 -> bits_t 1 -> forall reg, R reg.
  (* Initial register state based on Core0 and Core1's enclave parameters, and public Memory/SM turn registers. *)
  Parameter r' : core_init_params_t -> core_init_params_t -> bits_t 2 -> bits_t 1 -> forall reg, R reg.
  (* Rules defined by the machine *)
  Parameter rules : rule_name_t -> rule R Sigma.
  (* The type of registers must be finite for hardware to be synthesizable! *)
  Parameter FiniteType_reg_t : FiniteType _reg_t.
  (* The type of external functions must be finite. *)
  Parameter FiniteType_ext_fn_t : FiniteType _ext_fn_t.

  (* Register->string for pretty-printing *)
  Parameter Show_reg_t : Show _reg_t.
  (* External function->string for pretty-printing *)
  Parameter Show_ext_fn_t : Show _ext_fn_t.
  Parameter ext_fn_sim_specs : _ext_fn_t -> ext_fn_sim_spec.
  Parameter ext_fn_rtl_specs : _ext_fn_t -> ext_fn_rtl_spec.
  (* The user-defined schedule, specifying the order in which rules _appear_ to execute. *)
  Parameter schedule : @Syntax.scheduler Frontend.pos_t rule_name_t.
End Machine_sig.


(* A machine is parameterised on enclave parameters, which specify the enclave regions and sizes. *)
Module Machine (EnclaveParams: EnclaveParams_sig) <: Machine_sig.
  Module SM := SM EnclaveParams.
  Definition _reg_t := SM._reg_t.
  Definition _ext_fn_t := ext_fn_t.
  Definition R := SM.R.
  Definition Sigma := SM.Sigma.
  Definition r := SM.r.

  Definition r' params0 params1 mem_turn sm_turn :=
    r params0.(machine_pc)
      params1.(machine_pc)
      (opt_enclave_config_to_enclave_data params0.(machine_config))
      (opt_enclave_config_to_enclave_data params1.(machine_config))
      mem_turn sm_turn.

  Definition FiniteType_reg_t : FiniteType _reg_t := SM.FiniteType_reg_t.
  Definition FiniteType_ext_fn_t : FiniteType _ext_fn_t := FiniteType_ext_fn_t.

  Definition Show_reg_t := SM.Show_reg_t.
  Definition Show_ext_fn_t := SM.Show_ext_fn_t.

  Definition ext_fn_sim_specs fn :=
    {| efs_name := show fn;
       efs_method := match fn with
                    | ext_finish => true
                    | _ => false
                    end |}.

  Definition ext_fn_rtl_specs fn :=
    {| efr_name := show fn;
       efr_internal := match fn with
                      | ext_finish => true
                      | _ => false
                      end |}.


  Definition Lift_core0 : RLift _ Core.reg_t _reg_t Core.R R := ltac:(mk_rlift Core0).
  Definition Lift_core1 : RLift _ Core.reg_t _reg_t Core.R R := ltac:(mk_rlift Core1).
  Definition Lift_mem : RLift _ Memory.reg_t _reg_t Memory.R R := ltac:(mk_rlift Memory).

  Definition Lift_fn_id  : RLift ExternalSignature ext_fn_t ext_fn_t Sigma Sigma := ltac:(mk_rlift_id).

  Definition lifted_core0_rules (rl: rv_rules_t) : rule R Sigma :=
    lift_rule Lift_core0 Lift_fn_id (Core.rv_rules rl).
  Definition lifted_core1_rules (rl: rv_rules_t) : rule R Sigma :=
    lift_rule Lift_core1 Lift_fn_id (Core.rv_rules rl).
  Definition lifted_mem_rules (rl: mem_rules_t) : rule R Sigma :=
    lift_rule Lift_mem Lift_fn_id (Memory.rules rl).

  Definition lifted_core0_schedule := lift_scheduler RlCore0 Core.schedule.
  Definition lifted_core1_schedule := lift_scheduler RlCore1 Core.schedule.
  Definition lifted_mem_schedule := lift_scheduler RlMem Memory.schedule.
  Definition lifted_sm_schedule := lift_scheduler RlSm SM.schedule.

  Definition rules rl :=
    match rl with
    | RlSm rl => SM.rules rl
    | RlCore0 rl => lifted_core0_rules rl
    | RlCore1 rl => lifted_core1_rules rl
    | RlMem rl => lifted_mem_rules rl
    end.

  (* The machine runs rules from Core0, Core1, the memory, and the SM. *)
  Definition schedule : @Syntax.scheduler Frontend.pos_t rule_name_t :=
    lifted_core0_schedule ||> lifted_core1_schedule ||> lifted_mem_schedule ||>  lifted_sm_schedule.

End Machine.
