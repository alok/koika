(*! Definition of a pipelined schedule !*)
Require Import Koika.Frontend.
Require Import rv_cache_isolation.RVCore.
Require Import rv_cache_isolation.Common.
Require Import rv_cache_isolation.Machine.
Require Import rv_cache_isolation.External.


Module Package.
  Import EnclaveParams.
  Module Import Machine := Machine EnclaveParams.

  Existing Instance Show_reg_t.
  Existing Instance Show_ext_fn_t.
  Existing Instance FiniteType_reg_t.

  Definition rule_external := fun (_: rule_name_t) => false.
  Definition circuits :=
    compile_scheduler rules rule_external schedule.

  Definition koika_package :=
    {| koika_reg_types := R;
       koika_reg_init := r enclave_params.(_core_init0).(machine_pc)
                           enclave_params.(_core_init1).(machine_pc)
                           (opt_enclave_config_to_enclave_data enclave_params.(_core_init0).(machine_config))
                           (opt_enclave_config_to_enclave_data enclave_params.(_core_init1).(machine_config))
                           (* TODO *) Ob~0~0 Ob~0;
       koika_ext_fn_types := Sigma;
       koika_rules := rules;
       koika_rule_external := rule_external;
       koika_scheduler := schedule;
       koika_module_name := "rv32" |}.

  Definition package :=
    {| ip_koika := koika_package;
       ip_sim := {| sp_ext_fn_specs := ext_fn_sim_specs;
                    sp_prelude := None |};
       ip_verilog := {| vp_ext_fn_specs := ext_fn_rtl_specs |} |}.
End Package.
