Require Import CoqlibC.
Require Import Errors.
Require Import Unityping.
Require Import Maps.
Require Import AST.
Require Import Op.
Require Import Registers.
Require Import Globalenvs.
Require Import ValuesC.
Require Import IntegersC.
Require Import MemoryC.
Require Import Events.
Require Import RTLC.
Require Import Conventions.
Require Import sflib.
(** newly added **)
Require Import Skeleton ModSem Preservation.
Require Import SoundTop.
Require Import RTLC RTLtypingC0.

Section LPRSV.

  Variable prog: program.

  Hypothesis wt_prog:
    forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd
  .

  Theorem wt_state_local_preservation
          skenv_link
    :
      local_preservation (modsem skenv_link prog) (fun _ _ st => wt_state st)
  .
  Proof.
    econs; ii; ss; eauto.
    - (* init *)
      inv INIT.
      econs; et.
      + econs; et.
      + inv TYP. eapply typify_has_type_list; et.
    - (* step *)
      eapply subject_reduction; et.
      ii. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
      unfold Skeleton.SkEnv.revive in *.
      eapply Genv_map_defs_def in Heq. des. u in MAP. des_ifs_safe.
      esplits. eapply in_prog_defmap; eauto.
    - esplits; eauto.
      ii.
      inv AFTER.
      inv SUST.

      econs; et.
      admit "proj_sig_res change".
    - esplits; eauto. ss.
  Unshelve.
    all: ss.
  Qed.

End LPRSV.