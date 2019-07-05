Require Import Skeleton ModSem .
Require Import Integers.
Require Import CoqlibC ValuesC MemoryC.
Require Import LocationsC Conventions AsmregsC.
Require Import AsmC StoreArguments.

Set Implicit Arguments.


Lemma asm_initial_frame_succeed (asm: Asm.program) args skenv_link fd
      (ARGS: Datatypes.length args.(Args.vs) = Datatypes.length (sig_args fd.(fn_sig)))
      (SIZE: 4 * size_arguments fd.(fn_sig) <= Ptrofs.max_unsigned)
      (SIG: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig asm)) asm) (args.(Args.fptr)) =
            Some (Internal fd))
  :
    exists st_init, initial_frame skenv_link asm args st_init.
Proof.
  destruct args. ss.
  exploit store_arguments_progress.
  { eapply typify_has_type_list; eauto. }
  { eauto. }
  i. des. instantiate (1:=m) in STR.
  eexists (mkstate _ (Asm.State _ _)).
  econs; ss; eauto.
  - instantiate (1:= ((to_pregset rs) #PC <- fptr
                                      #RSP <- (Vptr (Mem.nextblock m) Ptrofs.zero)
                                      #RA <- Vnullptr)).
    ss.
  - econs; eauto.
  - econs.
    + inv STR. econs; eauto.
      eapply extcall_arguments_same; eauto.
      i. unfold to_mregset, to_pregset, Pregmap.set, to_preg, preg_of. des_ifs; ss; clarify.
    + des_ifs.
  - split.
    + des_ifs.
    + des_ifs.
  - i. des_ifs.
  - i. unfold Pregmap.set, to_pregset in PTR. des_ifs; eauto.
    + exfalso. apply PTR. ss.
    + left. esplits; eauto.
      apply NNPP. ii. exploit PTRFREE; eauto.
    + exfalso. apply PTR. ss.
      Unshelve. apply 0%nat.
Qed.
