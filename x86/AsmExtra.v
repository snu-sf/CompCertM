Require Import Skeleton ModSem .
Require Import Integers.
Require Import CoqlibC ValuesC MemoryC.
Require Import LocationsC Conventions AsmregsC.
Require Import AsmC StoreArguments.

Set Implicit Arguments.


Lemma asm_initial_frame_succeed (asm: Asm.program) args fptr vs m skenv_link fd sg
      (ARGS: args = Args.Cstyle fptr vs m)
      (LEN: Datatypes.length vs = Datatypes.length (sig_args sg))
      (SIZE: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (FPTR: Genv.find_funct (SkEnv.revive (SkEnv.project skenv_link (Sk.of_program fn_sig asm)) asm) fptr =
            Some (Internal fd))
      (SIG: fd.(fn_sig) = Some sg)

  :
    exists st_init, initial_frame skenv_link asm args st_init.
Proof.
  exploit store_arguments_progress.
  { eapply typify_has_type_list; eauto. }
  { eauto. }
  i. des. instantiate (1:=m) in STR. instantiate (1:=0%nat) in PTRFREE.
  eexists (mkstate _ (Asm.State _ _)).
  econs; try apply ARGS; ss; eauto.
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
  - instantiate (1:=0%nat). i. unfold Pregmap.set, to_pregset in PTR. des_ifs; eauto.
    + exfalso. apply PTR. ss.
    + left. esplits; eauto. apply NNPP. eauto.
    + exfalso. apply PTR. ss.
Qed.
