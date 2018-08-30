

Section SOUNDLPRESSBASE.


  Variable ms: ModSem.t.
  Context `{SU: Sound.class}.
  Variable sound_state_base: Sound.t -> ms.(ModSem.state) -> Prop.
  Hypothesis FIN: forall args, Finite {su0 : Sound.t | Sound.args su0 args}.
  (* Variable sound_state_base_at: forall *)
  (*     (su_at su_arg: Sound.t) (st: ms.(ModSem.state)) *)
  (*   , *)
  (*     Prop *)
  (* . *)

  (* Context `{FSL: FSL.class Sound.t Sound.le Sound.lub}. *)

  Let get_mem := ms.(ModSem.get_mem).

  Hypothesis INITSOUND: forall
      args su st0
      (ARGS: Sound.args su args)
      (INIT: ms.(ModSem.initial_frame) args st0)
    ,
      (<<SS: sound_state_base su st0>>) /\ (<<MLE: Sound.mle su args.(Args.m) st0.(get_mem)>>)
  .

  Inductive lifted (su_lifted: Sound.t) (args: Args.t): Prop :=
  | lifted_intro
      (ARGS: su_lifted.(Sound.args) args)
  .

  Hypothesis ATSOUND: forall
      su st0 args
      (SS: sound_state_base su st0)
      (AT: ModSem.at_external ms st0 args)
    ,
      (<<MLE: Sound.mle su st0.(get_mem) args.(Args.m)>>) /\
      exists su_lifted, (<<LE: Sound.le su su_lifted>>)
                        /\ (<<ARGS: su_lifted.(Sound.args) args>>)
                        (* /\ (<<SUAT: sound_state_base_at su su_lifted st0>>) *)
  .

  Hypothesis AFTERSOUND: forall
      su st0 retv su_g st1 args
      (SS: sound_state_base su st0)
      (RETV: Sound.retv su_g retv)
      (LE: Sound.le su su_g)
      (MLE: Sound.mle su_g args.(Args.m) retv.(Retv.m))
      (AFTER: ms.(ModSem.after_external) st0 retv st1)

      (GREATEST: forall su_lifted (ARGS: su_lifted.(Sound.args) args), <<LE: Sound.le su_lifted su_g>>)
      (HISTORY: ms.(ModSem.at_external) st0 args)
    ,
      <<SS: sound_state_base su st1>> /\ <<MLE: Sound.mle su retv.(Retv.m) st1.(get_mem)>>
  .

  Hypothesis FINALSOUND: forall
      su st0 retv
      (SS: sound_state_base su st0)
      (FINAL: ms.(ModSem.final_frame) st0 retv)
    ,
      <<RETV: Sound.retv su retv>> /\ <<MLE: Sound.mle su st0.(get_mem) retv.(Retv.m)>>
  .

  Hypothesis STEPSOUND: forall
      su st0 tr st1
      (SS: sound_state_base su st0)
      (STEP: ms.(ModSem.step) ms.(ModSem.globalenv) st0 tr st1)
    ,
      <<SS: sound_state_base su st1>> /\ <<MLE: Sound.mle su st0.(get_mem) st1.(get_mem)>>
  .

  Lemma sound_state_base_lpres_aux
        su st0 m_init
        (SS: sound_state_base su st0)
        (MLE: Sound.mle su m_init st0.(get_mem))
    :
      <<LPRES: lpres ms m_init su st0>>
  .
  (* Let sound_state_lpres_aux: forall *)
  (*       su st0 m_init *)
  (*       (SS: sound_state su st0) *)
  (*       (MLE: Sound.mle su m_init st0.(get_mem)) *)
  (*   , *)
  (*     <<LPRES: lpres ms m_init su st0>> *)
  (* . *)
  Proof.
    revert_until STEPSOUND.
    pcofix CIH.
    i.
    pfold.
    destruct (classic (ModSem.is_call ms st0)).
    {
      r in H. des.
      exploit ATSOUND; eauto. i; des.
      generalize (Sound.refined_FSL args); i.
      assert(INHAB: exists (su_lifted_refined: {su : Sound.t | Sound.args su args}), su_lifted_refined$ = su_lifted).
      { unshelve eexists (exist _ su_lifted _).
        - s. unshelve eauto.
        - s. unshelve eauto.
      }
      exploit (@FSL.find_greatest _ _ _ H0 (fun su => (su $).(Sound.args) args)); eauto.
      (* set (FSL := Sound.refined_FSL args). *)
      (* exploit (@FSL.find_greatest _ _ _ FSL (fun su => su.(Sound.args) args)); eauto. *)
      { ii. eapply Sound.refined_lub_args; eauto. }
      { des. exists su_lifted_refined. eauto with congruence. }
      i; des. destruct max as [su_greatest ARGS0].
      assert(Sound.le su_lifted su_greatest).
      { rr in MAX. ss. des. specialize (MAX0 su_lifted_refined). rp; [eapply MAX0|..]; eauto with congruence. }
      eapply lpres_at_external with (su_lifted := su_greatest); eauto.
      { etrans; eauto. }
      ii. exploit AFTERSOUND; eauto.
      { etrans; eauto. }
      { i. rr in MAX. des. ss.
        rp; [eapply MAX0|..]; eauto.
        - unshelve instantiate (1:= exist _ su_lifted0 _); ss.
        - ss.
      }
      i; des.
      right. eapply CIH; eauto.
      etrans; eauto.
      etrans; eauto.
      etrans; eauto.
      eapply Sound.le_spec; eauto.
      etrans; eauto.
    }
    destruct (classic (ModSem.is_return ms st0)).
    {
      r in H0. des.
      exploit FINALSOUND; eauto. i; des.
      econs 3; eauto.
      etrans; eauto.
    }
    econs; eauto.
    ii. hexpl STEPSOUND. right. eapply CIH; eauto. etrans; eauto.
  Qed.

  Theorem sound_state_base_lpres
          args su st0
          (ARGS: Sound.args su args)
          (INIT: ms.(ModSem.initial_frame) args st0)
    :
      <<LPRES: lpres ms args.(Args.m) su st0>>
  .
  Proof.
    hexpl INITSOUND.
    eapply sound_state_base_lpres_aux; eauto.
  Qed.

End SOUNDLPRESSBASE.







Require Import RTLC.
Require Import ValueDomain ValueAnalysis.
Require Import Linking.

Variable prog: RTL.program.
Variable skenv_link: SkEnv.t.
Let ms := RTLC.modsem skenv_link prog.


(* Remark: if econs/econsr gives different goal, at least 2 econs is possible *)
Ltac econsr :=
  first
    [
    econstructor 16
    |econstructor 15
    |econstructor 14
    |econstructor 13
    |econstructor 12
    |econstructor 11
    |econstructor 10
    |econstructor  9
    |econstructor  8
    |econstructor  7
    |econstructor  6
    |econstructor  5
    |econstructor  4
    |econstructor  3
    |econstructor  2
    |econstructor  1
    ]
.

Local Existing Instance Reach.

Definition bc2su (bound: block) (bc: block_classification): t' :=
  Top.mk (fun blk => bc blk = BCinvalid) bound
.

Lemma pmatch_sound
      bc bound blk ofs isreal aptr
      (PM: pmatch bc blk ofs isreal aptr)
      (BOUND: Plt blk bound)
  :
    <<SU: Sound.val bc.(bc2su bound) (Vptr blk ofs isreal)>>
.
Proof.
  ii; clarify. unfold bc2su; s. esplits; eauto.
  inv PM; eauto with congruence.
Qed.

Lemma vmatch_sound
      bc bound v av
      (VM: vmatch bc v av)
      (BOUND: forall blk ofs isreal bound (PTR: v = Vptr blk ofs isreal), Plt blk bound)
  :
    <<SU: Sound.val bc.(bc2su bound) v>>
.
Proof.
  inv VM; ss; eapply pmatch_sound; eauto.
Qed.

Local Transparent Mem.loadbytes.
Lemma smatch_sound
      bc bound m bpub aptr
      (BELOW: bc_below bc bound)
      (SM: smatch bc m bpub aptr)
      ofs
      (PERM : Mem.perm m bpub ofs Cur Readable)
  :
    <<SU: memval' bc.(bc2su bound) (ZMap.get ofs (Mem.mem_contents m) !! bpub)>>
.
Proof.
  inv SM.
  ii; clarify.
  assert(RPERM: Mem.range_perm m bpub ofs (ofs + 1) Cur Readable).
  { ii. assert(ofs1 = ofs) by xomega. clarify. }
  (* exploit (Mem.range_perm_loadbytes m bpub ofs 1); eauto. *)
  (* { ii. assert(ofs1 = ofs) by xomega. clarify. } *)
  (* i; des. *)
  exploit (H0 ofs); eauto.
  { unfold Mem.loadbytes. des_ifs. ss. rewrite PTR. eauto. }
  i.
  assert(bc blk <> BCinvalid).
  { inv H1; eauto with congruence. }
  assert(Plt blk bound).
  { eauto. }
  s. esplits; eauto.
Qed.

Lemma mmatch_sound
      bc m am
      (MM: mmatch bc m am)
  :
    <<SU: Sound.mem bc.(bc2su m.(Mem.nextblock)) m>>
.
Proof.
  inv MM; ss.
  econs; cycle 1.
  { ss. refl. }
  i; clarify.
  rename blk into bpub. (* rename blk0 into bpriv. *)
  specialize (mmatch_top bpub).
  ss. hexploit mmatch_top; eauto. i.
  eapply smatch_sound; eauto.
Qed.

Theorem VA_sound_state_base_lpres_aux
        args su st0
        (ARGS: Sound.args su args)
        (INIT: ms.(ModSem.initial_frame) args st0)
  :
    lpres ms args.(Args.m) su st0
.
Proof.
  eapply sound_state_base_lpres with (sound_state_base := sound_state_base prog ms.(globalenv)); eauto; ii; ss.
  - admit "init".
    (* inv INIT0. esplits; eauto. *)
    (* + econs; ss; eauto. *)
  - inv AT; inv SS; ss.
    split; [r; refl|].
    exists bc.(bc2su m0.(Mem.nextblock)).
    hexpl sound_stack_sound_compat COMPAT. inv COMPAT.
    esplits; eauto.
    { rr. ii. esplits; eauto. }
    + econs; ss; eauto.
      * ii; clarify. inv GE. unfold block in *. spc H1. exploit H1; eauto.
        { admit "ez". }
        i; des. rr in H. des; ss.
      * rewrite Forall_forall. i. eapply vmatch_sound; eauto.
      * eapply mmatch_sound; eauto.
  - inv AFTER. ss.
    des.
    assert(args0.(Args.m) = m_arg /\ args0.(Args.vs) = vs_arg).
    { inv HISTORY; ss. }
    clear HISTORY.
    des; clarify.
    inv SS.
    hexpl sound_stack_sound_compat COMPAT. inv COMPAT.
    esplits; eauto; try refl.
    assert(GLE: bc2su (Mem.nextblock (Args.m args0)) bc <1= su_g).
    { eapply GREATEST. econs; ss; eauto.
      - admit "history".
      - rewrite Forall_forall. i. eapply vmatch_sound. eapply ARGS0; eauto.
      - eapply mmatch_sound; eauto.
    }
    inv RETV.
    set (F := fun blk =>
                if plt blk args0.(Args.m).(Mem.nextblock)
                then bc blk
                else
                  if plt blk retv.(Retv.m).(Mem.nextblock)
                  then BCother
                  else BCinvalid).
    assert(exists (bc': block_classification), <<IMG: bc'.(bc_img) = F>>).
    { unshelve eexists (BC _ _ _); ss; eauto.
      - unfold F. ii. des_ifs. eapply bc_stack; eauto.
      - unfold F. ii. des_ifs. eapply bc_glob; eauto.
    } des.
    eapply sound_return_state with (bc := bc'); ss; eauto.
    (* econs; ss; eauto. *)
    + eapply sound_stack_new_bound.
      { eapply sound_stack_exten with (bc:=bc); eauto.
        - eapply sound_stack_ext; eauto.
          ii. inv MLE.
          erewrite <- Mem.loadbytes_unchanged_on_1; try apply PRIV0; eauto.
          ii. rr. eapply GLE; ss.
        - ii. rewrite IMG. unfold F. des_ifs.
      }
      inv MLE. ss.
    + clear - MM IMG F GLE VAL. destruct (Retv.v retv); ss; econs; eauto. destruct b0; ss; econs; eauto.
      rr in VAL. ii. hexpl VAL. eapply GLE. rr. rewrite IMG in *. unfold F in H. des_ifs. esplits; eauto.
      { rewrite IMG in *. unfold F in *. des_ifs. 
      inv MM. eapply mmatch_below; eauto.
      hexploit VAL; ss; eauto. eapply GLE; eauto.
      eapply 
        ttttttttttttttttt
        eapply LE; eauto.
        eapply Mem.loadbytes_unchanged_on; eauto.
        eapply Mem.loadbytes_unchanged_on_1; eauto.
      }
      econs; ss; eauto.
    destruct (pincl (am_nonstack am) Nonstack &&
                    forallb (fun av => vpincl av Nonstack) aargs)
             eqn: NOLEAK.

    econs; ss; eauto.
Qed.

Theorem VA_sound_state_lpres_aux
        m_init su st0
        (MLE: Sound.mle su m_init st0.(get_mem))
        (SS: sound_state prog ms.(globalenv) su st0)
  :
    lpres ms m_init su st0
.
Proof.
  eapply sound_state_lpres_aux with (sound_state := sound_state prog ms.(globalenv)); eauto.
  - ii. ss.
    inv SS0. inv AT; ss.
    esplits; eauto.
    + specialize (H prog (linkorder_refl _)). inv H; ss.
      assert(FPTR: vmatch bc fptr_arg Vtop).
      {
        des.
        unfold Genv.find_funct in *. des_ifs_safe.
        econsr. Undo. econs.
        econsr. Undo. econs.
        eapply GE. s.
        admit "ez".
      }
      hexpl sound_stack_sound_compat CPT. inv CPT.
      assert(VTOS: forall v, vmatch bc v Vtop -> su0.(Sound.val) v).
      { u. ii; clarify. exploit match_aptr_of_aval; eauto. intro P. inv P. eauto. }
      econs; ss; eauto.
      * admit "EZ".
      * econs. ii. clarify; ss.
        (* PTR: lookup public gives private. *)
        inv MM.
        destruct (classic (bc blk = BCinvalid)).
        { 
        specialize (mmatch_top blk). exploit mmatch_top; eauto.
        { ii. eapply inv H. clarify.
Qed.


Theorem VA_sound_state_lpres
        args su st0
        (ARGS: Sound.args su args)
        (INIT: ms.(ModSem.initial_frame) args st0)
        (SS: sound_state prog ms.(globalenv) su st0)
  :
    lpres ms args.(Args.m) su st0
.
Proof.
  eapply sound_state_lpres with (sound_state := sound_state prog ms.(globalenv)); eauto.
  - ii. inv INIT0.
    esplits; eauto.
    + econs; eauto.
      ii.

      econs; eauto.

  destruct 1.
  exploit initial_mem_matches; eauto. intros (bc & GE & BELOW & NOSTACK & RM & VALID).
  constructor; intros. apply sound_call_state with bc.
- constructor.
  econs; ii; ss; eauto.
- simpl; tauto.
- apply RM; auto.
- assert(CTX: Val.meminj_ctx).
  { apply Val.mi_normal. }
  apply mmatch_inj_top with m0.
  replace (inj_of_bc bc) with (Mem.flat_inj (Mem.nextblock m0)).
  eapply Genv.initmem_inject; eauto.
  symmetry; apply extensionality; unfold Mem.flat_inj; intros x.
  destruct (plt x (Mem.nextblock m0)).
  apply inj_of_bc_valid; auto.
  unfold inj_of_bc. erewrite bc_below_invalid; eauto.
- exact GE.
- exact NOSTACK.

Qed.