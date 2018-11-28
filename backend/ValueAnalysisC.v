Require Import FunInd.
Require Import CoqlibC Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import ValuesC Memory Globalenvs Events.
Require Import Registers Op RTLC.
Require Import ValueDomain ValueAOp Liveness.
Require Import sflib.
(** copied && added C **)
Require Import Skeleton.
Require Export ValueAnalysis.
Require Import Preservation.
Require Import UnreachC.
Require Import Sound.
Require Import ModSem.


(* Definition bc2su (bc: block_classification) (ge_nb: block) (bound: block): Unreach.t := *)
(*   Unreach.mk (fun blk => if plt blk bound *)
(*                          then block_class_eq (bc blk) BCinvalid *)
(*                          else false) *)
(*              ge_nb *)
(*              bound *)
(* . *)
(* Hint Unfold bc2su. *)


(* Tactic Notation "spc" hyp(H) := spc H. *)
(* Tactic Notation "spc" hyp(H) constr(n) := spcN H n. *)



Lemma sound_state_sound_args
      bc m0 stack su0 p skenv_link vs_arg cunit
      ge
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (defs p)) p))
      (STK: sound_stack cunit ge su0 bc stack m0 (Mem.nextblock m0))
      (ARGS: forall v : val, In v vs_arg -> vmatch bc v Vtop)
      (RO: romatch bc m0 (romem_for cunit))
      (MM: mmatch bc m0 mtop)
      (GE: genv_match bc ge)
      (NOSTK: bc_nostack bc)
      fptr_arg sg_arg
      (SIG: exists skd, Genv.find_funct skenv_link fptr_arg = Some skd /\ SkEnv.get_sig skd = sg_arg)
  :
    args' (bc2su bc ge.(Genv.genv_next) m0.(Mem.nextblock)) (Args.mk fptr_arg vs_arg m0)
.
Proof.
  { r. s. esplits; eauto.
    - des. unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs. ss. r. ii; clarify. ss.
      r in GE. des. specialize (GE0 blk). exploit GE0; eauto.
      { ss. eapply Genv.genv_defs_range; eauto. }
      i; des.
      (* exploit sound_stack_unreach_compat; eauto. intro CPT. des. *)
      (* inv SU. ss. *)
      esplits; eauto.
      + ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
    - rewrite Forall_forall. i. spcN 1 ARGS. spc ARGS. ii; clarify.
      assert(BCV: bc blk <> BCinvalid).
      { inv ARGS; ss. inv H1; ss. }
      esplits; eauto.
      + u. ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
    - inv MM. econs; eauto.
      + ii. clarify.
        assert(BCV: bc blk <> BCinvalid).
        { u in PUB. ii. rewrite H in *. ss. exploit Mem.perm_valid_block; eauto. i; des. des_ifs. }
        assert(BCV0: bc blk0 <> BCinvalid).
        {
          exploit mmatch_top; eauto.
          (* spcN 0%nat mmatch_top. spc mmatch_top. inv mmatch_top. *)
          intro SM. inv SM.
          specialize (H0 0%Z blk0 ofs0 true q n).
          exploit H0.
          { admit "ez - memory lemma". }
          intro PM.
          inv PM. ss.
        }
        esplits; eauto.
        { u. des_ifs. i; des_sumbool; ss. }
        s. eapply mmatch_below; eauto.
      + u. ii. des_ifs.
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. i; des.
        xomega.
    - econs; ss; i; des_ifs. inv GE. ss. des_sumbool. apply NNPP. ii.
      exploit (H0 x0); eauto. { xomega. } i; des. clarify.
  }
Qed.

(* copied from above *)
Lemma sound_state_sound_retv
      bc m_ret su0 p skenv_link v_ret cunit
      ge
      (GENV: ge = (SkEnv.revive (SkEnv.project skenv_link (defs p)) p))
      (STK: sound_stack cunit ge su0 bc [] m_ret (Mem.nextblock m_ret))
      (RES: vmatch bc v_ret Vtop)
      (RO: romatch bc m_ret (romem_for cunit))
      (MM: mmatch bc m_ret mtop)
      (GE: genv_match bc ge)
      (NOSTK: bc_nostack bc)
  :
    Sound.retv (bc2su bc ge.(Genv.genv_next) m_ret.(Mem.nextblock)) (Retv.mk v_ret m_ret)
.
Proof.
  { r. s. esplits; eauto.
    - ii; clarify.
      assert(BCV: bc blk <> BCinvalid).
      { inv RES; ss. inv H0; ss. }
      esplits; eauto.
      + u. ii. des_ifs. des_sumbool. ss.
      + inv MM. eapply mmatch_below; eauto.
    - inv MM. econs; eauto.
      + ii. clarify.
        assert(BCV: bc blk <> BCinvalid).
        { u in PUB. ii. rewrite H in *. ss. exploit Mem.perm_valid_block; eauto. i; des. des_ifs. }
        assert(BCV0: bc blk0 <> BCinvalid).
        {
          exploit mmatch_top; eauto.
          (* spcN 0%nat mmatch_top. spc mmatch_top. inv mmatch_top. *)
          intro SM. inv SM.
          specialize (H0 0%Z blk0 ofs0 true q n).
          exploit H0.
          { admit "ez - memory lemma". }
          intro PM.
          inv PM. ss.
        }
        esplits; eauto.
        { u. des_ifs. i; des_sumbool; ss. }
        s. eapply mmatch_below; eauto.
      + u. ii. des_ifs.
      + ss. r in GE. ss. des. r in mmatch_below.
        apply NNPP. ii. apply Pos.lt_nle in H.
        exploit GE0; eauto. i; des.
        exploit mmatch_below; eauto. i; des.
        xomega.
    - econs; eauto; ss; i; des_ifs. des_sumbool.
      rr in GE. des.
      apply NNPP. ii.
      exploit (GE0 x0); eauto.
      { unfold fundef in *. xomega. }
      i; des. ss.
  }
Qed.







Section PRSV.

  Variable skenv_link: SkEnv.t.
  Variable p: program.

  Hypothesis INCLUDE: include_defs
                        (fun fdef skdef => skdef_of_gdef fn_sig fdef = skdef)
                        p skenv_link.

  Let modsem := RTLC.modsem skenv_link p.

  Local Existing Instance Unreach.

  Theorem sound_state_preservation
    :
      local_preservation_strong modsem get_mem (sound_state p modsem.(globalenv))
  .
  Proof.
    econs; eauto.
    - i. inv INIT. ss.
      esplits; eauto; cycle 1.
      { refl. }
      econs; eauto. i.
      set (ge := (SkEnv.revive (SkEnv.project skenv_link (defs p)) p)) in *.
      set (f := fun b =>
                  if plt b (Genv.genv_next ge) then
                    match Genv.invert_symbol ge b with None => BCother | Some id => BCglob id end
                  else
                    if (plt b args.(Args.m).(Mem.nextblock)) && (negb (su_init b))
                    then BCother
                    else BCinvalid).
      (* set (f := fun b => *)
      (*             if (plt b args.(Args.m).(Mem.nextblock)) *)
      (*             then *)
      (*               match Genv.invert_symbol ge b with *)
      (*               | None => if su_init b then BCinvalid else BCother *)
      (*               | Some id => BCglob id *)
      (*               end *)
      (*             else *)
      (*               BCinvalid). *)
      assert(IMG: exists bc, bc.(bc_img) = f).
      { unshelve eexists (BC _ _ _); s; eauto.
        - ii. subst f. ss. des_ifs.
        - ii. subst f. ss. des_ifs. apply_all_once Genv.invert_find_symbol. clarify.
      }
      subst f. des.
      r in SUARG. des. ss. unfold Sound.vals in *. rewrite Forall_forall in *.
      assert(FP: forall blk, su_init blk -> Ple ge.(Genv.genv_next) blk).
      { inv SKENV. ss. i. inv MEM. rewrite <- PUB. apply NNPP. ii. inv WF. exploit WFHI; eauto. }
      assert(NB: Ple ge.(Genv.genv_next) args.(Args.m).(Mem.nextblock)).
      { inv SKENV. ss. }
      assert(GE: genv_match bc ge).
      { r.
        esplits; eauto.
        * ii. rewrite IMG in *. split; i.
          { exploit Genv.genv_symb_range; eauto. i.
            apply_all_once Genv.find_invert_symbol.
            unfold fundef in *.
            des_ifs.
          }
          des_ifs. apply Genv.invert_find_symbol; eauto.
        * rewrite IMG. ii.
          assert(Plt b (Mem.nextblock (Args.m args))).
          { eapply Plt_Ple_trans; eauto. }
          des_ifs.
      }
      eapply sound_call_state with (bc:= bc); eauto.
      + econs; eauto; cycle 1.
        { inv MEM; ss. rewrite NB0. xomega. }
        (* { inv SKENV. ss. } *)
        (* econs; eauto. *)
        (* * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss. *)
        (* * rewrite IMG. ii. des_ifs; ss; hexpl FP; try xomega. bsimpl. ss. *)
        (* * ii. inv MEM. eapply BOUND; eauto. *)
        (* * rewrite IMG. ii. des_ifs; ss. inv SKENV. rewrite PUB0 in *; ss. *)
        (* * inv SKENV. rewrite PUB in *. ss. *)
      + ii. repeat spc VALS. destruct v; econs; eauto. destruct b0; econs; eauto. rewrite IMG.
        inv TYP. ss.
        apply in_zip_iff in H0. des. unfold typify in *. des_ifs.
        hexploit1 VALS.
        { eapply nth_error_In; eauto. }
        repeat spc VALS. specialize (VALS eq_refl). (* TODO: fix spc ... *) des.
        des_ifs; ss. bsimpl. des; ss. des_sumbool. inv MEM. congruence.
      + ii. rewrite IMG in *. des_ifs.
        hexploit romem_for_consistent_2; eauto. intro ROM; des.
        exploit ROM; eauto. intro ROMEM; des.
        clarify.
        esplits; eauto.
        * eapply store_init_data_list_summary. ss. econs; eauto.
        *
          (* hexploit (@SkEnv.revive_precise _ _ (SkEnv.project skenv_link (defs p)) p); eauto. *)
          (* { intros jd IN. dup IN. rewrite prog_defmap_spec in IN. des. *)
          (*   hexploit (SkEnv.project_impl_spec skenv_link (defs p)). intro SPEC. *)
          (*   inv SPEC. *)
          (*   rewrite SYMBKEEP; ss. *)
          (*   { erewrite Genv.invert_find_symbol; ss. eauto. *)
          (*     apply Genv.find_def_symbol in IN. des. ss. *)
          (*     exploit Genv.invert_find_symbol; eauto. intro SYMB. *)
          (*     unfold ge in SYMB. unfold SkEnv.revive in SYMB. rewrite Genv_map_defs_symb in SYMB. *)
          (*     admit "idk". *)
          (*   } *)
          (*   { u. destruct (in_dec ident_eq jd (prog_defs_names p)) eqn:T; ss. } *)
          (* } *)
          (* { admit "ez". } *)
          (* intro PRC; des. *)

          (* inv PRC. *)
          (* exploit FIND_MAP; eauto. i; des. des_ifs. clear_tac. *)
          (* folder. *)

          assert(CONTAINS: forall
                    id
                    (IN: p.(defs) id)
                    gv
                    (DEF: (Sk.of_program fn_sig p).(prog_defmap) ! id = Some (Gvar gv))
                  ,
                    exists blk, <<SYMB: skenv_link.(Genv.find_symbol) id = Some blk>> /\
                                        <<DEF: skenv_link.(Genv.find_def) blk = Some (Gvar gv)>>).
          { i. exploit (INCLUDE id0); cycle 1; eauto.
            - i. des. esplits; eauto. instantiate (1:=Gvar gv) in MATCH.
              ss. clarify. ss. destruct gv. ss. destruct gvar_info. ss.
            - clear - DEF.
              exploit Sk.of_program_prog_defmap. i. inv H.
              + rewrite DEF in *. clarify.
              + rewrite DEF in *. clarify. inv H2. inv H3. ss.
                destruct i2, i1. ss.
          }

          exploit Genv.invert_find_symbol; eauto. intro SYMB. clarify.
          hexploit (Sk.of_program_prog_defmap p fn_sig id); eauto. intro REL.
          unfold fundef in *. inv REL.
          {  rewrite ROMEM in *. clarify. }
          symmetry in H0. clarify. symmetry in H2. inv H3. inv H5. ss. clear_tac.
          exploit (CONTAINS id); eauto.
          { u.
            des_sumbool.
            eapply prog_defmap_spec; eauto.
          }
          i; des.

          inv SKENV.
          set (gv := {| gvar_info := i2; gvar_init := init; gvar_readonly := true; gvar_volatile := false |}).
          exploit (RO b gv); eauto; ss.
          { unfold Genv.find_var_info.
            admit "ez".
          }
          i; des.

          r. esplits; eauto.
          { admit "this should hold". }
          { admit "this should hold". }
        * inv SKENV.
          exploit RO; eauto.
          { admit "copy from above". }
          { rewrite ROMEM1. ss. }
          i; des.
          ii. exploit PERM; eauto. i; des. inv ORD.
      + assert(BCSU: forall b, bc b <> BCinvalid -> ~ su_init b).
        { intros ? BC. rewrite IMG in BC.
          destruct (plt b (Genv.genv_next skenv_link)).
          - inv SKENV. ss. inv WF. ii. hexploit WFLO; eauto. i. Unreach.nb_tac. xomega.
          - des_ifs. bsimpl. des. ii. congruence.
        }
        assert(SUBC: forall b (VALID: Plt b (Mem.nextblock (Args.m args))), ~ su_init b -> bc b <> BCinvalid).
        { intros ? ? SU. rewrite IMG. des_ifs. bsimpl. des; ss. des_sumbool.
          inv SKENV. ss.
        }
        assert(SUMEM: forall b : block, bc b <> BCinvalid -> smatch bc (Args.m args) b Ptop).
        { i. rr. rename H0 into SU.
          hexploit BCSU; eauto. intro SU0.
          split; i.
          - hexploit mem'_load_val'; eauto. intro SUV.
            { destruct v; econs; et. destruct b1; econs; et. exploit SUV; et. i; des. ii.
              exploit BCSU; et.
              exploit SUBC; try apply H1; et.
              { inv MEM. Unreach.nb_tac. ss. }
              ss.
            }
          - hexploit mem'_loadbytes_val'; eauto. intro SUV.
            { destruct isreal'; econs; et. exploit SUV; et. i; des. ii.
              exploit BCSU; et.
              exploit SUBC; try apply H1; et.
              { inv MEM. Unreach.nb_tac. ss. }
              ss.
            }
        }
        econs; s; eauto.
        * rewrite IMG. ii. des_ifs; ss.
        * rewrite IMG. ii. des_ifs; ss. rewrite PTree.gempty in *. ss.
        * intros ? A. rewrite IMG in A. inv SKENV. ss. des_ifs; try xomega. bsimpl. des. des_sumbool. xomega.
      + r. rewrite IMG. i. des_ifs.
      + rr. ss. inv MEM. inv SKENV. ss. rewrite NB0. esplits; eauto.
        * i. des_ifs; try xomega. rewrite IMG. rewrite <- PUB. inv WF.
          destruct (su_init blk) eqn:T; des_sumbool.
          { hexploit WFLO; eauto. i. des_ifs; try xomega. bsimpl. ss. }
          des_ifs. bsimpl. exfalso. des_sumbool. xomega.
        * refl.
    - ii; ss. eapply sound_step; eauto.
    - i; ss. inv SUST.
      assert(GR: exists su_gr, SemiLattice.greatest le'
                                                    (* (fun su => su0.(UnreachC.ge_nb) = su.(UnreachC.ge_nb) /\ args' su args) *)
                                                    (fun su =>  le' su0 su /\ args' su args)
                                                    su_gr).
      { specialize (H p (linkorder_refl _)).
        set (args0 := args).
        inv AT. inv H; ss.
        exploit sound_state_sound_args; eauto. i.
        hexploit (@Sound.greatest_ex _ (bc2su bc (Genv.genv_next skenv_link) (Mem.nextblock m0)) args0); eauto.
        { esplits; eauto. ss. refl. }
        i; des. ss.
        esplits; eauto.

        (* eapply SemiLattice.greatest_le_irr with (lub := UnreachC.lub); eauto. *)
        (* - typeclasses eauto. *)
        (* - ii. eapply lubsucc; eauto. *)
        (* - ii. eapply lubspec; eauto. *)
        (* - ii. eapply lubclosed; try apply LUB; eauto. *)
        (* - exploit sound_stack_unreach_compat; eauto. i; des. ss. *)
        (*   r; u; ss. esplits; eauto. i. inv SU. exploit BOUND; eauto. i; des. des_ifs. rewrite PRIV; ss. *)
        exploit Sound.get_greatest_le; ss; eauto.
        - change le' with Sound.le. eapply Sound.hle_le; et.
      }
      des.
      esplits; eauto.
      { inv AT; ss. refl. }
      ii.
      r in RETV. des.
      esplits; eauto; cycle 1.
      { inv AT; inv AFTER; ss. refl. }
      + econs; eauto. intros cunit LO. specialize (H cunit LO). inv AFTER; ss. inv H; ss.
        assert(BCARGS: (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)).(Sound.args) args).
        { ss. inv AT; ss. r. s. rpapply sound_state_sound_args; eauto. }
        assert(BCLE0: Sound.le su0 (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock))).
        { change le' with Sound.le. eapply Sound.hle_le; et. }
        assert(BCLE1: Sound.le (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) su_gr).
        { eapply GR; eauto. }
        (* set (f := fun b => if plt b retv.(Retv.m).(Mem.nextblock) *)
        (*                    then *)
        (*                      if su_ret b *)
        (*                      then BCinvalid *)
        (*                      else BCother *)
        (*                    else *)
        (*                      BCinvalid *)
        (*     ). *)
        (* set (f := fun b => if plt b (Mem.nextblock m_arg) *)
        (*                    then bc b *)
        (*                    else *)
        (*                      if su_ret b *)
        (*                      then BCinvalid *)
        (*                      else BCother). *)
        (* set (f := fun b => if plt b (Mem.nextblock m_arg) *)
        (*                    then bc b *)
        (*                    else *)
        (*                      if plt b (Mem.nextblock retv.(Retv.m)) *)
        (*                      then *)
        (*                        if su_ret b *)
        (*                        then BCinvalid *)
        (*                        else BCother *)
        (*                      else BCinvalid). *)
        set (f := fun b => if plt b (Mem.nextblock m_arg)
                           then bc b
                           else
                             if plt b (Mem.nextblock retv.(Retv.m))
                             then
                               if su_ret b
                               then BCinvalid
                               else BCother
                             else BCinvalid).
        assert(exists bc', <<IMG: bc'.(bc_img) = f>>).
        { unshelve eexists (BC _ _ _); ss.
          - ii. subst f. ss. des_ifs. eapply bc_stack; eauto.
          - ii. subst f. ss. des_ifs. eapply bc_glob; eauto.
        } des.

        assert(HLEAFTER: Unreach.hle (bc2su bc (Genv.genv_next skenv_link) (Mem.nextblock m_arg))
                                     (bc2su bc' (Genv.genv_next skenv_link) (Mem.nextblock (Retv.m retv)))).
        { rr. ss. rewrite IMG. unfold f.
          assert(NB: Ple (Mem.nextblock m_arg) (Mem.nextblock (Retv.m retv))).
          { inv AT; ss. inv MLE. inv RO0. ss. }
          esplits; ss.
          - i. des_ifs. xomega.
        }

        assert(GRARGS: Sound.args su_gr args).
        { rr in GR. des. ss. }
        exploit Unreach.hle_hle_old; try apply LE; eauto.
        { rr in GRARGS. des. ss. }
        intro LEOLD.
        assert (VMTOP0: forall v, Sound.val su_gr v -> vmatch bc' v Vtop).
        { i.
          (* assert(Sound.val su_ret v). *)
          (* { eapply Sound.hle_val; et. } *)
          ss. r in H. destruct v; econs; eauto. destruct b0; econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs_safe.
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) b).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. inv MEM.
          rr in GRARGS. des. inv MEM. ss.
          inv AT; ss. rewrite NB0 in *. des_ifs; try xomega.
          intro BC. unfold bc2su in *. ss. rewrite BC in *. ss.
        }
        assert (VMTOP: forall v, val' su_ret v -> vmatch bc' v Vtop).
        { i. r in H. destruct v; econs; eauto. destruct b0; econs; eauto.
          exploit H; eauto. i; des. rewrite IMG. subst f. s. des_ifs_safe.
          assert(NSU: ~su_gr b).
          { ii. r in LEOLD. des. exploit PRIV; eauto. i; ss. congruence. }
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) b).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. inv MEM. rewrite NB in *. des_ifs.
          clear - NBC p0.
          ii. unfold bc2su in *. ss. rewrite H in *. ss.
        }
        assert (VMTOP1: forall v (BELOW: bc_below bc (Mem.nextblock m_arg)),
                   vmatch bc v Vtop -> vmatch bc' v Vtop).
        { i. inv H; econs; eauto. inv H2; econs; eauto.
          exploit BELOW; eauto. i.
          rewrite IMG. unfold f.
          des_ifs.
        }
        assert (PMTOP: forall blk ofs isreal, ~ su_ret blk -> Plt blk (Mem.nextblock (Retv.m retv)) -> pmatch bc' blk ofs isreal Ptop).
        { i. r in H. destruct isreal; econs; eauto.
          assert(NSU: ~su_gr blk).
          { ii. r in LEOLD. des. exploit PRIV; eauto. }
          assert(NBC: ~ (bc2su bc (Genv.genv_next skenv_link) m_arg.(Mem.nextblock)) blk).
          { ii. ss. r in BCLE1. des. exploit PRIV; eauto. des_ifs. }
          ss. rewrite IMG. unfold f. des_ifs.
          ii. rewrite H1 in *. ss.
        }
        assert (PMTOP1: forall blk ofs isreal
                               (BELOW: bc_below bc (Mem.nextblock m_arg))
                 ,
                   pmatch bc blk ofs isreal Ptop -> pmatch bc' blk ofs isreal Ptop).
        { i. inv H; econs; eauto.
          exploit BELOW; eauto. i.
          ss. rewrite IMG. unfold f. des_ifs.
        }
        assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' retv.(Retv.m) b Ptop).
        {
          intros; split; intros.
          -
            destruct (su_gr b) eqn:T.
            + assert(Plt b (Mem.nextblock m_arg)).
              {
                rr in GRARGS. des. inv MEM0. inv AT; ss.
                inv WF1. exploit WFHI; eauto. i.
                Unreach.nb_tac. ss.
              }
              rewrite IMG in *. subst f. ss. des_ifs.

              inv MM. exploit mmatch_top; eauto. intro SM. rr in SM. des.
              assert(LD: Mem.load chunk m_arg b ofs = Some v).
              { inv MLE. inv AT. ss. erewrite <- Mem.load_unchanged_on_1; try apply PRIV; eauto. }
              exploit SM; eauto.
            + assert(~ su_ret b).
              {
                rewrite IMG in *. subst f. ss. des_ifs.
                rr in LE. des. ss. erewrite <- OLD; eauto.
                { congruence. }
                rr in GRARGS. des. inv MEM0. inv AT; ss. Unreach.nb_tac. ss.
              }
              eapply VMTOP; eauto. eapply mem'_load_val'; eauto.
          -
            destruct (su_gr b) eqn:T.
            + assert(Plt b (Mem.nextblock m_arg)).
              {
                rr in GRARGS. des. inv MEM0. inv AT; ss.
                inv WF1. exploit WFHI; eauto. i.
                Unreach.nb_tac. ss.
              }
              rewrite IMG in *. subst f. ss. des_ifs.

              inv MM. exploit mmatch_top; eauto. intro SM. rr in SM. des.
              assert(LD: Mem.loadbytes m_arg b ofs 1 = Some [Fragment (Vptr b' ofs' isreal') q i]).
              { inv MLE. inv AT. ss. erewrite <- Mem.loadbytes_unchanged_on_1; try apply PRIV; eauto. }
              exploit SM0; eauto.
            + destruct isreal'; try (by econs; eauto).
              assert(~ su_ret b).
              {
                rewrite IMG in *. subst f. ss. des_ifs.
                rr in LE. des. ss. erewrite <- OLD; eauto.
                { congruence. }
                rr in GRARGS. des. inv MEM0. inv AT; ss. Unreach.nb_tac. ss.
              }
              eapply PMTOP; eauto; cycle 1.
              { inv MEM.
                Local Transparent Mem.loadbytes.
                unfold Mem.loadbytes in *. des_ifs.
                exploit (SOUND b ofs); eauto.
                { eapply r. xomega. }
                i; des. ss.
                Unreach.nb_tac. xomega.
              }
              eapply mem'_loadbytes_val'; eauto.
        }

        eapply sound_return_state with (bc := bc'); eauto.
        *
          apply sound_stack_new_bound with (Mem.nextblock m_arg); cycle 1.
          { admit "ez". }
          apply sound_stack_exten with bc; auto; cycle 1.
          { i. rewrite IMG. unfold f. des_ifs. }
          apply sound_stack_inv with m_arg; auto.
          i. inv MLE.
          inv AT. ss.
          eapply Mem.loadbytes_unchanged_on_1; try apply PRIV; eauto.
          u. i.
          eapply BCLE1; et. ss. des_ifs. des_sumbool. ss.
        * eapply VMTOP; et. unfold typify. des_ifs.
        * admit "ez - RO".
        *

          {
            constructor; simpl; intros.
            + apply ablock_init_sound. apply SMTOP. simpl; congruence.
            + rewrite PTree.gempty in H0; discriminate.
            + apply SMTOP; auto.
            + apply SMTOP; auto.
            + red; simpl; intros. destruct (plt b (Mem.nextblock m_arg)).
              * eapply Pos.lt_le_trans. eauto. { inv AT. apply MLE. }
              * rewrite IMG in *. subst f. ss. des_ifs.
          }
        * admit "ez".
        * red; simpl; intros. rewrite IMG. unfold f. des_ifs.
          eapply NOSTK; auto.
        * ss. etrans; eauto.
    - ii.
      inv FINAL. s.
      inv SUST. specialize (H p (linkorder_refl _)). inv H.
      exists (bc2su bc (Genv.genv_next skenv_link) m_ret.(Mem.nextblock)).
      esplits; try refl; ss; eauto.
      rp; [eapply sound_state_sound_retv; eauto|..]; eauto.
  Qed.

End PRSV.
