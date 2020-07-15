Require Import CoqlibC Maps Postorder.
Require Import AST Linking.
Require Import ValuesC MemoryC GlobalenvsC Events Smallstep.
Require Import Op ClightC.
Require Import CtypesC CtypingC.
Require Import sflib.
Require Import IntegersC.

Require Import Simulation.
Require Import Skeleton Mod ModSem SimMod SimModSemLift SimSymb SimMemLift MatchSimModSemExcl.
Require SoundTop.
Require SimMemId.
Require Import Any.
Require Import SIR.
Require Import FibHeader.
Require Import Fib6.
Require Import Fib5_old.
Require Import ModSemProps.
Require Import Program.
Require Import SIRProps.

Set Implicit Arguments.






Ltac step := gstep; econs; et.
Ltac step_assume := match goal with
                    | |- context[assume ?P ;; _] =>
                      (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                      first[
                          unfold assume at 5|
                          unfold assume at 4|
                          unfold assume at 3|
                          unfold assume at 2|
                          unfold assume at 1|
                          unfold assume at 0
                        ];
                      let name := fresh "T" in
                      destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
                        unfold triggerUB; rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
                        try step|]
                    end
.
Ltac step_unwrapN := match goal with
                     | |- context[unwrapN ?ox ;; _] =>
                       (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                       first[
                           unfold unwrapN at 5|
                           unfold unwrapN at 4|
                           unfold unwrapN at 3|
                           unfold unwrapN at 2|
                           unfold unwrapN at 1|
                           unfold unwrapN at 0
                         ];
                       let name := fresh "T" in
                       destruct ox eqn:name; cycle 1
                     end
.
Ltac step_guaranteeK := match goal with
                        | |- context[guaranteeK ?P ;; _] =>
                          (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                          first[
                              unfold guaranteeK at 5|
                              unfold guaranteeK at 4|
                              unfold guaranteeK at 3|
                              unfold guaranteeK at 2|
                              unfold guaranteeK at 1|
                              unfold guaranteeK at 0
                            ];
                          destruct (ClassicalDescription.excluded_middle_informative P); cycle 1
                        | |- context[guaranteeK ?P ?Q] =>
                          (*** I want to unfold only the "first" assume.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                          first[
                              unfold guaranteeK at 5|
                              unfold guaranteeK at 4|
                              unfold guaranteeK at 3|
                              unfold guaranteeK at 2|
                              unfold guaranteeK at 1|
                              unfold guaranteeK at 0
                            ];
                          destruct (ClassicalDescription.excluded_middle_informative (P Q)); cycle 1
                        end
.
Ltac step_guarantee := match goal with
                    | |- context[guarantee ?P ;; _] =>
                      (*** I want to unfold only the "first" guarantee.
Maybe we should use notation instead, so that we can avoid this weird "unfold"? ***)
                      first[
                          unfold guarantee at 5|
                          unfold guarantee at 4|
                          unfold guarantee at 3|
                          unfold guarantee at 2|
                          unfold guarantee at 1|
                          unfold guarantee at 0
                        ];
                      let name := fresh "T" in
                      destruct (ClassicalDescription.excluded_middle_informative P) as [name|name]; cycle 1; [
                        unfold triggerNB; rewrite bind_vis (*** <---------- this is counter-intuitive. Any good idea? ***);
                        try step|]
                    end
.



(*** TODO: update Ord.v ***)
Section WFMAP.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Variable idx_map: Type.
  Variable f: idx_map -> idx.
  Definition ord_map (b0 b1: idx_map): Prop := ord (f b0) (f b1).

  Theorem wf_map: well_founded ord_map.
  Proof.
    ii. rename a into b.
    remember (f b) as a. generalize dependent b.
    pattern a. eapply well_founded_ind; et. clear a; i.
    clarify. econs; et.
  Qed.

End WFMAP.

Section WFOPTION.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Let idx_option: Type := option idx.
  Inductive ord_option: idx_option -> idx_option -> Prop :=
  | ord_option_some
      i0 i1
      (ORD: ord i0 i1)
    :
      ord_option (Some i0) (Some i1)
  .

  Theorem wf_option: well_founded ord_option.
  Proof.
    ii.
    induction a; ii; ss.
    { pattern a. eapply well_founded_ind; et. clear a; i.
      econs; et. ii. inv H0. eapply H; et. }
    { econs. ii. inv H. }
  Qed.

End WFOPTION.

Section WFPMAP.

  Variable idx: Type.
  Variable ord: idx -> idx -> Prop.
  Hypothesis WF: well_founded ord.

  Variable idx_pmap: Type.
  Variable f: idx_pmap -> option idx.
  Definition ord_pmap (b0 b1: idx_pmap): Prop := (ord_map (ord_option ord) f) b0 b1.

  Theorem wf_pmap: well_founded ord_pmap.
  Proof.
    eapply wf_map. eapply wf_option. assumption.
  Qed.

End WFPMAP.





Definition mp: ModPair.t := SimSymbId.mk_mp (Fib6.module) (Fib5_old.module).

Require Import SIRBCE. (*** TODO: export in SIRProps ***)
Local Opaque ident_eq.

(*** TODO: use prop instead of option ***)
Let idx := option (nat * nat).
Definition manifesto (fname: ident): option (owned_heap -> mem -> list val -> idx) :=
  if ident_eq fname _fib_ru
  then Some (fun oh m vs => option_map (fun n => (n, 1%nat)) (parse_arg oh m vs))
  else None
.

Theorem correct: rusc defaultR [Fib6.module: Mod.t] [Fib5_old.module: Mod.t].
Proof.
  etrans.
  { mimic. eapply SIREutt.correct; ss.
    prog_tac.
    unfold Fib6.f_fib. setoid_rewrite <- tau_eutt at 2. refl.
  }
  eapply SIRBCE.correct with (manifesto:=manifesto); et.
  { eapply wf_option. eapply ord_lex_wf; eapply lt_wf. }
  econs; et; cycle 1.
  { prog_tac.
    - unfold Fib6.f_fib, f_fib. irw.
      step_assume. Undo 1.
      unfold assume. des_ifs; irw; cycle 1.
      { unfold triggerUB. irw. pfold. econs; et. }
      pfold. rewrite <- ! bind_trigger. eapply match_icall_pure; et.
      left. pfold. irw. econs; et. ii; ss. clarify.
      left. pfold. irw. econs; et.
  }
  { ii. unfold manifesto in PURE. des_ifs.
    esplits; et.
    { unfold prog. ss. }
    ii. unfold f_fib_ru.
    pfold. unfold unwrapN. des_ifs; irw; cycle 1.
    { unfold triggerNB. irw. econs; et. }
    des_ifs; try econs; et. irw.
    step_guarantee.
    { econs; et. }
    irw.
    econs; ss; et; cycle 1.
    { cbn. rewrite range_to_nat; cycle 1.
      { u in T. des_ifs. }
      cbn. econs; et. econs; et.
    }
    ii. esplits; et.
    { econs; et. econs 2; et. }
    left. pfold. des_ifs. irw.
    step_guarantee.
    { econs; et. }
    irw.
    econs; ss; et; cycle 1.
    { cbn. rewrite range_to_nat; cycle 1.
      { u in T0. des_ifs. }
      econs; et. econs; et.
    }
    ii. esplits; et.
    { econs; et. econs; et. }
    left. pfold. des_ifs. econs; et.
  }
Unshelve.
  all: ss.
  all: try (by sk_incl_tac).
Qed.
