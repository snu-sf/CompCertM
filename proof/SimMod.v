Require Import Events.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import ModSem.
Require Import Integers.
Require Import ASTC.
Require Import Maps.
Require Import LinkingC.

Require Import Syntax Sem Mod ModSem.
Require Import Sound.
Require Import SimSymb SimMem SimModSem.

Set Implicit Arguments.







Module ModPair.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    SM:> SimMem.class;
    SS:> SimSymb.class SM;
    ss: SimSymb.t;
    wf:= SimSymb.sim_sk ss src.(Mod.sk) tgt.(Mod.sk)
  }
  .

  Reset t. (* Need to state SS = SS in SimMem... JMEQ THINGS !!!!!!!!!!!!! *)

Section MODPAIR.
Context `{SM: SimMem.class} {SS: SimSymb.class SM} {SU: Sound.class}.

  Record t: Type := mk {
    src: Mod.t;
    tgt: Mod.t;
    ss: SimSymb.t;
  }
  .

  Definition to_msp (skenv_link_src skenv_link_tgt: SkEnv.t) (sm: SimMem.t) (mp: t): ModSemPair.t :=
    ModSemPair.mk (Mod.modsem (mp.(src)) skenv_link_src) (Mod.modsem (mp.(tgt)) skenv_link_tgt) mp.(ss) sm
  .

  (* TODO: Actually, ModPair can have idx/ord and transfer it to ModSemPair. *)
  (* Advantage: We can unify ord at Mod state. *)
  Inductive sim (mp: t): Prop :=
  | sim_intro
      (SIMSK: SimSymb.sim_sk mp.(ss) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk))
      (* (SIMMS: forall *)
      (*     skenv_src skenv_tgt *)
      (*   , *)
      (*     exists msp, *)
      (*       (* TODO: get_modsem always suceeds??? I think not. *) *)
      (*       <<SRC: msp.(ModSemPair.src) = (mp.(src).(Mod.get_modsem) skenv_src mp.(src).(Mod.data))>> *)
      (*       /\ <<TGT: msp.(ModSemPair.tgt) = (mp.(tgt).(Mod.get_modsem) skenv_tgt mp.(tgt).(Mod.data))>> *)
      (*       /\ <<SS: msp.(ModSemPair.ss) = mp.(ss)>> *)
      (*       /\ <<SIM: ModSemPair.sim msp>> *)
      (* ) *)
      (SIMMS: forall
          skenv_link_src skenv_link_tgt
          ss_link
          (SSLE: SimSymb.le mp.(ss) mp.(src) mp.(tgt) ss_link)
          sm_init_link
          (SIMSKENVLINK: SimSymb.sim_skenv sm_init_link ss_link skenv_link_src skenv_link_tgt)
        ,
          <<SIMMSP: ModSemPair.sim mp.(to_msp skenv_link_src skenv_link_tgt sm_init_link)>>)
  .

  (* Design: ModPair only has data, properties are stated in sim *)

End MODPAIR.
End ModPair.

Hint Unfold ModPair.to_msp.

(* Module ModPair. *)

(*   Record t: Type := { *)
(*     src: Mod.t; *)
(*     tgt: Mod.t; *)
(*     si: symbinj; *)
(*     (* TODO: unify closed & private *) *)
(*     closed: symbinj_closed si src tgt; *)
(*     private: symbinj_private si src tgt; *)
(*     (* TODO: which unary/binary property it expects *) *)
(*     (* TODO: analysis *) *)
(*   } *)
(*   . *)

(*   (* Change sim_modsem to be sensitive to si. *) *)
(*   (* Only when initial memory is respecting si, it can guarantee something. *) *)
(*   (* Q: Can we encode it inside SM? *) *)

(* End ModPair. *)




(* Section SIM. *)

(*   Context `{SS: SimSymb.class} `{SM: @SimMem.class SS}. *)

(*   Lemma sim_load_mod *)
(*         mp0 mp1 *)
(*         (SIM0: ModPair.sim mp0) *)
(*         (SIM1: ModPair.sim mp1) *)
(*         sk_src *)
(*         (LINKSRC: link mp0.(ModPair.src).(Mod.sk) mp1.(ModPair.src).(Mod.sk) = Some sk_src) *)
(*     : *)
(*       exists sk_tgt, *)
(*         <<LINKTGT: link mp0.(ModPair.tgt).(Mod.sk) mp1.(ModPair.tgt).(Mod.sk) = Some sk_tgt>> *)
(*   . *)
(*   Proof. *)
(*     inv SIM0. inv SIM1. *)
(*     exploit SimSymb.sim_sk_weak_enables_link; eauto. *)
(*     { eapply SimSymb.sim_sk_sim_sk_weak; eauto. } *)
(*     { eapply SimSymb.sim_sk_sim_sk_weak; eauto. } *)
(*   Qed. *)

(* End SIM. *)





(* Inductive sim_sk (si: symbinj) (sk_src sk_tgt: Sk.t): Prop := *)
(* | sim_sk_intro *)
(*     (CLOSED: symbinj_closed si sk_src sk_tgt) *)
(*     (PRIVATE: symbinj_private si sk_src sk_tgt) *)
(* . *)


(*   Inductive sim_modpair (mp: ModPair.t): Prop := *)
(* | sim_intro *)
(*     (SIMSK: sim_sk mp.(si) mp.(src).(Mod.sk) mp.(tgt).(Mod.sk)) *)
(*     (WF: True) (* si is well-formed according to src/tgt. So that it can link with others *) *)
(*     (SIMMS: forall *)
(*         skenv_src skenv_tgt *)
(*         (SIMSKENV: respects mp.(si) skenv_src skenv_tgt) *)
(*       , *)
(*         sim_modsem (mp.(si)) *)
(*                    (mp.(src).(Mod.get_modsem) skenv_src mp.(src).(Mod.data)) *)
(*                    (mp.(tgt).(Mod.get_modsem) skenv_tgt mp.(tgt).(Mod.data))) *)
(* . *)

 