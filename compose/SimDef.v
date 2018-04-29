Require Import Events.
Require Import Values.
Require Import AST.
Require Import Asmregs.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import CoqlibC.
Require Import Skeleton.
Require Import Integers.
Require Import ASTC.
Require Import LinkingC.
Require Import Maps.


Set Implicit Arguments.


Inductive sim_sig (sg_src sg_tgt: option signature): Prop :=
| sim_sig_keep
    sg
    (SRC: sg_src = Some sg)
    (TGT: sg_tgt = Some sg)
| sim_sig_drop
    (TGT: sg_tgt = None)
.

Inductive sim_fun: (fundef (option signature)) -> (fundef (option signature)) -> Prop :=
| sim_fdef_internal
    sg_src sg_tgt
    (SIM: sim_sig sg_src sg_tgt)
  :
    sim_fun (Internal sg_src) (Internal sg_tgt)
| sim_fdef_external
    ef
  :
    sim_fun (External ef) (External ef)
.

(* Inductive sim_var: (globvar unit) -> (globvar unit) -> Prop := *)
(* | sim_var_intro *)
(*     gv *)
(*   : *)
(*     sim_var gv gv *)
(* . *)

Inductive sim_def: (globdef (fundef (option signature)) unit) ->
                    (globdef (fundef (option signature)) unit) -> Prop :=
| sim_gfun
    f_src f_tgt
    (SIM: sim_fun f_src f_tgt)
  :
    sim_def (Gfun f_src) (Gfun f_tgt)
| sim_gvar
    (* gv_src gv_tgt *)
    (* (SIM: sim_var gv_src gv_tgt) *)
    gv
  :
    sim_def (Gvar gv) (Gvar gv)
.

(* TODO: there should be a general function that lifts rel to option rel *)
Inductive sim_odef: option (globdef (fundef (option signature)) unit) ->
                    option (globdef (fundef (option signature)) unit) -> Prop :=
| sim_odef_some
    def_src def_tgt
    (SIM: sim_def def_src def_tgt)
  :
    sim_odef (Some def_src) (Some def_tgt)
| sim_odef_none
  :
    sim_odef None None
.

Lemma sim_def_preserves_link
      (def_src0 def_src1 def_src: globdef (fundef (option signature)) unit)
      (LINKSRC: link def_src0 def_src1 = Some def_src)
      def_tgt0 def_tgt1
      (SIM0: sim_def def_src0 def_tgt0)
      (SIM1: sim_def def_src1 def_tgt1)
  :
    exists def_tgt, <<LINK: link def_tgt0 def_tgt1 = Some def_tgt>> /\ <<SIM: sim_def def_src def_tgt>>
.
Proof.
  Local Transparent Linker_def.
  Local Transparent Linker_fundef.
  ss.
  unfold link_def in *.
  inv SIM0; inv SIM1; ss; des_ifs_safe.
  - inv SIM; inv SIM0; ss; des_ifs_safe; esplits; eauto; repeat (econs; eauto).
  - esplits; eauto. econs; eauto.
  Local Opaque Linker_def.
  Local Opaque Linker_fundef.
Qed.


