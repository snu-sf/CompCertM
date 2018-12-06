Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Asm.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib AsmC Sem Syntax LinkingC Program SemProps.
Require Import GlobalenvsC MemoryC2 Lia LinkingC2.

Set Implicit Arguments.

Local Opaque Z.mul.


Definition extcall_args_reg (mr: mreg) (sg: signature):
  {In (R mr) (regs_of_rpairs (loc_arguments sg))} +
  {~ In (R mr) (regs_of_rpairs (loc_arguments sg))}.
Proof.
  generalize (regs_of_rpairs (loc_arguments sg)). induction l.
  - ss. tauto.
  - ss. inv IHl; [tauto|].
    destruct a.
    + destruct (mreg_eq r mr); [clarify; eauto|].
      right. intros []; clarify.
    + right. intros []; clarify.
Qed.

Definition src_init_rs sg (rs_src: regset) (rsp: val) : regset :=
  fun (pr : PregEq.t) =>
    match Asm.to_mreg pr with
    | Some mr =>
      if (extcall_args_reg mr sg)
      then (rs_src pr)
      else (to_fake (rs_src pr))
    | None =>
      match pr with
      | IR RSP => rsp
      | PC => rs_src PC
      | RA => to_fake (rs_src RA)
      | _ => to_fake (rs_src pr)
      end
    end.

Program Definition arg_copy_mem (m: mem) (blk_old blk_new: Values.block)
        (sg: signature) (args: list val) : mem :=
  Mem.mkmem
    (admit "")
    m.(Mem.mem_access) m.(Mem.nextblock)
                           m.(Mem.access_max) m.(Mem.nextblock_noaccess)
                                                  _.
Next Obligation.
Admitted.

Definition arg_copy_reg (sg: signature) (args: list val)
           (rs: regset) : regset.
Admitted.

Lemma arg_copy_reg_spec sg args rs pr
      (DIFF: (arg_copy_reg sg args rs) pr <> rs pr)
  :
    (<<UNDEF: (arg_copy_reg sg args rs) pr = Vundef>>) /\
    (<<ARGS: exists mr (MR: to_mreg pr = Some mr),
        In (R mr) (regs_of_rpairs (loc_arguments sg))>>).
Admitted.

Lemma arg_copy_reg_RA sg args rs
  :
    (arg_copy_reg sg args rs) RA = rs RA.
Proof.
  destruct (classic (arg_copy_reg sg args rs RA = rs RA)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_PC sg args rs
  :
    (arg_copy_reg sg args rs) PC = rs PC.
Proof.
  destruct (classic (arg_copy_reg sg args rs PC = rs PC)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_RSP sg args rs
  :
    (arg_copy_reg sg args rs) RSP = rs RSP.
Proof.
  destruct (classic (arg_copy_reg sg args rs RSP = rs RSP)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  clarify.
Qed.

Lemma arg_copy_reg_more_undef sg args rs pr
  :
    (arg_copy_reg sg args rs) pr = rs pr \/
    (arg_copy_reg sg args rs) pr = Vundef.
Proof.
  destruct (classic (arg_copy_reg sg args rs pr = rs pr)); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  eauto.
Qed.

Lemma arg_copy_reg_callee_save sg args rs mr
      (SAVE: is_callee_save mr)
  :
    (arg_copy_reg sg args rs) (to_preg mr) = rs (to_preg mr).
Proof.
  destruct (classic (arg_copy_reg sg args rs (to_preg mr) = rs (to_preg mr))); eauto.
  exploit arg_copy_reg_spec; eauto. i. des.
  rewrite to_preg_to_mreg in MR. clarify.
  exploit AsmExtra.extcall_args_callee_save_disjoint; eauto.
  intros [].
Qed.

Lemma memcpy_store_arguments
      rs m_src0 m_src1 m_src2 sg args blk_old blk_new ofs
      (ARGS: Asm.extcall_arguments rs m_src0 sg args)
      (RSRSP: rs # RSP = Vptr blk_old ofs true)
      (OFSZERO: ofs = Ptrofs.zero)
      (NEQ: blk_old <> blk_new)
      (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (FREE: freed_from m_src0 m_src1
                        blk_old ofs.(Ptrofs.unsigned)
                                      (ofs.(Ptrofs.unsigned)+4*size_arguments sg))
      (ALLOC: Mem.alloc m_src1 ofs.(Ptrofs.unsigned)
                                     (ofs.(Ptrofs.unsigned)+4*size_arguments sg)
              = (m_src2, blk_new))
  :
    store_arguments
      m_src1
      (arg_copy_reg sg args (src_init_rs sg rs (Vptr blk_new ofs true)))
      (typify_list args (sig_args sg))
      sg (arg_copy_mem m_src2 blk_old blk_new sg args).
Proof.
Admitted.

Lemma arg_copy_mem_extends m blk_old blk_new sg args
  :
    Mem.extends (arg_copy_mem m blk_old blk_new sg args) (memcpy m blk_old blk_new).
Proof.
Admitted.


(* Lemma memcpy_store_arguments *)
(*       rs m_src0 m_src1 m_src2 sg args blk_old blk_new ofs *)
(*       (ARGS: Asm.extcall_arguments rs m_src0 sg args) *)
(*       (RSRSP: rs # RSP = Vptr blk_old ofs true) *)
(*       (OFSZERO: ofs = Ptrofs.zero) *)
(*       (NEQ: blk_old <> blk_new) *)
(*       (SZ: 4 * size_arguments sg <= Ptrofs.max_unsigned) *)
(*       (FREE: freed_from m_src0 m_src1 *)
(*                         blk_old ofs.(Ptrofs.unsigned) *)
(*                                       (ofs.(Ptrofs.unsigned)+4*size_arguments sg)) *)
(*       (ALLOC: Mem.alloc m_src1 ofs.(Ptrofs.unsigned) *)
(*                                      (ofs.(Ptrofs.unsigned)+4*size_arguments sg) *)
(*               = (m_src2, blk_new)) *)
(*   : *)
(*     store_arguments *)
(*       m_src1 *)
(*       (src_init_rs sg rs (Vptr blk_new ofs true)) *)
(*       args sg (memcpy m_src2 blk_old blk_new). *)
(* Proof. *)
(*   admit "it doesn't hold.". *)
(* Qed. *)

(*   clarify; econs; eauto. *)
(*   - unfold extcall_arguments in *. *)
(*     revert args ARGS. generalize (is_tail_refl (loc_arguments sg)). *)
(*     assert (forall *)
(*                l args *)
(*                (TAIL: is_tail l (loc_arguments sg)) *)
(*                (ARGS: list_forall2 (extcall_arg_pair rs m_src0) l args) *)
(*              , *)
(*                list_forall2 *)
(*                  (extcall_arg_pair (src_init_rs sg rs (Vptr blk_new Ptrofs.zero true)) *)
(*                                    (memcpy m_src2 blk_old blk_new)) l args); auto. *)
(*     induction l; i; inv ARGS; econs; eauto. *)
(*     + inv H1; econs. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := One l0) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. auto. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. tauto. *)
(*       * eapply init_argument; eauto. *)
(*         apply tail_In with (a := Twolong hi lo) in TAIL; [|econs; eauto]. *)
(*         eapply regs_of_rpair_In in TAIL. tauto. *)
(*     + eapply IHl; auto. *)
(*       eapply is_tail_trans; eauto. econs 2. econs 1. *)
(*   - econs; ss; eauto. *)
(*     + refl. *)
(*     + intros b ofs0 IN PERM. des_ifs. *)
(*       * exfalso. apply IN. eapply Mem.perm_alloc_3; eauto. *)
(*       * f_equal. eapply PMap.gso; auto. *)
(*   - ss. ii. unfold Mem.perm. ss. *)
(*     eapply Mem.perm_alloc_2; eauto. *)
(* Qed. *)
