Require Import CoqlibC.
Require Export GlobalenvsC.
Require Import Memory.
Require Import Ctypes.
Require Export ASTC.
Require Import MapsC.
Require Import Values.

Set Implicit Arguments.



(* I don't want it to be "AST.program"-dependent, because of Ctypes.program *)
(* TODO: In high level, prog_public can be dropped, as the data is already linked. Is it really so? *)
(* Definition flesh F V := list (ident * globdef F V)%type. *)

(* Skeleton Genv *)
Module SkEnv.

  (* TODO: Fix properly to cope with Ctypes.fundef *)
  Definition t := Genv.t (AST.fundef (option signature)) unit.

  (* Definition project F V (skenv: t) (fl: flesh F V): option (Genv.t F V). *)
  (*   admit "". *)
  (* Defined. *)

  (* TODO: Is it OK to define it in Prop? I just need backward simulation of this. *)
  Inductive project (skenv: t) (ids: ident -> Prop) (skenv_proj: t): Prop :=
  | project_intro
      (PUBLIC: skenv_proj.(Genv.genv_public) = [])
      (* TODO: is this OK? Check if this info affects semantics except for linking *)
      (NEXT: skenv.(Genv.genv_next) = skenv_proj.(Genv.genv_next))
      (PROJ: forall
          id
          (IN: ids id)
        ,
          (<<SYMB: skenv.(Genv.find_symbol) id = skenv_proj.(Genv.find_symbol) id>>))
      (* TODO: I don't need def here. IT will be overwritten. *)
      (NPROJ: forall
          id
          (NIN: ~ ids id)
        ,
          <<NONE: skenv_proj.(Genv.find_symbol) id = None>>)
  .

  (* Definition project (skenv: t) (ids: list ident): option SkEnv.t. *)
  (*   admit "". *)
  (* Defined. *)

  Definition internals (skenv: t): list block :=
    List.map fst (skenv.(Genv.genv_defs).(PTree.elements))
  .

  (* We will not need this for now. Fix it when we need it (dynamic linking/incremental compilation) *)
  Definition filter_symbols (skenv: t) (symbols: list ident): t :=
    skenv.(Genv_filter_symb) (fun id => List.in_dec ident_eq id symbols)
  .

  Definition drop_external_defs (skenv: t): t :=
    skenv.(Genv_map_defs) (fun gd => assertion (negb (is_external gd)); Some gd)
  .

End SkEnv.

(* Skeleton *)
Module Sk.

  Definition t := AST.program (AST.fundef (option signature)) unit.

  Definition load_skenv: t -> SkEnv.t := @Genv.globalenv (AST.fundef (option signature)) unit.
  (* No coercion! *)

  Definition load_mem: t -> option mem := @Genv.init_mem (AST.fundef (option signature)) unit.
  (* No coercion! *)

End Sk.

Hint Unfold Sk.load_skenv Sk.load_mem.



(* They are just located, without any add/remove *)
About Genv.find_def_symbol.
Inductive sk_skenv_iso (sk: Sk.t) (skenv: SkEnv.t): Prop :=
| sk_skenv_iso_intro
    (ISO: forall
        id skd
      ,
        <<SK: sk.(prog_defmap) ! id = Some skd /\ is_internal skd>> <->
        <<SKENV: exists blk, skenv.(Genv.find_symbol) id = Some blk
                             /\ skenv.(Genv.find_def) blk = Some skd>>)
.




(* Question: How does genv affect semantics? *)
Module PLAYGROUND.

Require Import RTL.

Theorem eval_addressing_irr
        F V
        (ge0 ge1: Genv.t F V)
        (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  :
    <<OP: all3 (Op.eval_addressing ge0 =3= Op.eval_addressing ge1)>>
.
Proof.
  u.
  ii. unfold Op.eval_addressing. des_ifs.
  destruct x1; ss.
  { des_ifs. unfold Genv.symbol_address. rewrite SYMB. ss. }
Qed.

Theorem eval_operation_irr
        F V
        (ge0 ge1: Genv.t F V)
        (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  :
    <<OP: all4 (Op.eval_operation ge0 =4= Op.eval_operation ge1)>>
.
Proof.
  u.
  ii.
  destruct x1; ss.
  { des_ifs. unfold Genv.symbol_address. rewrite SYMB. ss. }
  { erewrite eval_addressing_irr; eauto. }
Qed.

Goal forall ge0 ge1 st0 tr st1
            (STEP: step ge0 st0 tr st1)
            (SYMB: all1 (Genv.find_symbol ge0 =1= Genv.find_symbol ge1))
  ,
    <<STEP: step ge1 st0 tr st1>>
.
Proof.
  i. inv STEP; try (by econs; eauto).
  - erewrite eval_operation_irr in *; eauto. econs; eauto.
  - erewrite eval_addressing_irr in *; eauto. econsby eauto.
  - erewrite eval_addressing_irr in *; eauto. econsby eauto.
  - econs; eauto.
    unfold find_function_ptr in *. des_ifs_safe. rewrite SYMB in *. ss.
  - econs; eauto.
    unfold find_function_ptr in *. des_ifs_safe. rewrite SYMB in *. ss.
  - eapply Events.eval_builtin_args_preserved with (ge2 := ge1) in H0; eauto.
    econs; eauto. eapply Events.external_call_symbols_preserved; eauto.
    econs; eauto.
    split.
    admit "Publics".
    Print Genv.block_is_volatile.
    admit "Genv.find_def with Gvar. (volatile)".
  - econs; eauto.
    unfold Genv.find_funct in *. des_ifs.
    unfold Genv.find_funct_ptr in *.
    admit "Genv.find_def with Gfun. internals".
  - unfold Genv.find_funct, Genv.find_funct_ptr in *. des_ifs.
    admit "Genv.find_def with Gfun. externals".
Abort.

End PLAYGROUND.



