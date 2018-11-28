Require Import Axioms CoqlibC Maps Errors.
Require Import AST Linking.
Require Archi.
(** newly added **)
Require Export Ctypes.
(* Csem Csyntax ASTC. *)
Require Import Errors.
Require Import Values.
Require Import sflib.
Require Import Skeleton ASTC.

Set Implicit Arguments.

Generalizable Variables F.

Definition fundef_of_fundef F (f: Ctypes.fundef F): AST.fundef F :=
  match f with
  | Internal f => AST.Internal f
  | External ef _ _ _ => AST.External ef
  end
.

Coercion fundef_of_fundef: Ctypes.fundef >-> AST.fundef.


Definition globdef_of_globdef F V (gd: globdef (Ctypes.fundef F) V) : globdef (AST.fundef F) V :=
  match gd with
  | Gfun fd => Gfun (fundef_of_fundef fd)
  | Gvar v => Gvar v
  end.

(* Definition is_external F (gd: globdef (Ctypes.fundef F) type): bool := *)
(*   match gd with *)
(*   | Gfun fd => is_external_fd fd *)
(*   | Gvar _ => false *)
(*   end *)
(* . *)

Global Instance fundef_HasExternal {F}: HasExternal (Ctypes.fundef F) :=
  Build_HasExternal (fun fd => is_external_fd (fundef_of_fundef fd)).

(* Module CSkEnv. *)

(*   Definition revive {F} (skenv: SkEnv.t) (prog: Ctypes.program F): Genv.t (Ctypes.fundef F) type := *)
(*     skenv.(Genv_map_defs) (fun blk gd => (do id <- skenv.(Genv.invert_symbol) blk; *)
(*                                          do gd <- prog.(prog_defmap) ! id; *)
(*                                          assertion (negb (is_external gd)); *)
(*                                          Some gd)) *)
(*   . *)

(*   Lemma revive_no_external *)
(*         F (prog: Ctypes.program F) *)
(*         skenv blk gd *)
(*         (DEF: Genv.find_def (revive skenv prog) blk = Some gd) *)
(*         (EXTERNAL: is_external gd) *)
(*     : *)
(*       False *)
(*   . *)
(*   Proof. *)
(*     unfold revive in *. *)
(*     apply_all_once Genv_map_defs_def. des. *)
(*     u in *. des_ifs. *)
(*   Qed. *)

(* End CSkEnv. *)

(* Definition program_of_program' F (p: program F) : AST.program (AST.fundef F) type := *)
(*   {| AST.prog_defs := map (fun idg => update_snd (@globdef_of_globdef _ _) idg) p.(prog_defs); *)
(*      AST.prog_public := p.(prog_public); *)
(*      AST.prog_main := p.(prog_main) |}. *)

(* Coercion program_of_program': program >-> AST.program. *)

Module CSk.

  Definition of_program {F} (get_sg: F -> signature) (prog: Ctypes.program F): Sk.t :=
    mkprogram (skdefs_of_gdefs get_sg (map (update_snd (@globdef_of_globdef F type)) prog.(prog_defs))) prog.(prog_public) prog.(prog_main)
  .

  Lemma of_program_defs
        F
        get_sg
        (p: Ctypes.program F)
    :
      (of_program get_sg p).(defs) = p.(defs)
  .
  Proof.
    destruct p; ss.
    Local Opaque in_dec.
    u; ss.
    Local Transparent in_dec.
    apply Axioms.functional_extensionality. intro id; ss.
    Check (in_dec ident_eq id (map fst prog_defs)).
    rewrite map_map. rewrite map_map. ss.
  Qed.

End CSk.

