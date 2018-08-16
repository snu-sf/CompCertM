Require Import Axioms CoqlibC Maps Errors.
Require Import AST Linking.
Require Archi.

Require Export Ctypes Csem Csyntax ASTC.
Require Import Errors.
Require Import sflib.
Require Import Skeleton ASTC.

Set Implicit Arguments.

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

Section CSPECIFIC.

  Definition is_external F (gd: globdef (Ctypes.fundef F) type): bool :=
    match gd with
    | Gfun fd => is_external_fd fd
    | Gvar _ => false
    end
  .

  Definition revive {F} (skenv: SkEnv.t) (prog: Ctypes.program F): Genv.t (Ctypes.fundef F) type :=
    skenv.(Genv_map_defs) (fun blk gd => (do id <- skenv.(Genv.invert_symbol) blk;
                                         do gd <- prog.(prog_defmap) ! id;
                                         assertion (negb (is_external gd));
                                         Some gd))
  .

  Lemma revive_no_external
        F (prog: Ctypes.program F)
        skenv blk gd
        (DEF: Genv.find_def (revive skenv prog) blk = Some gd)
        (EXTERNAL: is_external gd)
    :
      False
  .
  Proof.
    unfold revive in *.
    apply_all_once Genv_map_defs_def. des.
    u in *. des_ifs.
  Qed.
  
  Definition signature_of_function (f: function) :=
    {| sig_args := map typ_of_type (map snd (fn_params f));
       sig_res  := opttyp_of_type (fn_return f);
       sig_cc   := fn_callconv f |}.
  
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

End CSPECIFIC.


