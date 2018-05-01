Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Asmregs.
Require Import Linking.
Require Import CoqlibC.
Require Import sflib.

Require Import ModSem Mod Skeleton LinkingC.
Require Export Syntax.

Set Implicit Arguments.










Module Frame.

  (* Naming Candidates *)
  (* Module -> Short pronunciation. its shorhand "m" conflicts with "m" of "memory". *)
  (* StackFrame (Activation Record) -> Too long *)
  (* Frame -> Short, also it is quite clear (Frame is not used elsewhere in this level) *)

  Record t: Type := mk {
    ms: ModSem.t;
    st: ms.(ModSem.state);
    sg_arg: option signature; (* caller's sig *)
    sg_init: option signature; (* callee's sig *)
    rs_arg: regset;
  }
  .

  Definition update_st (fr0: t) (st: fr0.(ms).(ModSem.state)): t :=
    (mk fr0.(ms) st fr0.(sg_arg) fr0.(sg_init) fr0.(rs_arg))
  .

(* Definition is_internal (fr0: t): Prop := fr0.(ms).(ModSem.is_internal) fr0.(st) fr0.(sg_arg) fr0.(rs_arg). *)
  (* Definition is_internal (fr0: t): Prop := fr0.(ms).(ModSem.is_internal) fr0.(st). *)

End Frame.



Module Ge.

  (* NAMING: Consistency with SkEnv.t -> GEnv.t? but this is confusing with Genv *)
  Record t: Type := mk {
    skenv: SkEnv.t;
    mss: list ModSem.t;
  }
  .

  Inductive find_fptr_owner (ge: t) (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      blk
      (FPTR: fptr = Vptr blk Ptrofs.zero true)
      (MODSEM: List.In ms ge.(mss))
      if_sig
      (INTERNAL: Genv.find_def ms.(ModSem.skenv) blk = Some (Gfun (Internal if_sig)))
  .

  Definition no_fptr_owner (ge: t) (fptr: val): Prop :=
    List.Forall (not <*> find_fptr_owner ge fptr) ge.(mss).

End Ge.

Definition state: Type := list Frame.t.

(* If both are some, they are equal. *)
Definition compat_sig (sg0: option signature) (sg1: option signature): bool :=
  match sg0 with
  | None => true
  | Some sg0 => match sg1 with
           | None => true
           | Some sg1 => signature_eq sg0 sg1
           end
  end
.

(* Naming -> fr0/fr1 instead of fr_fst fr_snd. There will not be many fr_fst simultaneously, so it is OK *)
Inductive step (ge: Ge.t): state -> trace -> state -> Prop :=
| step_call
    fr0 frs
    fptr_arg sg_arg rs_arg m_arg
    (CALL: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) fptr_arg sg_arg rs_arg m_arg)
    (* id *)
    (* (IDFIND: ge.(Ge.skenv).(Genv.invert_symbol) fptr_arg = Some id) *)
    if_sig
    (SIGFIND: ge.(Ge.skenv).(Genv.find_funct) fptr_arg = Some (Internal if_sig))
    (SIG: compat_sig sg_arg if_sig)
    ms
    (MSFIND: ge.(Ge.find_fptr_owner) fptr_arg ms)
    st_init
    (INIT: ms.(ModSem.initial_machine) fptr_arg sg_arg rs_arg m_arg st_init)
  :
    step ge (fr0 :: frs)
         E0 ((Frame.mk ms st_init sg_arg if_sig rs_arg) :: fr0 :: frs)
| step_return
    fr0 fr1 frs
    rs_ret m_ret
    (FINAL: fr0.(Frame.ms).(ModSem.final_machine) fr0.(Frame.sg_init) fr0.(Frame.rs_arg) fr0.(Frame.st)
                                                  rs_ret m_ret)
    st0
    (RETURN: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) fr0.(Frame.sg_arg) fr0.(Frame.rs_arg) rs_ret m_ret st0)
  :
    step ge (fr0 :: fr1 :: frs)
         E0 ((fr1.(Frame.update_st) st0) :: frs)
| step_internal
    fr0 frs
    (* (INTERNAL: fr0.(Frame.is_internal)) *)
    tr st0
    (STEP: fr0.(Frame.ms).(ModSem.step) fr0.(Frame.ms).(ModSem.globalenv) fr0.(Frame.st) tr st0)
  :
    step ge (fr0 :: frs)
         tr ((fr0.(Frame.update_st) st0) :: frs)
| step_syscall
    fr0 frs
    fptr_arg sg_arg rs_arg m_arg
    (CALL: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) fptr_arg sg_arg rs_arg m_arg)
    (MSNOTFIND: ge.(Ge.no_fptr_owner) fptr_arg)
    ef
    (SYSFIND: ge.(Ge.skenv).(Genv.find_funct) fptr_arg = Some (External ef))
    (SIG: compat_sig sg_arg (Some ef.(ef_sig)))
    (* Below is copied from Asm.v *)
    vs_arg
    (SYSARGS: extcall_arguments rs_arg m_arg (ef_sig ef) vs_arg)
    tr v_ret m_ret
    (SYSSEM: external_call ef ge.(Ge.skenv) vs_arg m_arg tr v_ret m_ret)
    rs_ret
    (RETREGS: rs_ret= (Pregmap.set PC (rs_arg RA)
                                   (set_pair (loc_external_result (ef_sig ef)) v_ret
                                             (undef_regs (map preg_of Conventions1.destroyed_at_call) rs_arg))))
    st0
    (RETURN: fr0.(Frame.ms).(ModSem.after_external) fr0.(Frame.st) sg_arg rs_arg rs_ret m_ret st0)
  :
    step ge (fr0 :: frs)
         E0 ((fr0.(Frame.update_st) st0) :: frs)
.




Section SEMANTICS.

  Variable p: program.
  (* Variable init_skel: Skel.t. *)
  (* Hypothesis LINKED: link_list (List.map Mod.skel p) = Some init_skel. *)

  Definition link_sk: option Sk.t := link_list (List.map Mod.sk p).

  (* Definition init_skenv: option SkEnv.t := option_map (@Genv.globalenv (fundef unit) unit) init_sk. *)
  (* Definition init_skenv (init_sk: Sk.t): SkEnv.t := (@Genv.globalenv (fundef (option signature)) unit) init_sk. *)

  Definition load_modsems (skenv: SkEnv.t): list ModSem.t := List.map ((flip Mod.modsem) skenv) p.

  (* Definition init_mem: option mem := option_join (option_map (@Genv.init_mem (fundef unit) unit) init_sk). *)
  (* Definition init_mem (init_sk: Sk.t): option mem := (@Genv.init_mem (fundef (option signature)) unit) init_sk. *)

  (* Definition init_genv: option Ge.t := *)
  (*   option_map (fun skenv => (Ge.mk skenv (init_modsem skenv))) init_skenv. *)
  Definition load_genv (init_skenv: SkEnv.t): Ge.t := Ge.mk init_skenv (load_modsems init_skenv).

  (* Making dummy_module that calls main? => Then what is sk of it? Memory will be different with physical linking *)
  Inductive initial_state: state -> Prop :=
  | initial_state_intro
      sk_link skenv_link m ge
      (INITSK: link_sk = Some sk_link)
      (INITSKENV: sk_link.(Sk.load_skenv) = skenv_link)
      (INITMEM: sk_link.(Sk.load_mem) = Some m)
      (INITGENV: load_genv skenv_link = ge)

      fptr_arg
      (INITFPTR: Genv.symbol_address skenv_link sk_link.(prog_main) Ptrofs.zero = fptr_arg)
      ms
      (MSFIND: ge.(Ge.find_fptr_owner) fptr_arg ms)

      sg_arg
      (INITSG: sg_arg = None)
      rs_arg
      (INITREG: rs_arg = Pregmap.init Vundef)
      st_init
      (INIT: ms.(ModSem.initial_machine) fptr_arg sg_arg rs_arg m st_init)
    :
      initial_state ((Frame.mk ms st_init None sg_arg rs_arg) :: nil)
  .

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro
      fr0
      rs_ret m_ret
      (FINAL: fr0.(Frame.ms).(ModSem.final_machine) fr0.(Frame.sg_arg) fr0.(Frame.rs_arg) fr0.(Frame.st)
                                                    rs_ret m_ret)
      retv
      (RETV: rs_ret RAX = Vint retv)
    :
      final_state [fr0] retv
  .

  Definition load: option semantics :=
    match link_sk with
    | Some sk_link => Some (Semantics_gen step initial_state final_state
                                          (load_genv sk_link.(Sk.load_skenv))
                                          (* (load_genv sk.(Sk.load_skenv)).(Ge.skenv) *)
                                          (admit "dummy for now. it is not used")
                           )
    | None => None
    end
  .

End SEMANTICS.

Hint Unfold link_sk load_modsems load_genv load.

