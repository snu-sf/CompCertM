Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import GlobalenvsC.
Require Import LinkingC.
Require Import CoqlibC.
Require Import sflib.

Require Import ModSem Mod Skeleton System.
Require Export Syntax.

Set Implicit Arguments.









Module Frame.

  Record t: Type := mk {
    ms: ModSem.t;
    st: ms.(ModSem.state); (* local state *)
  }.

  Definition update_st (fr0: t) (st0: fr0.(ms).(ModSem.state)): t := (mk fr0.(ms) st0).

End Frame.



Module Ge.

  (* NOTE: Ge.(snd) is not used in semantics. It seems it is just for convenience in meta theory *)
  Definition t: Type := (list ModSem.t * SkEnv.t).

  Inductive find_fptr_owner (ge: t) (fptr: val) (ms: ModSem.t): Prop :=
  | find_fptr_owner_intro
      (MODSEM: In ms ge.(fst))
      if_sig
      (INTERNAL: Genv.find_funct ms.(ModSem.skenv) fptr = Some (Internal if_sig)).

  Inductive disjoint (ge: t): Prop :=
  | disjoint_intro
      (DISJOINT: forall fptr ms0 ms1
          (FIND0: ge.(find_fptr_owner) fptr ms0)
          (FIND1: ge.(find_fptr_owner) fptr ms1),
          ms0 = ms1).

End Ge.

Inductive state: Type :=
| Callstate
    (args: Args.t)
    (frs: list Frame.t)
| State
    (frs: list Frame.t).

Inductive step (ge: Ge.t): state -> trace -> state -> Prop :=
| step_call
    fr0 frs args
    (AT: fr0.(Frame.ms).(ModSem.at_external) fr0.(Frame.st) args):
    step ge (State (fr0 :: frs))
         E0 (Callstate args (fr0 :: frs))

| step_init
    args frs ms st_init
    (MSFIND: ge.(Ge.find_fptr_owner) args.(Args.get_fptr) ms)
    (INIT: ms.(ModSem.initial_frame) args st_init):
    step ge (Callstate args frs)
         E0 (State ((Frame.mk ms st_init) :: frs))

| step_internal
    fr0 frs tr st0
    (STEP: Step (fr0.(Frame.ms)) fr0.(Frame.st) tr st0):
    step ge (State (fr0 :: frs))
         tr (State ((fr0.(Frame.update_st) st0) :: frs))
| step_return
    fr0 fr1 frs retv st0
    (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
    (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) retv st0):
    step ge (State (fr0 :: fr1 :: frs))
         E0 (State ((fr1.(Frame.update_st) st0) :: frs)).




Section SEMANTICS.

  Variable p: program.

  Definition link_sk: option Sk.t := link_list (List.map Mod.sk p).

  Definition skenv_fill_internals (skenv: SkEnv.t): SkEnv.t :=
    skenv.(Genv_map_defs) (fun _ gd => Some
                                      match gd with
                                      | Gfun (External ef) => (Gfun (Internal ef.(ef_sig)))
                                      | Gfun _ => gd
                                      | Gvar gv => gd
                                      end).

  Definition load_system (skenv: SkEnv.t): (ModSem.t * SkEnv.t) :=
    (System.modsem skenv, skenv.(skenv_fill_internals)).

  Definition load_modsems (skenv: SkEnv.t): list ModSem.t := List.map ((flip Mod.modsem) skenv) p.

  Definition load_genv (init_skenv: SkEnv.t): Ge.t :=
    let (system, skenv) := load_system init_skenv in
    (system :: (load_modsems init_skenv), init_skenv).

  (* Making dummy_module that calls main? => Then what is sk of it? Memory will be different with physical linking *)
  Inductive initial_state: state -> Prop :=
  | initial_state_intro
      sk_link skenv_link m_init fptr_init
      (INITSK: link_sk = Some sk_link)
      (INITSKENV: sk_link.(Sk.load_skenv) = skenv_link)
      (INITMEM: sk_link.(Sk.load_mem) = Some m_init)
      (FPTR: fptr_init = (Genv.symbol_address skenv_link sk_link.(prog_main) Ptrofs.zero))
      (SIG: skenv_link.(Genv.find_funct) fptr_init = Some (Internal signature_main))
      (WF: forall md (IN: In md p), <<WF: Sk.wf md>>):
      initial_state (Callstate (Args.mk fptr_init [] m_init) []).

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro
      fr0 retv i
      (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
      (INT: retv.(Retv.v) = Vint i):
      final_state (State [fr0]) i.

  Definition sem: semantics :=
    (Semantics_gen (fun _ => step) initial_state final_state
                   (match link_sk with
                    | Some sk_link => load_genv sk_link.(Sk.load_skenv)
                    | None => (nil, SkEnv.empty)
                    end)
                   (* NOTE: The symbolenv here is never actually evoked in our semantics. Putting this value is merely for our convenience. (lifting receptive/determinate) Whole proof should be sound even if we put dummy data here. *)
                   (match link_sk with
                    | Some sk_link => sk_link.(Sk.load_skenv)
                    | None => SkEnv.empty
                    end)).
  (* Note: I don't want to make it option type. If it is option type, there is a problem. *)
  (* I have to state this way:
```
Variable sem_src: semantics.
Hypothesis LOADSRC: load p_src = Some sem_src.
```
Then, sem_src.(state) is not evaluatable.
   *)
  (* However, if it is not option type.
```
Let sem_src := semantics prog.
```
Then, sem_src.(state) is evaluatable.
   *)

End SEMANTICS.

Hint Unfold link_sk load_modsems load_genv.
