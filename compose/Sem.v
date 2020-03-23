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
      (MODSEM: In ms (fst ge))
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
    (MSFIND: ge.(Ge.find_fptr_owner) (Args.get_fptr args) ms)
    (INIT: ms.(ModSem.initial_frame) args st_init):
    step ge (Callstate args frs)
         E0 (State ((Frame.mk ms st_init) :: frs))

| step_internal
    fr0 frs tr st0
    (STEP: Step (fr0.(Frame.ms)) fr0.(Frame.st) tr st0):
    step ge (State (fr0 :: frs))
         tr (State (((Frame.update_st fr0) st0) :: frs))
| step_return
    fr0 fr1 frs retv st0
    (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
    (AFTER: fr1.(Frame.ms).(ModSem.after_external) fr1.(Frame.st) retv st0):
    step ge (State (fr0 :: fr1 :: frs))
         E0 (State (((Frame.update_st fr1) st0) :: frs)).




Section SEMANTICS.

  Variable p: program.

  Definition p_sys: program := System.module (link_list (List.map Mod.sk p)) :: p.

  Definition link_sk: option Sk.t := link_list (List.map Mod.sk p_sys).

  (* Making dummy_module that calls main? => Then what is sk of it? Memory will be different with physical linking *)
  Inductive initial_state: state -> Prop :=
  | initial_state_intro
      sk_link skenv_link m_init fptr_init
      (INITSK: link_sk = Some sk_link)
      (INITSKENV: (Sk.load_skenv sk_link) = skenv_link)
      (INITMEM: (Sk.load_mem sk_link) = Some m_init)
      (FPTR: fptr_init = (Genv.symbol_address skenv_link sk_link.(prog_main) Ptrofs.zero))
      (SIG: (Genv.find_funct skenv_link) fptr_init = Some (Internal signature_main))
      (WF: forall md (IN: In md p), <<WF: Sk.wf md>>):
      initial_state (Callstate (Args.mk fptr_init [] m_init) []).

  Inductive final_state: state -> int -> Prop :=
  | final_state_intro
      fr0 retv i
      (FINAL: fr0.(Frame.ms).(ModSem.final_frame) fr0.(Frame.st) retv)
      (INT: (Retv.v retv) = Vint i):
      final_state (State [fr0]) i.

  (* Definition load_modsems (skenv: SkEnv.t): list ModSem.t := List.map ((flip Mod.modsem) skenv) p. *)

  Definition load_genv (init_skenv: SkEnv.t): Ge.t :=
    (List.map ((flip Mod.modsem) init_skenv) p_sys, init_skenv)
  .

  Definition sem: semantics :=
    (Semantics_gen (fun _ => step) initial_state final_state
                   (match link_sk with
                    | Some sk_link => load_genv (Sk.load_skenv sk_link)
                    | _ => (nil, SkEnv.empty)
                    end)
                   (* NOTE: The symbolenv here is never actually evoked in our semantics. Putting this value is merely for our convenience. (lifting receptive/determinate) Whole proof should be sound even if we put dummy data here. *)
                   (match link_sk with
                    | Some sk_link => (Sk.load_skenv sk_link)
                    | _ => SkEnv.empty
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

Hint Unfold link_sk load_genv.
