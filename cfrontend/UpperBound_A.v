Require Import CoqlibC Maps.
Require Import ASTC Integers Floats Values MemoryC Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions Linking.
(** newly added **)
Require Export Csem Cop Ctypes Ctyping Csyntax Cexec.
Require Import Simulation Memory ValuesC.
Require Import Skeleton ModSem Mod sflib.
Require Import CtypesC CsemC Sem Syntax LinkingC Program.

Set Implicit Arguments.

Local Opaque Z.mul.

Section PRESERVATION.

  Existing Instance Val.mi_final.

(** UpperBound A *)

(*
A
* : Physical
+ : Logical 
(c0 * c1) + ctx
>=
(c0 + c1) + ctx
*)
  
(*
B
* : Physical
+ : Logical 
c0 * empty
>=
c0 + empty
*)
  

  Section PLANB1.

(** ********************* linking *********************************)    
  Variable prog1 : Csyntax.program.
  Variable prog2 : Csyntax.program.
  Variable prog' : Csyntax.program.
  Hypothesis LINK : link prog1 prog2 = Some prog'.
  Let tprog' : Syntax.program := List.map CsemC.module [prog2; prog1].
  Variable ctx : Syntax.program.

  Let prog : Syntax.program := CsemC.module prog' :: ctx.
  Let tprog : Syntax.program := tprog' ++ ctx.

(** ********************* linking *********************************)

  Variable sk_src: Sk.t.
  Hypothesis LINK_SK_SRC: link_sk prog = Some sk_src.
  (* TODO: consider linking fail case *)
  Let skenv_link_src := Sk.load_skenv sk_src.

  Variable sk_tgt: Sk.t.
  Hypothesis LINK_SK_TGT: link_sk tprog = Some sk_tgt.
  (* TODO: consider linking fail case *)
  Let skenv_link_tgt := Sk.load_skenv sk_tgt.
  
  Let ge := load_genv prog skenv_link_src.
  (* Let ge_ce : composite_env := prog_comp_env prog. *)
  (* Let tge_ce : composite_env := prog_comp_env prog. *)
  Let tge := load_genv tprog skenv_link_tgt.
(* Inductive match_states_aux : Csem.State -> Sem.state -> nat -> Prop := *)

  
  (*
  (c0 * c1) + ctx
  >=
  (c0 + c1) + ctx
  src : physical
  tgt : logical

  src has 3 Modules (C0*C1), ctx, Sys
  tgt has 4 Modules C0, C1, ctx, Sys

  there are "5" kinds of match states needed(maybe)
  1. reg - reg 
  2. call - call
  3. reg - call ----> only btw c maybe
  (* 4. ret - ret *)
  (* 5. reg - ret *)
  what is reg state? 1. internal 
   *)
  Fixpoint app_cont (c1 c2: cont) : cont :=
    match c1 with
    | Kstop => c2
    | Kdo c => Kdo (app_cont c c2)
    | Kseq s c => Kseq s (app_cont c c2)
    | Kifthenelse s1 s2 c => Kifthenelse s1 s2 (app_cont c c2)
    | Kwhile1 e s c => Kwhile1 e s (app_cont c c2)
    | Kwhile2 e s c => Kwhile2 e s (app_cont c c2)
    | Kdowhile1 e s c => Kdowhile1 e s (app_cont c c2)
    | Kdowhile2 e s c => Kdowhile2 e s (app_cont c c2)
    | Kfor2 e s1 s2 c => Kfor2 e s1 s2 (app_cont c c2)
    | Kfor3 e s1 s2 c => Kfor3 e s1 s2 (app_cont c c2)
    | Kfor4 e s1 s2 c => Kfor4 e s1 s2 (app_cont c c2)
    | Kswitch1 ls c =>  Kswitch1 ls (app_cont c c2)
    | Kswitch2 c =>  Kswitch2 (app_cont c c2)
    | Kreturn c => Kreturn (app_cont c c2)
    | Kcall f e em ty c => Kcall f e em ty (app_cont c c2)
    end.

  Inductive similar_state : Csem.state -> Csem.state -> cont -> Prop :=
  | reg_state_similar
      f s c c0 c1 e m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.State f s c e m) (Csem.State f s c1 e m) c0
  | expr_state_similar
      f ex c c0 c1 e m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.ExprState f ex c e m) (Csem.ExprState f ex c1 e m) c0
  | call_sate_similar
      fptr tyf vargs c c0 c1 m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.Callstate fptr tyf vargs c m) (Csem.Callstate fptr tyf vargs c1 m) c0
  | return_sate_similar
      vres c c0 c1 m
      (CONT: c = app_cont c1 c0)
    : similar_state (Csem.Returnstate vres c m) (Csem.Returnstate vres c1 m) c0
  | stuck_state_similar
      c0
    : similar_state Csem.Stuckstate Csem.Stuckstate c0.

  Inductive match_frames : list Frame.t -> list Frame.t -> Prop :=
  | match_frames_nil
    :
      match_frames nil nil
  | match_frames_cons_sys
      fr_src frs_src fr_tgt frs_tgt st
      (MATCH: match_frames frs_src frs_tgt)
      (SYS1: fr_src = Frame.mk (System.modsem skenv_link_src) st)
      (SYS1: fr_tgt = Frame.mk (System.modsem skenv_link_tgt) st)
    :
      match_frames (fr_src::frs_src) (fr_src::frs_tgt)
  | match_frames_cons_ctx
      fr_src frs_src fr_tgt frs_tgt
      m st1 st2 (* state must be same?? i dont think so *)
      (MATCH: match_frames frs_src frs_tgt)
      (MOD: In m ctx)
      (CTX1: fr_src = Frame.mk (Mod.get_modsem m skenv_link_src (Mod.data m)) st1)
      (CTX2: fr_tgt = Frame.mk (Mod.get_modsem m skenv_link_tgt (Mod.data m)) st2)
    :
      match_frames (fr_src::frs_src) (fr_src::frs_tgt)
  | match_frames_cons_c_one
      fr_src frs_src fr_tgt frs_tgt prog_tgt st_src st_tgt
      (MATCH: match_frames frs_src frs_tgt)
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (CSTATE1: fr_src = Frame.mk (CsemC.modsem skenv_link_src prog') st_src)
      (CSTATE2: fr_tgt = Frame.mk (CsemC.modsem skenv_link_src prog_tgt) st_tgt)
      (SAME: st_src = st_tgt) (* everything is the same, including cont *)
    :
      match_frames (fr_src::frs_src) (fr_tgt::frs_tgt) (* this case needed? *)
  | match_frames_cons_c_two
      fr_src frs_src fr_tgt0 fr_tgt1 frs_tgt
      st_src st_tgt0 st_tgt1 fptr tyf vs_arg c0 m0 prog_tgt
      (MATCH: match_frames frs_src frs_tgt)
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (C0STATE: st_tgt0 = Csem.Callstate fptr tyf vs_arg c0 m0)      
      (C0EXT: at_external skenv_link_tgt prog_tgt st_tgt0 (Args.mk fptr vs_arg m0))
      (SIMILAR: similar_state st_src st_tgt1 c0)
    :
      match_frames (fr_src::frs_src) (fr_tgt1::fr_tgt0::frs_tgt).

  Inductive match_owner : ModSem.t -> ModSem.t -> Prop :=
  | match_sys
      ms1 ms2
      (SYS1: ms1 = System.modsem skenv_link_src)
      (SYS2: ms2 = System.modsem skenv_link_tgt)
    :
      match_owner ms1 ms2
  | match_ctx
      m ms1 ms2
      (MOD: In m ctx)
      (CTX1: ms1 = Mod.get_modsem m skenv_link_src (Mod.data m))
      (CTX2: ms2 = Mod.get_modsem m skenv_link_tgt (Mod.data m))
    :
      match_owner ms1 ms2
  | match_cmod
      prog_tgt ms1 ms2
      (PROG: prog_tgt = prog1 \/ prog_tgt = prog2)
      (CMOD1: ms1 = CsemC.modsem skenv_link_src prog')
      (CMOD2: ms2 = CsemC.modsem skenv_link_tgt prog_tgt)
    :
      match_owner ms1 ms2.

  Inductive match_states : Sem.state -> Sem.state -> nat -> Prop :=
  | match_regular_states
      frs_src frs_tgt
      (FMATCH: match_frames frs_src frs_tgt)
    :
      match_states (State frs_src) (State frs_tgt) 0
  | match_call_states
      args_src frs_src args_tgt frs_tgt ms1 ms2
      (OWNER1: Ge.find_fptr_owner ge (Args.fptr args_src) ms1)
      (OWNER2: Ge.find_fptr_owner tge (Args.fptr args_tgt) ms2)
      (FMATCH: match_frames frs_src frs_tgt)
      (OWNER: match_owner ms1 ms2)
    :
      match_states (Callstate args_src frs_src) (Callstate args_tgt frs_tgt) 0
  | 
      
  .

  (* 
  Inlining
  src - not inlined 
  tgt - inlined 

  so....
  src has more "function call"
  1. reg - reg 
  2. call - call
  3. call - reg
  4. ret - ret
  5. ret - reg
  *)

  Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sp' rs' m' F fenv ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (State stk f (Vptr sp Ptrofs.zero true) pc rs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero true) (spc ctx pc) rs' m')
  | match_call_states: forall stk fptr sg tfptr args m stk' args' m' F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (FPTR: Val.inject F fptr tfptr)
        (VINJ: Val.inject_list F args args')
        (MINJ: Mem.inject F m m'),
      match_states (Callstate stk fptr sg args m)
                   (Callstate stk' tfptr sg args' m')
  | match_call_regular_states: forall stk fptr sg f vargs m stk' f' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (FPTR: Genv.find_funct ge fptr = Some (Internal f))
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Callstate stk fptr sg vargs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero true) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F
        (MS: match_stacks F m m' stk stk' (Mem.nextblock m'))
        (VINJ: Val.inject F v v')
        (MINJ: Mem.inject F m m'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sp' rs' m' F ctx pc' or rinfo
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (MINJ: Mem.inject F m m')
        (VB: Mem.valid_block m' sp')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Ptrofs.zero true) pc' rs' m').


  Inductive match_stacks (F: meminj) (m m': mem):
             list stackframe -> list stackframe -> block -> Prop :=
  | match_stacks_nil: forall bound1 bound
        (MG: match_globalenvs F bound1)
        (BELOW: Ple bound1 bound),
      match_stacks F m m' nil nil bound
  | match_stacks_cons: forall res f sp pc rs stk f' sp' rs' stk' bound fenv ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Plt sp' bound),
      match_stacks F m m'
                   (Stackframe res f (Vptr sp Ptrofs.zero true) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero true) (spc ctx pc) rs' :: stk')
                   bound
  | match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
        (MS: match_stacks_inside F m m' stk stk' f' ctx sp' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Plt sp' bound),
      match_stacks F m m'
                   stk
                   (Stackframe res f' (Vptr sp' Ptrofs.zero true) rpc rs' :: stk')
                   bound

with match_stacks_inside (F: meminj) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
        (MS: match_stacks F m m' stk stk' sp')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' stk stk' f' ctx sp' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sp' rs' ctx'
        (MS: match_stacks_inside F m m' stk stk' f' ctx' sp' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' (Stackframe res f (Vptr sp Ptrofs.zero true) pc rs :: stk)
                                 stk' f' ctx sp' rs'.
