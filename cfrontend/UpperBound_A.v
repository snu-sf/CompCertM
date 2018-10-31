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
  3. call - reg ----> only btw c maybe
  4. ret - ret
  5. ret - reg
  what is reg state? 1. internal 
   *)
  Inductive match_states : Sem.state -> Sem.state -> nat -> Prop :=
  | match_regular_states
      fr_src fr_tgt
      (FRLENSRC: (length fr_src <= 2)%nat)
      (FRLENSRC: (length fr_src <= 3)%nat)
    :
      match_states (State fr_src) (State fr_tgt) 0
  | match_call_states

    :
      match_states 
      
      

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
