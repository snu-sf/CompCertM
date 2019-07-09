Require Import AST Coqlib.
Require Import Asm.
Require Import sflib.
Require Import AsmC Mod.
Require Import DemoHeader.

Definition lb0: label := 1%positive.
Definition code: list instruction :=
  [
    Ptestq_rr RDI RDI ;
      Pjcc Cond_s lb0 ;
      Pxorpd_f XMM0 ;
      (* note: actual code is pxor, but it it prints xorpd *)
      (* it also prints the same thing: Pxorps_f XMM0 ; *)
      Pcvtsl2sd_fr XMM0 RDI ;
      Pret ;

      Plabel lb0 ;
      Pmov_rr RAX RDI ;
      Pshrq_ri RAX Integers.Int.one ;
      Pandq_ri RDI Integers.Int64.one ;
      Porq_rr RAX RDI ;
      Pxorpd_f XMM0 ;
      Pcvtsl2sd_fr XMM0 RAX ;
      Paddd_ff XMM0 XMM0 ;
      Pret
  ].

Definition func: function :=
  mkfunction (mksignature [Tlong] (Some Tfloat) cc_default true) code
.

Definition prog: program := mkprogram [(func_id, (Gfun (Internal func)))] [func_id ; main_id] main_id.

Definition md: Mod.t := AsmC.module prog.

Hint Unfold md prog func code.
