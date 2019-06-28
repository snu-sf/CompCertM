Require Import AST Coqlib.
Require Import Asm.
Require Import sflib.
Require Import AsmC Mod.
Require Import MutrecHeader Integers.

Definition _memoized : ident := 60%positive.
Definition lb0: label := 1%positive.
Definition lb1: label := 2%positive.
Definition lb2: label := 3%positive.


Definition code: list instruction :=
 [
   (* .cfi_startproc *)
   Pallocframe 32 (Ptrofs.repr 24) Ptrofs.zero ;
     (* subq    $24, %rsp *)
     (* .cfi_adjust_cfa_offset    24 *)
     (* leaq    32(%rsp), %rax *)
     (* movq    %rax, 0(%rsp) *)
     Pmov_mr_a (Addrmode (Some RSP) None (inl 8)) RBX;
     (* movq    %rbx, 8(%rsp) *)
     Pmov_rr RBX RDI ;
     (* movq    %rdi, %rbx *)
     Ptestl_rr RBX RBX ;
     (* testl    %ebx, %ebx *)
     Pjcc Cond_ne lb0;
     (* jne    .L100 *)
     Pxorl_r RAX;
     (* xorl    %eax, %eax *)
     Pjmp_l lb1;
     (* jmp    .L101 *)

     Plabel lb0 ;
     (* .L100: *)
     Pmovl_rm RAX (Addrmode None None (inr (_memoized, Ptrofs.zero)));
     (* movl	memoized(%rip), %eax *)
     Pcmpl_rr RBX RAX;
     (* cmpl	%eax, %ebx *)
     Pjcc Cond_e lb2;
     (* je	.L102 *)
     Pleal RDI (Addrmode (Some RBX) None (inl (- 1)));
     (* leal    -1(%ebx), %edi *)
     Pcall_s f_id (mksignature [Tint] (Some Tint) cc_default);
     (* call    f *)
     Pleal RAX (Addrmode (Some RAX) (Some (RBX, 1)) (inl 0));
     (* leal    0(%eax,%ebx,1), %eax *)
     Pmovl_mr (Addrmode None None (inr (_memoized, Ptrofs.zero))) RAX;
     (*	movl	%ebx, memoized(%rip) *)
     Pmovl_mr (Addrmode None None (inr (_memoized, Ptrofs.repr 4))) RAX;
     (*	movl	%ebx, (memoized + 4)(%rip) *)     
     Pjmp_l lb1;
     (* jmp    .L101 *)

     Plabel lb2 ;
     (* .L102: *)
     Pmovl_rm RAX (Addrmode None None (inr (_memoized, Ptrofs.repr 4)));
     (* movl	(memoized + 4)(%rip), %eax *)
     
     Plabel lb1 ;
     (* .L101: *)
     Pmov_rm_a RBX (Addrmode (Some RSP) None (inl 8));
     (* movq    8(%rsp), %rbx *)
     Pfreeframe 32 (Ptrofs.repr 24) Ptrofs.zero;
     (* addq    $24, %rsp *)
     Pret
       (* ret *)
 ].

Definition func_g: function :=
  mkfunction (mksignature [Tint] (Some Tint) cc_default) code
.

Definition prog: program := mkprogram [(g_id, (Gfun (Internal func_g)))] [g_id ; main_id] main_id.

Definition md: Mod.t := AsmC.module prog.