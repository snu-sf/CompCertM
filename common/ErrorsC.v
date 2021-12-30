Require Import CoqlibC.
From compcertr Require Import Errors Compiler.

Lemma mmap_app A B (f: A -> res B) l0 l1:
    mmap f (l0 ++ l1) =
    bind (mmap f l0) (fun hds => bind (mmap f l1) (fun tl => OK (hds ++ tl))).
Proof.
  induction l0; ss; i; unfold bind at 1; des_ifs. rewrite IHl0. unfold bind. des_ifs.
Qed.

Lemma mmap_partial A B C (f: A -> res B) (g: B -> res C) la lc
      (MMAP: mmap (fun a => OK a @@@ f @@@ g) la = OK lc):
  exists lb, (<<MMAP0: mmap f la = OK lb>>) /\ (<<MMAP1: mmap g lb = OK lc>>).
Proof.
  ginduction la; ss; i; clarify.
  - esplits; eauto.
  - unfold bind in *. des_ifs_safe. exploit IHla; eauto. i. des.
    rewrite MMAP0. esplits; eauto. ss. unfold bind. rewrite MMAP1. des_ifs.
Qed.
