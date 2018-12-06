Require Import CoqlibC.

Ltac minv H :=
  let X := fresh in
  set (X := H);
  inv X.

Ltac mset H1 H2 :=
  let X := fresh in
  set (X := H2);
  eapply H1 in X.

Ltac mset2 H1 H2 :=
  let X := fresh in
  set (X := H1);
  specialize (X H2).
