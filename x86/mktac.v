Require Import CoqlibC.

Ltac cinv H :=
  let X := fresh in
  set (X := H);
  inv X.

Ltac cset H1 H2 :=
  let X := fresh in
  set (X := H2);
  eapply H1 in X.

Ltac cset2 H1 H2 :=
  let X := fresh in
  set (X := H1);
  specialize (X H2).
