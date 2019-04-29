Require Import Setoid Program.Basics.
Require Import CoqlibC Decidableplus.
Require Import AST Integers Values MemoryC Events Globalenvs.
(** newly added **)
Require Import AxiomsC.
Require Export Separation.

Local Open Scope sep_scope.


Ltac sep_split := econs; [|split]; swap 2 3.

Global Program Instance disjoint_footprint_sym: Symmetric disjoint_footprint.
Next Obligation. ii. eapply H; eauto. Qed.


Section INJ.
