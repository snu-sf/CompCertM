Require Import CoqlibC.
Require Import ASTC.
Require Import LocationsC.
Require Export Conventions1.
(* newly added *)
Require Export Conventions.

Global Instance main_args_some: main_args_ctx := { main_args := true }.