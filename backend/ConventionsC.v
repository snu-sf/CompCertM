Require Import CoqlibC.
Require Import ASTC.
Require Import LocationsC.
From compcertr Require Export
     Conventions1
     Conventions.

Global Instance main_args_some: main_args_ctx := { main_args := true }.
