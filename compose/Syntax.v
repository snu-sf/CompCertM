From compcertr Require Import
     Maps
     AST
     Integers
     Values
     Memory
     Events
     Smallstep
     Globalenvs
     Linking.
Require Import CoqlibC.
From compcertr Require Import sflib.

Require Import ModSem Mod Skeleton LinkingC.

Definition program := list Mod.t.

