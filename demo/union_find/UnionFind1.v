Require Import CoqlibC Maps.
Require Import ASTC Integers ValuesC EventsC MemoryC Globalenvs.
Require Import Op Registers.
Require Import sflib.
Require Import SmallstepC.
Require Export Simulation.
Require Import Skeleton Mod ModSem.
Require ClightC.
Require Import UnionFindHeader.
Require Import UnionFind0.
Require Import SIRStack.
(* Require Import Clightdefs. *)

Set Implicit Arguments.


(* Let f_new_alt (oh0: owned_heap) (m0: mem) (vs0: list val): *)
(*   itree (E owned_heap) (owned_heap * (mem * val)) := *)
(*   unwrapU (do _ <- parg_new vs0 ; *)
(*            do (m1, b) <- malloc m0 (Ptrofs.repr 12) ; *)
(*            let x  := Vptr b Ptrofs.zero in *)
(*            do m2 <- Mem.store Mptr   m1 b 4 x ; *)
(*            do m3 <- Mem.store Mint32 m2 b 0 (Vint Int.zero) ; *)
(*            Some (oh0, (m3, x))) >>= ret *)
(* . *)

(*** I will prefer below definition because it is more canonical; we can control unwarpU/unwrapN ***)
Definition f_new (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  tau;;
  _ <- unwrapU (parg_new vs0) ;;
  '(m1, b) <- unwrapU (malloc m0 (Ptrofs.repr 16)) ;;
  let x  := Vptr b Ptrofs.zero in
  m2 <- unwrapU (Mem.store Mptr m1 b 8 x) ;;
  m3 <- unwrapU (Mem.store Mint32 m2 b 0 (Vint Int.zero)) ;;
  tau;;
  Ret (oh0, (m3, x))
.

(* Goal f_new_alt = f_new. *)
(*   apply func_ext3. ii. unfold f_new_alt, f_new. *)
(*   irw. unfold unwrapU. unfold o_bind2, curry2. uo. unfold triggerUB. *)
(*   repeat (des_ifs; ss; irw); try (by grind). *)
(* Qed. *)

Definition f_find (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  x <- unwrapU (parg_find vs0) ;;
  p <- unwrapU (Mem.load Mptr m0 x 8) ;;
  cond <- unwrapU (Val.cmplu_bool (Mem.valid_pointer m0) Cne p (Vptr x Ptrofs.zero)) ;;
  tau;;
  myif (cond)
    (tau;; '(oh1, (m1, p0)) <- trigger (ICall _find oh0 m0 [p]) ;;
      m2 <- unwrapU (Mem.store Mptr m1 x 8 p0) ;;
      tau;;
      Ret (oh1, (m2, p0)))
    (tau;; Ret (oh0, (m0, p)))
.

Definition unint (v: val): option int :=
  match v with
  | Vint i => Some i
  | _ => None
  end
.

Definition f_union (oh0: owned_heap) (m0: mem) (vs0: list val):
  itree (E owned_heap) (owned_heap * (mem * val)) :=
  '(x, y) <- unwrapU (parg_union vs0) ;;
  tau;;
  '(oh1, (m1, xRoot)) <- trigger (ICall _find oh0 m0 [Vptr x Ptrofs.zero]) ;; tau;;
  '(oh2, (m2, yRoot)) <- trigger (ICall _find oh1 m1 [Vptr y Ptrofs.zero]) ;;
  cond <- unwrapU (Val.cmplu_bool (Mem.valid_pointer m2) Ceq xRoot yRoot) ;;
  tau;;
  (myif cond
        (tau;; Ret (oh2, (m2, Vundef)))
        (`xRootB: block <- unwrapU (unblock xRoot) ;;
         `yRootB: block <- unwrapU (unblock yRoot) ;;
         (* `xRank: int <- unwrapU (do _xRank <- Mem.load Mint32 m2 xRootB 0 ; (unint _xRank)) ;; *)
         (* `yRank: int <- unwrapU (do _yRank <- Mem.load Mint32 m2 yRootB 0 ; (unint _yRank)) ;; *)
         `_xRank: val <- unwrapU (Mem.load Mint32 m2 xRootB 0) ;;
         `_yRank: val <- unwrapU (Mem.load Mint32 m2 yRootB 0) ;;
         `xRank: int <- unwrapU (unint _xRank) ;;
         `yRank: int <- unwrapU (unint _yRank) ;;
         myif (Int.ltu xRank yRank)
              (m3 <- unwrapU (Mem.store Mptr m2 xRootB 8 yRoot) ;;
              tau;; Ret (oh2, (m3, Vundef)))
              (myif (Int.ltu yRank xRank)
                    (m3 <- unwrapU (Mem.store Mptr m2 yRootB 8 xRoot) ;;
                     tau;; Ret (oh2, (m3, Vundef)))
                    (m3 <- unwrapU (Mem.store Mptr m2 yRootB 8 xRoot) ;;
                     m4 <- unwrapU (Mem.store Mint32 m3 xRootB 0 (Vint (Int.add xRank Int.one))) ;;
                     tau;; Ret (oh2, (m4, Vundef)))
              )
        )
  )
.
(*** TODO: Add notation for myif (proper align with automatic align) ***)


(*** TODO: Add infix notation for Maps.add ***)
Definition prog: program owned_heap :=
  (Maps.add _union f_union (Maps.add _find f_find (Maps.add _new f_new Maps.empty))).

Program Definition module: SMod.t _ := SMod.mk (UnionFind0.module) prog "UF"%string initial_owned_heap _.
