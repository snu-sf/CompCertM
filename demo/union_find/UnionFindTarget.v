From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Local Open Scope Z_scope.

Definition _Node : ident := 2%positive.
Definition _find : ident := 61%positive.
Definition _main : ident := 69%positive.
Definition _makeSet : ident := 58%positive.
Definition _malloc : ident := 56%positive.
Definition _p : ident := 59%positive.
Definition _p0 : ident := 60%positive.
Definition _parent : ident := 3%positive.
Definition _rank : ident := 1%positive.
Definition _same_set : ident := 68%positive.
Definition _unionS : ident := 67%positive.
Definition _x : ident := 57%positive.
Definition _xRank : ident := 65%positive.
Definition _xRoot : ident := 63%positive.
Definition _y : ident := 62%positive.
Definition _yRank : ident := 66%positive.
Definition _yRoot : ident := 64%positive.
Definition _t'1 : ident := 70%positive.
Definition _t'2 : ident := 71%positive.

Definition f_makeSet := {|
  fn_return := (tptr (Tstruct _Node noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_x, (tptr (Tstruct _Node noattr))) :: (_t'1, (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _Node noattr) tulong) :: nil))
    (Sset _x
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _parent (tptr (Tstruct _Node noattr)))
      (Etempvar _x (tptr (Tstruct _Node noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
            (Tstruct _Node noattr)) _rank tuint)
        (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _x (tptr (Tstruct _Node noattr))))))))
|}.

Definition f_find := {|
  fn_return := (tptr (Tstruct _Node noattr));
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _Node noattr))) ::
               (_p0, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
        (Tstruct _Node noattr)) _parent (tptr (Tstruct _Node noattr))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _p (tptr (Tstruct _Node noattr)))
                   (Etempvar _x (tptr (Tstruct _Node noattr))) tint)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                          (tptr (Tstruct _Node noattr)) cc_default))
            ((Etempvar _p (tptr (Tstruct _Node noattr))) :: nil))
          (Sset _p0 (Etempvar _t'1 (tptr (Tstruct _Node noattr)))))
        (Ssequence
          (Sset _p (Etempvar _p0 (tptr (Tstruct _Node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _parent
              (tptr (Tstruct _Node noattr)))
            (Etempvar _p (tptr (Tstruct _Node noattr))))))
      Sskip)
    (Sreturn (Some (Etempvar _p (tptr (Tstruct _Node noattr)))))))
|}.

Definition f_unionS := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _Node noattr))) ::
                (_y, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_xRoot, (tptr (Tstruct _Node noattr))) ::
               (_yRoot, (tptr (Tstruct _Node noattr))) :: (_xRank, tuint) ::
               (_yRank, tuint) :: (_t'2, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                    (tptr (Tstruct _Node noattr)) cc_default))
      ((Etempvar _x (tptr (Tstruct _Node noattr))) :: nil))
    (Sset _xRoot (Etempvar _t'1 (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                      (tptr (Tstruct _Node noattr)) cc_default))
        ((Etempvar _y (tptr (Tstruct _Node noattr))) :: nil))
      (Sset _yRoot (Etempvar _t'2 (tptr (Tstruct _Node noattr)))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                     (Etempvar _yRoot (tptr (Tstruct _Node noattr))) tint)
        (Sreturn None)
        Sskip)
      (Ssequence
        (Sset _xRank
          (Efield
            (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
              (Tstruct _Node noattr)) _rank tuint))
        (Ssequence
          (Sset _yRank
            (Efield
              (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _rank tuint))
          (Sifthenelse (Ebinop Olt (Etempvar _xRank tuint)
                         (Etempvar _yRank tuint) tint)
            (Sassign
              (Efield
                (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _parent
                (tptr (Tstruct _Node noattr)))
              (Etempvar _yRoot (tptr (Tstruct _Node noattr))))
            (Sifthenelse (Ebinop Ogt (Etempvar _xRank tuint)
                           (Etempvar _yRank tuint) tint)
              (Sassign
                (Efield
                  (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                    (Tstruct _Node noattr)) _parent
                  (tptr (Tstruct _Node noattr)))
                (Etempvar _xRoot (tptr (Tstruct _Node noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _yRoot (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _parent
                    (tptr (Tstruct _Node noattr)))
                  (Etempvar _xRoot (tptr (Tstruct _Node noattr))))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _xRoot (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _rank tuint)
                  (Ebinop Oadd (Etempvar _xRank tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))))))))
|}.

Definition f_same_set := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_x, (tptr (Tstruct _Node noattr))) ::
                (_y, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                    (tptr (Tstruct _Node noattr)) cc_default))
      ((Etempvar _x (tptr (Tstruct _Node noattr))) :: nil))
    (Scall (Some _t'2)
      (Evar _find (Tfunction (Tcons (tptr (Tstruct _Node noattr)) Tnil)
                    (tptr (Tstruct _Node noattr)) cc_default))
      ((Etempvar _y (tptr (Tstruct _Node noattr))) :: nil)))
  (Sreturn (Some (Ebinop Oeq (Etempvar _t'1 (tptr (Tstruct _Node noattr)))
                   (Etempvar _t'2 (tptr (Tstruct _Node noattr))) tint))))
|}.

Definition composites : list composite_definition :=
(Composite _Node Struct
   ((_rank, tuint) :: (_parent, (tptr (Tstruct _Node noattr))) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_makeSet, Gfun(Internal f_makeSet)) :: (_find, Gfun(Internal f_find)) ::
 (_unionS, Gfun(Internal f_unionS)) ::
 (_same_set, Gfun(Internal f_same_set)) :: nil).

Definition public_idents : list ident :=
(_same_set :: _unionS :: _find :: _makeSet :: _malloc :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.

Require Import Mod ClightC.

Definition module: Mod.t := module2_mi prog (Some "UF"%string).
