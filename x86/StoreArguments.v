Require Import CoqlibC.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import ValuesC.
Require Import MemoryC.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import LocationsC.
Require Import Conventions.
Require Stacklayout.
(** newly added **)
Require Import Mach.

Definition only_args (m: mem) (blk: block) (lo: ptrofs) (locs: list loc) :=
  forall ofs,
    (<<UNDEF: ZMap.get ofs (Mem.mem_contents m) !! blk = Undef >>) \/
    (<<INARGS: exists ofs0 ty v,
        (<<IN: In (S Outgoing ofs0 ty) locs>>) /\
        (<<RANGE: 4 * ofs0 <= ofs < 4 * ofs0 + size_chunk (chunk_of_type ty)>>) /\
        (<<LOAD: Mem.loadv
                   (chunk_of_type ty)
                   m
                   (Val.offset_ptr (Vptr blk lo) (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs0)))
                 = Some v>>) /\
        (<<VDEF: v <> Vundef>>)>>).

Inductive store_arguments (m0: mem) (rs: Mach.regset) (vs: list val) (sg: signature) (m2: mem): Prop :=
| store_arguments_intro
    m1 blk
    (ALC: Mem.alloc m0 0 (4 * size_arguments sg) = (m1, blk))
    (VALS: extcall_arguments rs m2 (Vptr blk Ptrofs.zero) sg vs)
    (ONLYARGS: only_args m2 blk Ptrofs.zero (regs_of_rpairs (loc_arguments sg)))
    (UNCH: Mem.unchanged_on (fun b ofs => if eq_block b blk then ~ (0 <= ofs < 4 * size_arguments sg) else True) m1 m2)
    (NB: m1.(Mem.nextblock) = m2.(Mem.nextblock))
    (PERM: Mem.range_perm m2 blk 0 (4 * size_arguments sg) Cur Freeable).
