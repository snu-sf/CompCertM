Require Import CoqlibC.
Require Import AST Memory Separation.
Require Import BoundsC.

Local Open Scope sep_scope.
(** newly added **)
Require Export Stacklayout.



(* fe_ofs_arg <- spofs *)
Definition make_env_ofs (fe_ofs_arg: Z) (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
  let olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w in  (* back link *)
  let ocs := olink + w in                           (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let oretaddr := align (ostkdata + b.(bound_stack_data)) w in (* return address *)
  let sz := oretaddr + w in (* total size *)
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

Lemma make_env_ofs_zero
      b
  :
    <<EQ: make_env b = make_env_ofs 0 b>>
.
Proof.
  red. unfold make_env, make_env_ofs, fe_ofs_arg. cbn. f_equal.
Qed.

Lemma frame_env_separated:
  forall b sp fe_ofs_arg m P
  (OFSARG: 0 <= fe_ofs_arg),
  let fe := make_env_ofs fe_ofs_arg b in
  m |= range sp fe_ofs_arg (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
  m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
       ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
       ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr)
       ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
       ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
       ** P.
Proof.
Local Opaque Z.add Z.mul sepconj range.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg + 4 * b.(bound_outgoing)) by omega.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= olink) by (apply align_le; omega).
  assert (olink + w <= ocs) by (unfold ocs; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
(* Reorder as:
     outgoing
     back link
     callee-save
     local
     retaddr *)
  rewrite sep_swap12.
  rewrite sep_swap23.
  rewrite sep_swap45.
  rewrite sep_swap34.
(* Apply range_split and range_split2 repeatedly *)
  apply range_split_2. fold olink. omega. omega.
  apply range_split. omega.
  apply range_split_2. fold ol. omega. omega.
  apply range_drop_right with ostkdata. omega.
  rewrite sep_swap.
  apply range_drop_left with (ostkdata + bound_stack_data b). omega.
  rewrite sep_swap.
  exact H.
Qed.

Lemma frame_env_range:
  forall fe_ofs_arg b
  (OFSARG: 0 <= fe_ofs_arg),
  let fe := make_env_ofs fe_ofs_arg b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= fe_ofs_arg + 4 * b.(bound_outgoing)) by omega.
  assert (fe_ofs_arg + 4 * b.(bound_outgoing) <= olink) by (apply align_le; omega).
  assert (olink + w <= ocs) by (unfold ocs; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr).
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
  split. omega. omega.
Qed.

Lemma frame_env_aligned:
  forall b fe_ofs_arg
  (OFSARG: (8 | fe_ofs_arg)),
  let fe := make_env_ofs fe_ofs_arg b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (align_chunk Mptr | fe_ofs_link fe)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (fe_ofs_arg + 4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. assumption.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  apply align_divides; omega.
Qed.
