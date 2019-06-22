Require Import UpperBound_A UpperBound_B LowerBound.
Require Import CompilerC.
Require Import CoqlibC.
Require Import BehaviorsC LinkingC EventsC MapsC ASTC CtypesC.


Lemma back_propagate_ub_behav
      beh0
      (INITUB: behavior_improves beh0 (Goes_wrong E0))
  :
    <<INITUB: beh0 = Goes_wrong E0>>
.
Proof.
  rr in INITUB. des; clarify; et.
  rr in INITUB0. des. unfold behavior_app in *. des_ifs. destruct t; ss.
Qed.

Lemma back_propagate_ub_program
      sem0 sem1
      (IMPR: improves sem0 sem1)
      (INITUB: program_behaves sem1 (Goes_wrong E0))
  :
    <<INITUB: program_behaves sem0 (Goes_wrong E0)>>
.
Proof.
  exploit IMPR; eauto. i; des.
  hexploit back_propagate_ub_behav; et. i ;des. clarify.
Qed.

Theorem separate_compilation_correct
        (srcs: list Csyntax.program) (tgts: list Asm.program) builtins src_link
        (TYPECHECKS: Forall (fun src => CsemC.typechecked builtins src) srcs)
        (TYPECHECKLINK: CsemC.typechecked builtins src_link)
        (LINK: link_list srcs = Some src_link)
        (MAIN: exists main_f,
            (<<INTERNAL: src_link.(prog_defmap) ! (src_link.(prog_main)) = Some (Gfun (Ctypes.Internal main_f))>>)
            /\
            (<<SIG: type_of_function main_f = Tfunction Ctypes.Tnil type_int32s cc_default>>))
        (TR: Errors.mmap transf_c_program srcs = Errors.OK tgts)
  :
    (<<INITUB: program_behaves (Csem.semantics src_link) (Goes_wrong E0)>>) \/
    exists tgt_link, <<LINK: link_list tgts = Some tgt_link>> /\
                     <<IMPROVES: improves (Csem.semantics src_link) (Asm.semantics tgt_link)>>
.
Proof.
  hexploit upperbound_b_correct; eauto. { des. esplits; et. } intro A.
  hexploit upperbound_a_correct; eauto. instantiate (1:= []). ss. intro B; des.
  hexploit compiler_correct; eauto.
  { do 2 instantiate (1:= []). ss. }
  instantiate (1:= []). ss. rewrite ! app_nil_r. intro C; des.
  hexploit (lower_bound_correct tgts); eauto. intro D.
  des.
  { left.
    hexploit back_propagate_ub_program; try apply C; et. intro CUB.
    hexploit back_propagate_ub_program; try apply CUB; et. intro BUB.
    hexploit back_propagate_ub_program; try apply BUB; et.
  }
  right. esplits; et. etrans; et. etrans; et. etrans; et.
Qed.
