Require Import UpperBound_A UpperBound_B LowerBound.
Require Import CompilerC.
Require Import CoqlibC.
Require Import BehaviorsC LinkingC EventsC MapsC ASTC CtypesC.


Theorem separate_compilation_correct
        (srcs: list Csyntax.program) (tgts: list Asm.program) builtins src_link
        (TYPECHECKS: Forall (fun src => CsemC.typechecked builtins src) srcs)
        (TYPECHECKLINK: CsemC.typechecked builtins src_link)
        (LINK: link_list srcs = Some src_link)
        (MAIN: exists main_f,
            (<<INTERNAL: (prog_defmap src_link) ! (src_link.(prog_main)) = Some (Gfun (Ctypes.Internal main_f))>>) /\
            (<<SIG: type_of_function main_f = Tfunction Ctypes.Tnil type_int32s cc_default>>))
        (TR: Errors.mmap transf_c_program srcs = Errors.OK tgts):
    (<<INITUB: program_behaves (Csem.semantics src_link) (Goes_wrong E0)>>) \/
    exists tgt_link, <<LINK: link_list tgts = Some tgt_link>> /\
                     <<IMPROVES: improves (Csem.semantics src_link) (Asm.semantics tgt_link)>>.
Proof.
  hexploit upperbound_b_correct; eauto. intro A.
  hexploit upperbound_a_correct; eauto. instantiate (1:= []). ss. intro B; des.
  hexploit compiler_correct_full; eauto.
  { do 2 instantiate (1:= []). ss. }
  instantiate (1:= []). ss. rewrite ! app_nil_r. intro C; des.
  hexploit (lower_bound_correct tgts); eauto. intro D. des.
  { left.
    hexploit back_propagate_ub_program; try apply C; et. intro CUB.
    hexploit back_propagate_ub_program; try apply CUB; et. intro BUB.
    hexploit back_propagate_ub_program; try apply BUB; et.
  }
  right. esplits; et. etrans; et. etrans; et. etrans; et.
Qed.
