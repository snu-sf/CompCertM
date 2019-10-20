Require Import CoqlibC.
Require Import MemoryC.
Require Import Values.
Require Import Maps.
Require Import Events.
Require Import Globalenvs.
Require Import sflib.
Require Import RelationClasses.
Require Import FSets.
Require Import Ordered.
Require Import AST.
Require Import Integers.

Require Import ModSem.
Require Import Skeleton.
Require Import System.

Set Implicit Arguments.






Module Sound.

  Class class :=
  {
    t: Type;

    mle: t -> Memory.mem -> Memory.mem -> Prop;
    mle_PreOrder su0 :> PreOrder (mle su0);

    hle: t -> t -> Prop;
    hle_PreOrder :> PreOrder hle;
    lepriv: t -> t -> Prop;
    lepriv_PreOrder :> PreOrder lepriv;
    wf: t -> Prop;

    hle_lepriv: forall su0 su1
        (HLE: hle su0 su1)
        (WF: wf su0),
        <<LE: lepriv su0 su1>>;

    hle_mle: forall m0 m1 su0 su1
        (MLE: mle su1 m0 m1)
        (HLE: hle su0 su1)
        (WF: wf su0),
        <<MLE: mle su0 m0 m1>>;

    val: t -> Values.val -> Prop;
    vals: t -> list Values.val -> Prop := fun su vs => Forall su.(val) vs;
    mem: t -> mem -> Prop;

    regset: t -> Asm.regset -> Prop := fun su rs => forall pr, su.(val) (rs pr);
    args: t -> Args.t -> Prop :=
      fun su args =>
        match args with
        | Args.Cstyle fptr vs m =>
          (<<VAL: val su fptr>>) /\
          (<<VALS: vals su vs>>) /\
          (<<MEM: mem su m>>) /\
          (<<WF: wf su>>)
        | Args.Asmstyle rs m =>
          (<<REGSET: regset su rs>>) /\
          (<<MEM: mem su m>>) /\
          (<<WF: wf su>>)
        end
    ;
    retv: t -> Retv.t -> Prop :=
      fun su retv =>
        match retv with
        | Retv.Cstyle v m =>
          (<<VAL: val su v>>) /\
          (<<MEM: mem su m>>) /\
          (<<WF: wf su>>)
        | Retv.Asmstyle rs m =>
          (<<REGSET: regset su rs>>) /\
          (<<MEM: mem su m>>) /\
          (<<WF: wf su>>)
        end
    ;

    hle_val: forall su0 su1 v
        (VAL: val su0 v)
        (HLE: hle su0 su1),
        <<VAL: val su1 v>>;

    skenv: t -> Memory.mem -> SkEnv.t -> Prop;
    init_spec: forall
        sk_link skenv_link m_init
        (MEM: Sk.load_mem sk_link = Some m_init)
        (SKE: Sk.load_skenv sk_link = skenv_link),
        exists su_init,
          (<<SUARGS: su_init.(args) (Args.mk (Genv.symbol_address skenv_link (prog_main sk_link) Ptrofs.zero) [] m_init)>>) /\
          (<<SUSKE: su_init.(skenv) m_init skenv_link>>);

    skenv_lepriv: forall m0 su0 su1 ske
        (SKE: su0.(skenv) m0 ske)
        (LE: lepriv su0 su1),
        <<SKE: su1.(skenv) m0 ske>>;

    skenv_mle: forall m0 m1 su0 ske
        (SKE: su0.(skenv) m0 ske)
        (MLE: su0.(mle) m0 m1),
        <<SKE: su0.(skenv) m1 ske>>;

    skenv_project: forall su m0 skenv_link sk skenv0
        (WF: SkEnv.wf skenv_link)
        (WFM: SkEnv.wf_mem skenv_link sk m0)
        (SKE: su.(skenv) m0 skenv_link)
        (LE: SkEnv.project_spec skenv_link sk skenv0)
        (INCL: SkEnv.includes skenv_link sk),
        <<SKE: su.(skenv) m0 skenv0>>;

    system_skenv: forall su m0 skenv_link,
        su.(skenv) m0 skenv_link <-> su.(skenv) m0 skenv_link.(System.skenv);

    system_axiom: forall
        ef skenv0 su0 args0
        tr v_ret m_ret
        (CSTYLE: Args.is_cstyle args0)
        (ARGS: su0.(args) args0)
        (SKE: skenv su0 args0.(Args.m) skenv0)
        (EXT: (external_call ef) skenv0 args0.(Args.vs) args0.(Args.m) tr v_ret m_ret),
        exists su1, <<LE: hle su0 su1>> /\ <<RETV: su1.(retv) (Retv.mk v_ret m_ret)>> /\ <<MLE: su0.(mle) args0.(Args.m) m_ret>>;
  }.

  Section SOUND.
  Context {SU: class}.

  Lemma skenv_hle: forall m0 su0 su1 ske
      (WF: Sound.wf su0)
      (SKE: su0.(skenv) m0 ske)
      (MLE: hle su0 su1),
      <<SKE: su1.(skenv) m0 ske>>.
  Proof.
    i. eapply skenv_lepriv; eauto. eapply hle_lepriv; eauto.
  Qed.

  End SOUND.

End Sound.
