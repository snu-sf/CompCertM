Require Import CoqlibC.
Require Import MemoryC.
Require Import RelationClasses.
Require Import FSets.
From compcertr Require Import
     Values
     Maps
     Events
     Globalenvs
     sflib
     Ordered
     AST
     Integers.

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
    vals: t -> list Values.val -> Prop := fun su vs => Forall (val su) vs;
    mem: t -> mem -> Prop;

    regset: t -> Asm.regset -> Prop := fun su rs => forall pr, (val su) (rs pr);
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
          (<<SUARGS: (args su_init) (Args.mk (Genv.symbol_address skenv_link (prog_main sk_link) Ptrofs.zero) [] m_init)>>) /\
          (<<SUSKE: (skenv su_init) m_init skenv_link>>);

    skenv_lepriv: forall m0 su0 su1 ske
        (SKE: (skenv su0) m0 ske)
        (LE: lepriv su0 su1),
        <<SKE: (skenv su1) m0 ske>>;

    skenv_mle: forall m0 m1 su0 ske
        (SKE: (skenv su0) m0 ske)
        (MLE: (mle su0) m0 m1),
        <<SKE: (skenv su0) m1 ske>>;

    skenv_project: forall su m0 skenv_link sk skenv0
        (WF: SkEnv.wf skenv_link)
        (WFM: SkEnv.wf_mem skenv_link sk m0)
        (SKE: (skenv su) m0 skenv_link)
        (LE: SkEnv.project_spec skenv_link sk skenv0)
        (INCL: SkEnv.includes skenv_link sk),
        <<SKE: (skenv su) m0 skenv0>>;

    system_skenv: forall su m0 skenv_link
        (SKELINK: (skenv su) m0 skenv_link),
        <<SKE: (skenv su) m0 (System.skenv skenv_link)>>;

    system_axiom: forall
        ef skenv0 su0 args0
        tr v_ret m_ret
        (CSTYLE: Args.is_cstyle args0)
        (ARGS: (args su0) args0)
        (SKE: skenv su0 (Args.m args0) skenv0)
        (EXT: (external_call ef) skenv0 (Args.vs args0) (Args.m args0) tr v_ret m_ret),
        exists su1, <<LE: hle su0 su1>> /\ <<RETV: (retv su1) (Retv.mk v_ret m_ret)>> /\ <<MLE: (mle su0) (Args.m args0) m_ret>>;
  }.

  Section SOUND.
  Context {SU: class}.

  Lemma skenv_hle: forall m0 su0 su1 ske
      (WF: Sound.wf su0)
      (SKE: (skenv su0) m0 ske)
      (MLE: hle su0 su1),
      <<SKE: (skenv su1) m0 ske>>.
  Proof.
    i. eapply skenv_lepriv; eauto. eapply hle_lepriv; eauto.
  Qed.

  End SOUND.

End Sound.
