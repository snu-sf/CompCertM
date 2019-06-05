Require Import Sem SimProg Skeleton Mod ModSem SimMod SimModSem SimSymb SimMem Sound SimSymb.
Require Import CsemC.
Require SimMemId SimMemExt SimMemInj.
Require SoundTop UnreachC.
Require SimSymbId SimSymbDrop.
Require Import CoqlibC.
Require Import ValuesC.
Require Import LinkingC.
Require Import MapsC.
Require Import AxiomsC.
Require Import Ord.
Require Import MemoryC.
Require Import SmallstepC.
Require Import Events.
Require Import Preservation.
Require Import Integers.
Require Import LocationsC Conventions.

Require Import AsmregsC.
Require Import MatchSimModSem.
Require Import IdSimExtra.

Set Implicit Arguments.

Local Opaque Z.mul Z.add Z.sub Z.div.



Lemma ccc_id
      (ccc: Csyntax.program)
      (WF: Sk.wf ccc.(module))
  :
    exists mp,
      (<<SIM: @ModPair.sim SimMemId.SimMemId SimMemId.SimSymbId SoundTop.Top mp>>)
      /\ (<<SRC: mp.(ModPair.src) = ccc.(module)>>)
      /\ (<<TGT: mp.(ModPair.tgt) = ccc.(module)>>)
.
Proof.
  eexists (ModPair.mk _ _ _); s.
  esplits; eauto. instantiate (1:=tt).
  econs; ss; i.
  rewrite SIMSKENVLINK in *.
  eapply match_states_sim; ss.
  - apply unit_ord_wf.
  - eapply SoundTop.sound_state_local_preservation.
  - instantiate (1:= fun sm_arg _ st_src st_tgt sm0 =>
                       (<<EQ: st_src = st_tgt>>) /\
                       (<<MWF: sm0.(SimMemId.src) = sm0.(SimMemId.tgt)>>) /\
                       (<<STMWF: match st_src.(CsemC.get_mem) with
                                 | Some m => sm0.(SimMemId.src) = m
                                 | _ => True
                                 end>>)).
    ss. i.
    destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
    clear SAFESRC. dup INITTGT. inv INITTGT. ss.
    eexists. eexists (SimMemId.mk tgt tgt). esplits; eauto; ss.
  - ii. destruct args_src, args_tgt, sm_arg. inv SIMARGS; ss; clarify.
  - ii. ss. des. clarify.
  - i. ss. des. clarify. esplits; eauto.
    + inv CALLSRC. ss. clarify.
    + instantiate (1:=top4). ss.
  - i. clear HISTORY. ss. destruct sm_ret, retv_src, retv_tgt.
    inv SIMRET. des. ss. clarify. eexists (SimMemId.mk _ _). esplits; eauto.
    inv AFTERSRC. ss.
  - i. ss. des. destruct sm0. ss. clarify. eexists (SimMemId.mk tgt tgt).
    esplits; eauto.
    inv FINALSRC. ss.
  - right. ii. des. destruct sm0. ss. clarify. esplits; eauto.
    + i. exploit H; ss.
      * econs 1.
      * i. des; clarify. econs; eauto.
    + i. exists tt, st_tgt1.
      exists (match st_tgt1.(CsemC.get_mem) with
              | Some m => SimMemId.mk m m
              | _ => SimMemId.mk tgt tgt
              end).
      esplits; eauto.
      * left. econs; eauto; [econs 1|]. symmetry. apply E0_right.
      * des_ifs.
      * des_ifs.
Qed.
