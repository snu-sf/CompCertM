# CompCertM: CompCert with Lightweight Modular Verification and Multi-Language Linking
- Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, Chung-Kil Hur.  
[CompCertM: CompCert with Lightweight Modular Verification and Multi-Language Linking](https://sf.snu.ac.kr/compcertm/)

## Build
CompCertM is based on [CompCertR](https://github.com/snu-sf/CompCertR) which is a refactored version of CompCert. In order to build CompCertM, you need to build CompCertR first.
1) Clone https://github.com/snu-sf/CompCertR and follow the [installation instructions](https://github.com/snu-sf/CompCertR#installation-instructions).  

2) **Go to the CompCertR directory** and issue the following commands: <pre>
git clone https://github.com/snu-sf/CompCertM.git
cd CompCertM
make -j[N]</pre>


Or, you can download a Docker image in which `/home/coq/CompCertR/CompCertM` contains the build result:
```
docker pull minkiminki/popl20-93:v3.5
docker run -it minkiminki/popl20-93:v3.5
```

## Code Structure

For directories that existed in [CompCert](https://github.com/AbsInt/CompCert) (e.g. backend/), there are files that extends original CompCert's files.

New directories are roughly as follows.

- bound/: adequacy w.r.t. C and assembly (UpperBound_A.v, UpperBound_B.v, LowerBound.v)  
- compose/: interaction semantics and its properties  
- demo/: examples including Unreadglob, mutual-sum and utod
- selfsim/: self-simulation of Clight and Assembly  
- scripts/: scripts used for SLOC counting (_Table 1, 2, 3_)  
- proof/: our meta theory


We list a few important definitions/proofs from the paper.

**Semantics**  
- Interaction Semantics _(Section 5)_ : [compose/Sem.v](compose/Sem.v)  
- Module _(Page 18, Fig. 9)_: [compose/Mod.v](compose/Mod.v)  
- Module Semantics _(Page 18, Fig. 9)_: [compose/ModSem.v](compose/ModSem.v#L138)  

**Verification Techniques**  
- RUSC Theory _(Section 2.3)_: [proof/RUSC.v](proof/RUSC.v)  
- Mixed Simulation _(Section 2.4)_: [proof/Simulation.v](proof/Simulation.v) - [`xsim`](proof/Simulation.v#L486)  
- Parameter-MemRel _(Page 20, Fig. 10)_: [proof/SimMem.v](proof/SimMem.v)  
- Parameter-SymbRel _(Page 20, Fig. 10)_: [proof/SimSymb.v](proof/SimSymb.v)  
- Parameter-MemPred _(Page 20, Fig. 10)_: [proof/Sound.v](proof/Sound.v)  
(NOTE: The definition of a memory predicate is a little different from that in the paper. If we consider `(Sound.t * Memory.mem)` as a single component (= "t" in the paper), two definitions are equivalent.)  
- Parameterized Open Simulation _(Page 21, Fig. 11)_: [proof/SimModSem.v](proof/SimModSem.v)  
- Open Preservation _(Page 21, Fig. 11)_: [proof/Preservation.v](proof/Preservation.v) - [`local_preservation_standard`](proof/Preservation.v#L102)  
- Adequacy of Parameterized Open Simulation _(Page 22, Theorem 6.2)_: [proof/AdequacyLocal.v](proof/AdequacyLocal.v) - [`Theorem adequacy_local`](proof/AdequacyLocal.v#L705).  

**Correctness Theorems**  
- Compiler cocrrectness theorem (main result): [driver/CompilerC.v](driver/CompilerC.v)
  + Compositional Correctness I _(Page 23, Theorem 7.3)_: [`Theorem compiler_correct`](driver/CompilerC.v#L633)
  + Compositional Correctness II _(Page 24, Theorem 7.5)_: [`Theorem compiler_correct_full`](driver/CompilerC.v#L712)  
- Adequacy w.r.t. Assembly _(Page 24, Theorem 7.6)_: [bound/LowerBound.v](bound/LowerBound.v) - [`Theorem lower_bound_correct`](bound/LowerBound.v#L2395)
- Adequacy w.r.t. C _(Page 24, Theorem 7.7)_: [bound/UpperBound_B.v](bound/UpperBound_B.v) - [`Theorem upper_bound_b_correct`](bound/UpperBound_B.v#L1349)  

**Examples**  
- Unreadglob example _(Section 4.1)_: [demo/unreadglob](demo/unreadglob) ([demo directory in CompCertR](https://github.com/snu-sf/CompCertR/tree/v3.5_adapt/demo) also contains actual optimization and proof files)  
- mutual-sum example _(Section 4.2)_: [demo/mutrec](demo/mutrec)
  + a.c, b.asm _(Page 16, Fig. 7)_: [a.c](demo/mutrec/a.c), [b.s](demo/mutrec/b.s)
  + a.spec, b.spec _(Page 16, Fig. 7)_: [MutrecAspec.v](demo/mutrec/MutrecAspec.v), [MutrecBspec.v](demo/mutrec/MutrecBspec.v)
  + ab.spec _(Page 16, Fig. 7)_: [MutrecABspec.v](demo/mutrec/MutrecABspec.v)
  + refinement proof: [MutrecRefinement.v](demo/mutrec/MutrecRefinement.v) - [`Theorem Mutrec_correct`](demo/mutrec/MutrecRefinement.v#L144)
- utod example: [demo/utod](demo/utod)  

## Workflow

We first describe a step-by-step process of software verification using CompCert, and then describe such instructions for CompCertM.

(Running)
Write a C program, compile it to binary using CompCert executable (i.e. `ccomp`), and run it.

(Verifying)
- Translate each C module into Coq using `clightgen`.
- CompCert's C semantics formally defines behavior of your translated program.
- Verify properties about such behavior with your own technique. (e.g. a workflow using [VST](https://www.cs.princeton.edu/~appel/vc/Verif_sumarray.html))

For CompCertM, it is basically the same except we also support hand-written assembly modules.

(Running)
Write a program (you can use both C and *assembly*), compile C modules to binary using CompCert executable (i.e. `compcomp`), and run it. ([a.c](demo/mutrec/a.c), [b.s](demo/mutrec/b.s))

(Verifying)
- Translate each C module into Coq using `clightgen` as before. ([MutrecA.v](demo/mutrec/MutrecA.v))

  Unfortunately, as there is no such translation tool yet for assembly language, user should manually translate assembly modules into Coq. ([MutrecB.v](demo/mutrec/MutrecB.v))

  CompCert emits assembly module (defined in Coq) into actual `.s` file using `PrintAsm.ml`.

  You should make sure that printing your assembly (defined in Coq) using `PrintAsm.ml` yields a `.s` file that is equivalent to the one you have manually wrote.
- CompCertM's interaction semantics formally defines [behavior of your translated program](https://github.com/snu-sf/CompCertM/blob/v3.5/demo/mutrec/MutrecRefinement.v#L149). 
- Verify properties about such behavior with your own technique.

  As discussed in the paper, we advocate the use of RUSC theory in program verification, and we demonstrate this with [mutrec](demo/mutrec) example.
  
  Define open specs for each module. ([MutrecAspec.v](demo/mutrec/MutrecAspec.v), [MutrecBspec.v](demo/mutrec/MutrecBspec.v))
  
  Verify each module against its specification modularly. ([MutrecAproof.v](demo/mutrec/MutrecAproof.v), [MutrecBproof.v](demo/mutrec/MutrecBproof.v))
  
  Merge such open specs togather ([MutrecABproof.v](demo/mutrec/MutrecABproof.v))
  
  Prove self-simulations required for RUSC theory. (IdSim*.v)
  
  Get final result with RUSC theory. ([MutrecRefinement.v](demo/mutrec/MutrecRefinement.v))
