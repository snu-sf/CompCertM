puts "Count MultiComp"
puts

puts
puts "<<LowerBound>>"
puts
system("coqwc bound/LinkingC2.v bound/LowerBoundExtra.v bound/LowerBound.v")

puts
puts "<<UpperBound>>"
puts
system("coqwc bound/UpperBound_AExtra.v bound/UpperBound_A.v bound/UpperBound_B.v")

puts
puts "<<Unreadglob-IdSim>>"
puts
system("coqwc demo/unreadglob/IdSimAsmDropInv.v demo/unreadglob/IdSimAsmIdInv.v demo/unreadglob/IdSimClightDropInv.v demo/unreadglob/IdSimClightIdInv.v demo/unreadglob/IdSimInvExtra.v")

puts
puts "<<Unreadglob-rest>>"
puts
system("coqwc demo/unreadglob/SimSymbDropInv.v demo/unreadglob/UnreadglobproofC.v")

puts
puts "<<Demo>>"
puts
system("find . -type f -path './demo/*' ! -path './demo/unreadglob/*' -name '*.v' | xargs coqwc")

PASS_PROOFS=["cfrontend/Cstrategy.v", "cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "x86/Asmgenproof"]

PASS_PROOFS.map!{|i| i + "C.v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")

puts
puts "<<Interation Semantics>>"
puts
system("coqwc compose/Sem.v compose/Mod.v compose/ModSem.v compose/System.v compose/Skeleton.v compose/Syntax.v")

puts
puts "<<Language Semantics>>"
puts
system("coqwc cfrontend/CstrategyC,v cfrontend/ClightC.v cfrontend/CsharminorC.v backend/CminorC.v backend/CminorSelC.v backend/RTLC.v backend/LTLC.v backend/LinearC.v backend/MachC.v x86/AsmC.v")

puts
puts "<<Our Meta Theory>>"
puts
system("coqwc compose/JunkBlock.v compose/ModSemProps.v compose/SimSymbDrop.v compose/SimSymb.v proof/*.v")

puts
puts "<<Mixed Simulation>>"
puts
system("coqwc proof/Simulation.v")

puts
puts "CompCert Meta Theory: the Rest"
puts

puts
puts "<<WHOLE>>"
puts
system("find . -name *.v | xargs coqwc")

