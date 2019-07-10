puts "Count MultiComp"
puts

puts
puts "<<Adq. w.r.t. C>>"
puts
system("coqwc bound/UpperBound_AExtra.v bound/UpperBound_A.v bound/UpperBound_B.v")

puts
puts "<<Unreadglob-PASS PROOF>>"
puts
system("coqwc demo/unreadglob/UnreadglobproofC.v")

puts
puts "<<Unreadglob-rest>>"
puts
system("find demo/unreadglob ! -name 'UnreadglobproofC.v' -name '*.v' | xargs coqwc")

puts
puts "<<Unreadglob-whole>>"
puts
system("coqwc demo/unreadglob/*.v")

puts
puts "<<Mutrec-PASS PROOF>>"
puts
system("coqwc demo/mutrec/MutrecAproof.v demo/mutrec/MutrecBproof.v demo/mutrec/MutrecABproof.v")

puts
puts "<<Mutrec-rest>>"
puts
system("find demo/mutrec ! -name 'MutrecAproof.v' ! -name 'MutrecBproof.v' ! -name 'MutrecABproof.v' -name '*.v' | xargs coqwc")

puts
puts "<<Mutrec-whole>>"
puts
system("coqwc demo/mutrec/*.v")

puts
puts "<<Utod>>"
puts
system("coqwc demo/utod/*.v")

PASS_PROOFS=["cfrontend/Cstrategyproof", "cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "backend/Separation", "x86/Asmgenproof"]

PASS_PROOFS.map!{|i| i + "C.v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")

puts
puts "<<Interation Semantics>>"
puts
system("coqwc compose/*.v")

puts
puts "<<Language Semantics>>"
puts
system("coqwc cfrontend/Csem.v cfrontend/CstrategyC.v cfrontend/ClightC.v cfrontend/CsharpminorC.v \
              backend/CminorC.v backend/CminorSelC.v backend/RTLC.v backend/LTLC.v backend/LinearC.v backend/MachC.v x86/AsmC.v")

puts
puts "<<Our Meta Theory>>"
puts
system("find proof -name '*.v' ! -name 'Simulation.v' | xargs coqwc")

puts
puts "<<Mixed Simulation>>"
puts
system("coqwc proof/Simulation.v")

puts
puts "<<Adq. w.r.t. Asm>>"
puts
system("coqwc bound/LinkingC2.v bound/LowerBoundExtra.v bound/LowerBound.v")

puts
puts "CompCert Meta Theory: the Rest"
puts

puts
puts "<<WHOLE>>"
puts
system("find . ! -path '*demo/*' -name '*.v' ! -name 'UpperBound_AExtra.v' ! -name 'UpperBound_A.v' ! -name 'UpperBound_B.v' | xargs coqwc")

