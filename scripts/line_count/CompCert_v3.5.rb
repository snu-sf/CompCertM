puts "Count CompCert v3.5"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "x86/Asmgenproof", "backend/ValueAnalysis"]

PASS_PROOFS.map!{|i| i + ".v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")
puts
puts "add Cstrategy part for pass proof: 770"
puts
puts "NOTE: Cstrategy is counted by hand because it contains both semantics and pass proof."
puts

puts
puts "<<WHOLE>>"
puts
system("find . -type f ! -path '*arm/*' ! -path '*powerpc/*' ! -path '*riscV/*' ! -path '*x86_32/*' ! -path '*cparser/*' -name '*.v' ! -name 'Ctyping.v' | xargs coqwc")
