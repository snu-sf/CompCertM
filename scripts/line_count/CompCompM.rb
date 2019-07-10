puts "Count MultiComp"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cstrategyproof", "cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "x86/Asmgenproof", "backend/ValueAnalysis"]

PASS_PROOFS.map!{|i| i + ".v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")

puts
puts "<<WHOLE>>"
puts
system("find . -type f ! -path '*compcomp-linking/*' ! -path '*.normal_build/*' ! -path '*demo/*' ! -path '*arm/*' \
             ! -path '*powerpc/*' ! -path '*riscV/*' ! -path '*x86_32/*' ! -path '*cparser/*' -name '*.v' ! -name 'Ctyping.v' | xargs coqwc")
