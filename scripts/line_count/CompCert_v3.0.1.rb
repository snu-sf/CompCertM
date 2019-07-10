puts "Count Yale-CompCert, refactored"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cshmgenproof",
             "cfrontend/Cminorgenproof",
             "backend/Selectionproof",
             "backend/RTLgenproof",
             "backend/Tailcallproof",
             "backend/Inliningproof",
             "backend/Renumberproof",
             "backend/Constpropproof",
             "backend/CSEproof",
             "backend/ValueAnalysis",
             "backend/Deadcodeproof",
             "backend/Allocproof",
             "backend/Tunnelingproof",
             "backend/Linearizeproof",
             "backend/CleanupLabelsproof",
             "backend/Stackingproof",
             "x86/Asmgenproof"]

PASS_PROOFS.map!{|i| i + ".v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")
puts

puts
puts "<<WHOLE>>"
puts
system("find . -type f ! -path '*arm/*' ! -path '*powerpc/*' ! -path '*x86_32/*' ! -path '*cparser/*' \
          ! -name 'Cexec.v' ! -name 'initializers.v' ! -name 'initilizersproof.v' ! -name 'Cstrategy.v' \
          ! -name 'Csem.v' ! -name 'Csyntax.v' ! -name 'SimplLocals.v' ! -name '*SimplLocalsproof.v' \
          ! -name 'SimplExpr.v' ! -name 'SimplExprproof.v' ! -name 'Ctyping.v' ! -name 'Cexecimpl.v' \
          ! -name 'Unusedglob.v' ! -name 'Unusedglobproof.v' \
          -name '*.v' ! -name 'Ctyping.v' | xargs coqwc")
