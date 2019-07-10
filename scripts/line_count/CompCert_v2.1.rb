puts "Count CompCert v2.1"
# system("find . -name '*.v'| xargs coqwc")
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof", "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof",
             "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof", "backend/CSEproof", "backend/Allocproof",
             "backend/Tunnelingproof", "backend/Linearizeproof", "backend/CleanupLabelsproof", "backend/Stackingproof", "ia32/Asmgenproof"]

PASS_PROOFS.map!{|i| i + ".v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")
puts

puts
puts "<<WHOLE>>"
puts
system("find . -type f ! -path './arm/*' ! -path './powerpc/*' \
          ! -name 'Cexec.v' ! -name 'initializers.v' ! -name 'initilizersproof.v' ! -name 'Cstrategy.v' \
          ! -name 'Csem.v' ! -name 'Csyntax.v' ! -name 'SimplLocals.v' ! -name 'SimplLocalsproof.v' \
          ! -name 'SimplExpr.v' ! -name 'SimplExprproof.v' ! -name 'Ctyping.v' \
          -name '*.v'| xargs coqwc")
