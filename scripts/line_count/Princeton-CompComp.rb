puts "Counting Princeton-compcomp"
puts
puts "<<Preprocessing>>"
puts
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cshmgenproof_comp",
             "cfrontend/Cminorgenproof_comp", "cfrontend/CminorgenproofSIM", "cfrontend/CminorgenproofRestructured",
             "backend/Selectionproof_comp",
             "backend/RTLgenproof_comp",
             "backend/Tailcallproof_comp",
             "backend/Inliningproof_comp",
             "backend/Renumberproof_comp",
             "backend/Constpropproof_comp",
             "backend/CSEproof_comp",
             "backend/Allocproof_comp",
             "backend/Tunnelingproof_comp",
             "backend/Linearizeproof_comp",
             "backend/CleanupLabelsproof_comp",
             "backend/Stackingproof_comp",
             "backend/Asmgenproof_comp"]

PASS_PROOFS.map!{|i| i + ".v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS.join(" ")}")
puts

UNUSED=["cfrontend/Cshmgenproof", "cfrontend/Clight", "cfrontend/Csharpminor",
        "cfrontend/Cminorgenproof", "backend/Cminor",
        "backend/Selectionproof", "backend/CminorSel", "backend/SelectLong", "backend/Selection",  "backend/SelectLongproof",
        "backend/RTLgenproof", "backend/RTL",
        "backend/Tailcallproof",
        "backend/Inliningproof",
        "backend/Renumberproof",
        "backend/Constpropproof",
        "backend/CSEproof",
        "backend/Allocproof", "backend/LTL",
        "backend/Tunnelingproof",
        "backend/Linearizeproof",
        "backend/CleanupLabelsproof", "backend/Linear",
        "backend/Stackingproof", "backend/Mach",
        "ia32/Asmgenproof", "ia32/Asm", "ia32/Asmgen", "backend/Asmgenproof0", "ia32/Asmgenproof1",
        "driver/Compiler", "driver/Complements"]

system("mkdir unused")
system("mkdir unused/cfrontend")
system("mkdir unused/backend")
system("mkdir unused/ia32")
system("mkdir unused/driver")
UNUSED.map!{|i| i + ".v"}
UNUSED.each{ |i| system("mv #{i} unused/#{i}")}

puts
puts "<<WHOLE>>"
puts
system("find . -type f ! -path '*arm/*' ! -path '*powerpc/*' ! -path '*unused/*' ! -path '*cpaser/*' \
          ! -path '*cfrontend/Cexec.v' ! -path '*cfrontend/initializers.v' ! -path '*cfrontend/initilizersproof.v' ! -path '*cfrontend/Cstrategy.v' \
          ! -path '*cfrontend/Csem.v' ! -path '*cfrontend/Csyntax.v' ! -path '*cfrontend/SimplLocals.v' ! -path '*cfrontend/SimplLocalsproof.v' \
          ! -path '*cfrontend/SimplExpr.v' ! -path '*cfrontend/SimplExprproof.v' \
          -name '*.v' ! -name 'Ctyping.v' | xargs coqwc")


puts
puts "<<UNUSED>>"
puts
system("find . -type f -path '*unused/*' -name '*.v'| xargs coqwc")

UNUSED.each{ |i| system("mv unused/#{i} #{i}")}
system("rm -rf unused")
