puts "Counting Princeton-compcomp"
puts
puts "<<Preprocessing>>"
puts
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cshmgenproof_comp",
             "cfrontend/Cminorgenproof_comp", "cfrontend/CminorgenproofSIM", "cfrontend/CminorgenproofRestructured",
             "backend/Selectionproof_comp", "ia32/SelectOpproof", "backend/SelectLongproof_comp", "backend/SelectDivproof",
             "backend/RTLgenproof_comp", "backend/RTLgenspec",
             "backend/Tailcallproof_comp",
             "backend/Inliningproof_comp", "backend/Inliningspec",
             "backend/Renumberproof_comp",
             "backend/Constpropproof_comp", "ia32/ConstpropOpproof",
             "backend/CSEproof_comp", "ia32/CombineOpproof",
             "backend/Allocproof_comp",
             "backend/Tunnelingproof_comp",
             "backend/Linearizeproof_comp",
             "backend/CleanupLabelsproof_comp",
             "backend/Stackingproof_comp",
             "backend/Asmgenproof_comp", "backend/Asmgenproof0_comp", "backend/Asmgenproof1_comp"]

PASS_PROOFS.map!{|i| i + ".v"}

EXCLUDE_FOLDERS=["arm", "powerpc", "unused"]

EXCLUDE_FOLDER=EXCLUDE_FOLDERS.inject(""){|sum, i| sum + "! -path \'*" + i + "\/*\' "}

EXCLUDE_FILES=["Cexec", "initializers", "initilizersproof", "Cstrategy", "Csem", "Csyntax", "SimplLocals", "SimplLocalsproof", "SimplExpr", "SimplExprproof", "Ctyping"]

EXCLUDE_FILE=EXCLUDE_FILES.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}

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
system("find . -type f " + EXCLUDE_FOLDER + "-name '*.v' " + EXCLUDE_FILE + " | xargs coqwc")

=begin
puts
puts "<<UNUSED>>"
puts
system("find unused -type f -name '*.v'| xargs coqwc")

UNUSED.each{ |i| system("mv unused/#{i} #{i}")}
system("rm -rf unused")
=end
