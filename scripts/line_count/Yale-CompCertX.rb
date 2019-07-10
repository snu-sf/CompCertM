puts "Count Yale-CompCertX"
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
             "backend/Deadcodeproof",
             "backend/Allocproof",
             "backend/Tunnelingproof",
             "backend/Linearizeproof",
             "backend/CleanupLabelsproof",
             "backend/Stackingproof",
             "x86/Asmgenproof",
             "backend/ValueAnalysis"]

PASS_PROOFXS = PASS_PROOFS.dup

PASS_PROOFS << "x86/SelectOpproof" << "x86/SelectLongproof" << "backend/SelectDivproof" << "backend/SplitLongproof" << "backend/RTLgenspec" << "backend/Inliningspec"
PASS_PROOFS << "x86/ConstpropOpproof" << "x86/CombineOpproof" << "common/Separation" << "x86/Asmgenproof1" << "backend/Asmgenproof0"
PASS_PROOFXS << "backend/SelectLongproof"

PASS_PROOFS.map!{|i| "compcert/" + i + ".v"}
PASS_PROOFXS.map!{|i| "compcertx/" + i + "X.v"}

PASS_PROOFS_ALL = PASS_PROOFS << PASS_PROOFXS

EXCLUDE_FOLDERS=["arm", "powerpc", "x86_32", "cparser"]

EXCLUDE_FOLDER=EXCLUDE_FOLDERS.inject(""){|sum, i| sum + "! -path \'*" + i + "\/*\' "}

EXCLUDE_FILES=["Cexec", "initializers", "initilizersproof", "Cstrategy", "Csem", "Csyntax", "SimplLocals", "SimplLocalsproof", "SimplExpr", "SimplExprproof", "Ctyping", "Unusedglob", "Unusedglobproof", "Unusedglobpproofimpl", "ValueDomainImplX"]

EXCLUDE_FILE=EXCLUDE_FILES.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}

puts
puts "<<<PASS_PROOFS>>>"
puts
system("coqwc #{PASS_PROOFS_ALL.join(" ")}")
puts

puts
puts "<<WHOLE>>"
puts
system("find compcert compcertx coqrel liblayers -type f " + EXCLUDE_FOLDER + "-name '*.v' " + EXCLUDE_FILE + " | xargs coqwc")

=begin
puts
puts "<<<PASS_PROOFSX>>>"
puts
system("coqwc #{PASS_PROOFXS.join(" ")}")
puts

puts
puts "<<Refactored>>"
puts
system("find compcert -type f ! -path '*arm/*' ! -path '*compcert/powerpc/*' ! -path '*compcert/x86_32/*' ! -path '*compcert/cparser/*' \
          ! -name '*compcert/cfrontend/Cexec.v' ! -name '*compcert/cfrontend/initializers.v' ! -name '*compcert/cfrontend/initilizersproof.v' ! -name '*compcert/cfrontend/Cstrategy.v' \
          ! -name '*compcert/cfrontend/Csem.v' ! -name '*compcert/cfrontend/Csyntax.v' ! -name '*compcert/cfrontend/SimplLocals.v' ! -name '*compcert/cfrontend/SimplLocalsproof.v' \
          ! -name '*compcert/cfrontend/SimplExpr.v' ! -name '*compcert/cfrontend/SimplExprproof.v' ! -name '*compcert/cfrontend/Ctyping.v' ! -name '*compcert/cfrontend/Cexecimpl.v' \
          ! -name '*compcert/backend/Unusedglob.v' ! -name '*compcert/backend/Unusedglobproof.v' \
          -name '*.v' ! -name 'Ctyping.v' | xargs coqwc")

puts
puts "<<Added>>"
puts
system("find compcertx coqrel liblayers -type f -name '*.v'| xargs coqwc")
=end

