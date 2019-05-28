COMPCOMP=ARGV[0]

RTLS=["backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
      "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof"]
BACKENDS=["backend/Selectionproof", "backend/RTLgenproof", "backend/Tunnelingproof", "backend/Linearizeproof",
          "backend/CleanupLabelsproof", "backend/Debugvarproof"]
STACKNIG=["backend/Stackingproof"]
WHOLE=["x86/Asmgenproof", "cfrontend/Cminorgenproof", "cfrontend/Cshmgenproof", "cfrontend/SimplLocalsproof", "cfrontend/SimplExprproof"]
#NOTE: Cstrategy is omitted because it contains semantics/other proofs (bigstep) too

RTLS.map!{|i| i + if COMPCOMP then "C.v" else ".v" end}
BACKENDS.map!{|i| i + if COMPCOMP then "C.v" else ".v" end}
WHOLE.map!{|i| i + if COMPCOMP then "C.v" else ".v" end}

puts
puts "<<<RTLS>>>"
puts
system("tokei -f #{RTLS.join(" ")}")

puts
puts "<<<BACKENDS - STACKING>>>"
puts
system("tokei -f #{RTLS.join(" ")} #{BACKENDS.join(" ")}")

puts
puts "<<<WHOLE - STACKING>>>"
puts
system("tokei -f #{RTLS.join(" ")} #{BACKENDS.join(" ")} #{WHOLE.join(" ")}")
