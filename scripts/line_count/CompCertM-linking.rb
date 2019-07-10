def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  result=result[0].to_i + result[1].to_i
  puts
  puts "RESULTS: #{result}"
  return result
end

puts "Count MultiComp"
puts

UNREADGLOBPROOFS=["UnreadglobproofC"]
UNREADGLOBPROOFS

PASS_PROOFS=["cfrontend/Cstrategyproof", "cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "backend/Separation", "x86/Asmgenproof"]

PASS_PROOFS.map!{|i| i + "C.v"}

puts
puts "<<<PASS_PROOFS>>>"
puts
print_result(`coqwc #{PASS_PROOFS.join(" ")}`)

puts
puts "<<Unreadglob-PASS PROOF>>"
puts
print_result(`coqwc #{UNREADGLOBPROOFS.map{|i| "demo/unreadglob/" + i + ".v"}.join(" ")}`)

puts
puts "<<Unreadglob-rest>>"
puts
print_result(`find demo/mutrec #{UNREADGLOBPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts
puts "<<Unreadglob-whole>>"
puts
print_result(`coqwc demo/unreadglob/*.v`)

MUTRECPROOFS=["MutrecAproof", "MutrecBproof", "MutrecABproof"]

puts
puts "<<Mutrec-PASS PROOF>>"
puts
print_result(`coqwc #{MUTRECPROOFS.map{|i| "demo/mutrec/" + i + ".v"}.join(" ")}`)

puts
puts "<<Mutrec-rest>>"
puts
print_result(`find demo/mutrec #{MUTRECPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts
puts "<<Mutrec-whole>>"
puts
print_result(`coqwc demo/mutrec/*.v`)

UTODPROOFS=["DemoSpecProof"]

puts
puts "<<Utod-PASS PROOF>>"
puts
print_result(`coqwc #{UTODPROOFS.map{|i| "demo/utod/" + i + ".v"}.join(" ")}`)

puts
puts "<<Utod-rest>>"
puts
print_result(`find demo/utod #{UTODPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts
puts "<<Utod-whole>>"
puts
print_result(`coqwc demo/utod/*.v`)

puts
puts "<<Adq. w.r.t. C>>"
puts
print_result(`coqwc bound/UpperBound_AExtra.v bound/UpperBound_A.v bound/UpperBound_B.v`)

puts
puts "<<Interation Semantics>>"
puts
print_result(`coqwc compose/*.v`)

puts
puts "<<Language Semantics>>"
puts
print_result(`coqwc cfrontend/CsemC.v cfrontend/CstrategyC.v cfrontend/ClightC.v cfrontend/CsharpminorC.v \
                         backend/CminorC.v backend/CminorSelC.v backend/RTLC.v backend/LTLC.v backend/LinearC.v backend/MachC.v x86/AsmC.v`)

puts
puts "<<Self Simulation>>"
puts
print_result(`coqwc selfsim/*.v`)

puts
puts "<<CompCert Meta: the Rest>>"
puts

puts
puts "<<CompCertM meta>>"
puts
print_result(`find proof -name '*.v' ! -name 'Simulation.v' | xargs coqwc`)

puts
puts "<<Mixed Simulation>>"
puts
print_result(`coqwc proof/Simulation.v`)

puts
puts "<<Adq. w.r.t. Asm>>"
puts
print_result(`coqwc bound/LinkingC2.v bound/LowerBoundExtra.v bound/LowerBound.v`)

puts
puts "<<WHOLE>>"
puts
print_result(`find . ! -path '*demo/*' -name '*.v' ! -name 'UpperBound_AExtra.v' ! -name 'UpperBound_A.v' ! -name 'UpperBound_B.v' | xargs coqwc`)
