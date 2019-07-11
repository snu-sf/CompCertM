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

MUTRECPROOFS=["MutrecAproof", "MutrecBproof", "MutrecABproof"]

UTODPROOFS=["DemoSpecProof"]

PASS_PROOFS=["cfrontend/Cstrategyproof", "cfrontend/SimplExprproof", "cfrontend/SimplLocalsproof", "cfrontend/Cshmgenproof", "cfrontend/Cminorgenproof",
             "backend/Selectionproof", "backend/RTLgenproof", "backend/Tailcallproof", "backend/Inliningproof", "backend/Renumberproof", "backend/Constpropproof",
             "backend/CSEproof", "backend/Deadcodeproof", "backend/Unusedglobproof", "backend/Allocproof", "backend/Tunnelingproof", "backend/Linearizeproof",
             "backend/CleanupLabelsproof", "backend/Debugvarproof", "backend/Stackingproof", "backend/Separation", "x86/Asmgenproof"]

PASS_PROOFS.map!{|i| i + "C.v"}

UPPERBOUNDS=["UpperBound_AExtra", "UpperBound_A", "UpperBound_B"]

INTERACTIONS=["SemProps", "ModSemProps"]

LANGUAGE=["cfrontend/CsemC", "cfrontend/CstrategyC", "cfrontend/ClightC", "cfrontend/CsharpminorC",
          "backend/CminorC", "backend/CminorSelC", "backend/RTLC", "backend/LTLC", "backend/LinearC",
          "backend/MachC", "backend/MachExtra", "x86/AsmC", "x86/AsmExtra"]

LOWERBOUNDS=["LinkingC2", "LowerBoundExtra", "LowerBound"]

loc=`find . ! -path '*demo/*' #{UPPERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`.split("\n")[-1].split(" ")
loc=loc[0].to_i + loc[1].to_i

puts
puts "<<<PASS_PROOFS>>>"
puts
loc=loc-print_result(`coqwc #{PASS_PROOFS.join(" ")}`)

puts
puts "<<Unreadglob-PASS PROOF>>"
puts
print_result(`coqwc #{UNREADGLOBPROOFS.map{|i| "demo/unreadglob/" + i + ".v"}.join(" ")}`)

puts
puts "<<Unreadglob-rest>>"
puts
print_result(`find demo/unreadglob #{UNREADGLOBPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts
puts "<<Unreadglob-whole>>"
puts
print_result(`coqwc demo/unreadglob/*.v`)

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
print_result(`coqwc #{UPPERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)

puts
puts "<<Interation Semantics>>"
puts
loc=loc-print_result(`coqwc compose/*.v #{INTERACTIONS.map{|i| "proof/" + i + ".v"}.join(" ")}`)

puts
puts "<<Language Semantics>>"
puts
loc=loc-print_result(`coqwc #{LANGUAGE.map{|i| i + ".v"}.join(" ")}`)

puts
puts "<<Self Simulation>>"
puts
loc=loc-print_result(`coqwc selfsim/*.v`)


puts
puts "<<CompCert Meta>>"
puts
loc=loc-print_result(`find . ! -path '*demo/*' ! -path '*compose/*' ! -path '*proof/*' ! -path '*bound/*' ! -path '*selfsim/*' -name '*.v' \
#{PASS_PROOFS.inject(""){|sum, i| sum + "! -wholename \'\*" + i + "\' "}} #{INTERACTIONS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} \
#{LANGUAGE.inject(""){|sum, i| sum + "! -wholename \'\*" + i + ".v\' "}} #{LOWERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} | xargs coqwc`)

puts
puts "<<CompCertM meta>>"
puts
loc=loc-print_result(`find proof -name '*.v' ! -name 'Simulation.v' ! -name 'SemProps.v' ! -name 'ModSemProps.v' | xargs coqwc`)

puts
puts "<<Mixed Simulation>>"
puts
loc=loc-print_result(`coqwc proof/Simulation.v`)

puts
puts "<<Adq. w.r.t. Asm>>"
puts
loc=loc-print_result(`coqwc #{LOWERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)

puts
puts "<<WHOLE>>"
puts
print_result(`find . ! -path '*demo/*' #{UPPERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts
puts "Check #{loc} must be 0"
