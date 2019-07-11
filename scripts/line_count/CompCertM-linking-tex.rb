def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  result=result[0].to_i + result[1].to_i
  puts
  puts "RESULTS: #{result}"
  return result
end

tex1="Pass Proofs    & 34376     & 35893 (+4.41\\\%)  & "
tex2="The Rest       & 85617     & 87965 (+2.74\\\%)  & "
tex3="Whole          & 119993    & 123858 (+3.22\\\%) & "

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
tex3=tex3 + loc.to_s + "(+" + (((loc/119993.0)*100).round(2)).to_s + "\\\%) & 2102 & "

puts
puts "<<<PASS_PROOFS>>>"
puts
temp=print_result(`coqwc #{PASS_PROOFS.join(" ")}`)
loc=loc-temp
tex1=tex1 + temp.to_s + "(+" + (((temp/34376.0)*100).round(2)).to_s + "\\\%) & 1842 & "
tex2=tex2 + loc.to_s + "(+" + (((loc/85617.0)*100).round(2)).to_s + "\\\%) & 260 & "

puts
puts "<<Unreadglob-PASS PROOF>>"
puts
temp=print_result(`coqwc #{UNREADGLOBPROOFS.map{|i| "demo/unreadglob/" + i + ".v"}.join(" ")}`)
tex1=tex1 + temp.to_s + " & "

puts
puts "<<Unreadglob-rest>>"
puts
temp=print_result(`find demo/unreadglob #{UNREADGLOBPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex2=tex2 + temp.to_s + " & "

puts
puts "<<Unreadglob-whole>>"
puts
temp=print_result(`coqwc demo/unreadglob/*.v`)
tex3=tex3 + temp.to_s + " & "

puts
puts "<<Mutrec-PASS PROOF>>"
puts
temp=print_result(`coqwc #{MUTRECPROOFS.map{|i| "demo/mutrec/" + i + ".v"}.join(" ")}`)
tex1=tex1 + temp.to_s + " & "

puts
puts "<<Mutrec-rest>>"
puts
temp=print_result(`find demo/mutrec #{MUTRECPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex2=tex2 + temp.to_s + " & "

puts
puts "<<Mutrec-whole>>"
puts
temp=print_result(`coqwc demo/mutrec/*.v`)
tex3=tex3 + temp.to_s + " & "

puts
puts "<<Utod-PASS PROOF>>"
puts
temp=print_result(`coqwc #{UTODPROOFS.map{|i| "demo/utod/" + i + ".v"}.join(" ")}`)
tex1=tex1 + temp.to_s + " & . \\\\"

puts
puts "<<Utod-rest>>"
puts
temp=print_result(`find demo/utod #{UTODPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex2=tex2 + temp.to_s + " & . \\\\"

puts
puts "<<Utod-whole>>"
puts
temp=print_result(`coqwc demo/utod/*.v`)
tex3=tex3 + temp.to_s + " & "

puts
puts "<<Adq. w.r.t. C>>"
puts
temp=print_result(`coqwc #{UPPERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)
tex3=tex3 + temp.to_s + " \\\\ "

breakdown = "Interaction Semantics & "
puts
puts "<<Interation Semantics>>"
puts
temp=print_result(`coqwc compose/*.v #{INTERACTIONS.map{|i| "proof/" + i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

breakdown = breakdown + "Language Semantics & "
puts
puts "<<Language Semantics>>"
puts
temp=print_result(`coqwc #{LANGUAGE.map{|i| i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

breakdown = breakdown + "Self Simulation & "
puts
puts "<<Self Simulation>>"
puts
temp=print_result(`coqwc selfsim/*.v`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"


breakdown = breakdown + "CompCert Meta & "
puts
puts "<<CompCert Meta>>"
puts
temp=print_result(`find . ! -path '*demo/*' ! -path '*compose/*' ! -path '*proof/*' ! -path '*bound/*' ! -path '*selfsim/*' -name '*.v' \
#{PASS_PROOFS.inject(""){|sum, i| sum + "! -wholename \'\*" + i + "\' "}} #{INTERACTIONS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} \
#{LANGUAGE.inject(""){|sum, i| sum + "! -wholename \'\*" + i + ".v\' "}} #{LOWERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} | xargs coqwc`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

breakdown = breakdown + "CompCertM Meta & "
puts
puts "<<CompCertM meta>>"
puts
temp=print_result(`find proof -name '*.v' ! -name 'Simulation.v' ! -name 'SemProps.v' ! -name 'ModSemProps.v' | xargs coqwc`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

breakdown = breakdown + "Mixed Simulation & "
puts
puts "<<Mixed Simulation>>"
puts
temp=print_result(`coqwc proof/Simulation.v`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

breakdown = breakdown + "Adq. w.r.t. Asm & "
puts
puts "<<Adq. w.r.t. Asm>>"
puts
temp=print_result(`coqwc #{LOWERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s + " \\\\ \n"

puts
puts "<<WHOLE>>"
puts
print_result(`find . ! -path '*demo/*' #{UPPERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

puts "----------------------"
print tex1
puts
print tex2
puts
print tex3
puts
puts "----------------------"
print breakdown
puts
puts "CHECKING: #{loc} must be 0"

