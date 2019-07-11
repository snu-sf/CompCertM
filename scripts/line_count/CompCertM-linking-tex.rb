def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  result=result[0].to_i + result[1].to_i
  puts
  puts "RESULTS: #{result}"
  return result
end

tex1="Pass Proofs    & 34,376     & 35,893 (+4.41\\%)  & " #NOTE: NEED CHANGE
tex2="The Rest       & 85,617     & 87,965 (+2.74\\%)  & " #NOTE: NEED CHANGE
tex3="Whole          & 119,993    & 123,858 (+3.22\\%) & " #NOTE: NEED CHANGE

tex4="Pass Proofs    & 1,842 &" #NOTE: NEED CHANGE
tex5="The Rest       & 260 &" #NOTE: NEED CHANGE
tex6="Whole          & 2,102 &" #NOTE: NEED CHANGE


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
tex3=tex3 + loc.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "(+" + (((loc/119993.0)*100).round(2)).to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "\\%) & 80,580    & 160,050 (+98.62\\%)                 & 108,776   & 152,104 (+39.83\\%) \\\\" #NOTE: NEED CHANGE

puts
puts "<<<PASS_PROOFS>>>"
puts
temp=print_result(`coqwc #{PASS_PROOFS.join(" ")}`)
loc=loc-temp
tex1=tex1 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "(+" + (((temp/34376.0)*100).round(2)).to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "\\%) & 21,215    & 52,140 (+145.77\\%) \\hspace{-1.8mm} & 26,466    & 30,572 (+15.51\\%)  \\\\ " #NOTE: NEED CHANGE
tex2=tex2 + loc.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "(+" + (((loc/85617.0)*100).round(2)).to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + "\\%) & 59,365    & 107,910 (+81.73\\%)                 & 82,312    & 121,532 (+47.65\\%) \\\\" #NOTE: NEED CHANGE

puts
puts "<<Unreadglob-PASS PROOF>>"
puts
temp=print_result(`coqwc #{UNREADGLOBPROOFS.map{|i| "demo/unreadglob/" + i + ".v"}.join(" ")}`)
tex4=tex4 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Unreadglob-rest>>"
puts
temp=print_result(`find demo/unreadglob #{UNREADGLOBPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex5=tex5 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Unreadglob-whole>>"
puts
temp=print_result(`coqwc demo/unreadglob/*.v`)
tex6=tex6 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Mutrec-PASS PROOF>>"
puts
temp=print_result(`coqwc #{MUTRECPROOFS.map{|i| "demo/mutrec/" + i + ".v"}.join(" ")}`)
tex4=tex4 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Mutrec-rest>>"
puts
temp=print_result(`find demo/mutrec #{MUTRECPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex5=tex5 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Mutrec-whole>>"
puts
temp=print_result(`coqwc demo/mutrec/*.v`)
tex6=tex6 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Utod-PASS PROOF>>"
puts
temp=print_result(`coqwc #{UTODPROOFS.map{|i| "demo/utod/" + i + ".v"}.join(" ")}`)
tex4=tex4 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & . \\\\"

puts
puts "<<Utod-rest>>"
puts
temp=print_result(`find demo/utod #{UTODPROOFS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)
tex5=tex5 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & . \\\\"

puts
puts "<<Utod-whole>>"
puts
temp=print_result(`coqwc demo/utod/*.v`)
tex6=tex6 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " & "

puts
puts "<<Adq. w.r.t. C>>"
puts
temp=print_result(`coqwc #{UPPERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)
tex6=tex6 + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ "

breakdown = "Interaction Semantics/Properties & "
puts
puts "<<Interation Semantics>>"
puts
temp=print_result(`coqwc compose/*.v #{INTERACTIONS.map{|i| "proof/" + i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

breakdown = breakdown + "Language Semantics/Properties & "
puts
puts "<<Language Semantics>>"
puts
temp=print_result(`coqwc #{LANGUAGE.map{|i| i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

breakdown = breakdown + "Self Simulation & "
puts
puts "<<Self Simulation>>"
puts
temp=print_result(`coqwc selfsim/*.v`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"


breakdown = breakdown + "\\cc{} Meta Theory Extension & "
puts
puts "<<CompCert Meta>>"
puts
temp=print_result(`find . ! -path '*demo/*' ! -path '*compose/*' ! -path '*proof/*' ! -path '*bound/*' ! -path '*selfsim/*' -name '*.v' \
#{PASS_PROOFS.inject(""){|sum, i| sum + "! -wholename \'\*" + i + "\' "}} #{INTERACTIONS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} \
#{LANGUAGE.inject(""){|sum, i| sum + "! -wholename \'\*" + i + ".v\' "}} #{LOWERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} | xargs coqwc`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

breakdown = breakdown + "\\icc{} Meta Theory & "
puts
puts "<<CompCertM meta>>"
puts
temp=print_result(`find proof -name '*.v' ! -name 'Simulation.v' ! -name 'SemProps.v' ! -name 'ModSemProps.v' | xargs coqwc`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

breakdown = breakdown + "Mixed Simulation & "
puts
puts "<<Mixed Simulation>>"
puts
temp=print_result(`coqwc proof/Simulation.v`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

breakdown = breakdown + "Adq. w.r.t. Asm & "
puts
puts "<<Adq. w.r.t. Asm>>"
puts
temp=print_result(`coqwc #{LOWERBOUNDS.map{|i| "bound/" + i + ".v"}.join(" ")}`)
loc=loc-temp
breakdown = breakdown + temp.to_s.reverse.gsub(/...(?=.)/,'\&,').reverse + " \\\\ \n"

puts
puts "<<WHOLE>>"
puts
print_result(`find . ! -path '*demo/*' #{UPPERBOUNDS.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}} -name '*.v' | xargs coqwc`)

File.open("results_table.tex", 'w') do |file|
  file.puts "\\begin{table}[t]"
  file.puts "%% \\footnotesize"
  file.puts"\\scriptsize"
  file.puts "%% [1.25pt]"
  file.puts "\\begin{tabu}{l |[1.25pt] r | r | r || r | r || r | r }"
  file.puts "Portion     & \\cc{} 3.5 & \\cc{}R 3.5        & \\icc{} pack                                               & \\cc{} 2.1 & \\ccc{}                             & \\cc{} 3.0 & \\ccx{}             \\\\"
  file.puts "\\hline"
  file.puts tex1
  file.puts tex2
  file.puts tex3
  file.puts "\\end{tabu}"
  file.puts "\\vspace{2mm}"
  file.puts "\\caption{SLOC of \\icc{} and related works --- compared to its baseline \\cc{}s, respectively}"
  file.puts "\\end{table}"
  file.puts "\\label{table:evaluation-ours}"
  file.puts
  file.puts "\\youngju{Table is fixed -- by jeehoonkang}"
  file.puts
  file.puts
  file.puts
  file.puts
  file.puts
  file.puts "\\begin{table}[t]"
  file.puts "\\scriptsize"
  file.puts "\\parbox{0.4\\linewidth}{"
  file.puts "\\begin{tabu}{l | l}"
  file.puts "Portion                          & SLOC                                                                                                     \\\\"
  file.puts "\\hline"
  file.puts breakdown
  file.puts
  file.puts "\\end{tabu}"
  file.puts "\\vspace{2mm}"
  file.puts "\\caption{Breakdown of                                                                                                                       \\\\"
  file.puts "  \\colorbox{light-gray}{\\icc{} pack - The Rest}}"
  file.puts "}%"
  file.puts "\\parbox{0.6\\linewidth}{"
  file.puts "\\begin{tabu}{l |[1.25pt] r | r | r | r | r}"
  file.puts "Portion                          & \\texttt{Unreadglob} 3.5 & \\texttt{Unreadglob} pack & \\texttt{mutual-sum} & \\texttt{utod} & Adq. w.r.t. C \\\\"
  file.puts "\\hline"
  file.puts tex4
  file.puts tex5
  file.puts tex6
  file.puts "\\end{tabu}"
  file.puts "\\vspace{2mm}"
  file.puts "\\caption{SLOC of Additional Developments}"
  file.puts "}%"
  file.puts "\\end{table}"
  file.puts "\\label{table:evaluation-others}"
end
puts "CHECKING: #{loc} must be 0"
