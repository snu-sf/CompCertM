def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  puts
  puts "RESULTS: #{result[0].to_i + result[1].to_i}"
end

puts "Count MultiComp"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/Cstrategyproof",
             "cfrontend/SimplExprproof", "cfrontend/SimplExprspec",
             "cfrontend/SimplLocalsproof",
             "x86/SelectOpproof", "x86/SelectLongproof", "backend/SplitLongproof",
             "x86/ConstpropOpproof",
             "x86/CombineOpproof",
             "backend/Deadcodeproof",
             "backend/Unusedglobproof",
             "backend/Debugvarproof",
             "common/Separation",
             "x86/Asmgenproof", "x86/Asmgenproof1",
             "backend/ValueAnalysis"]

f = File.open("compcomp-linking/scripts/line_count/Shared_Pass_Proof", "r")
f.each_line do |line|
  line.split(" ").map!{|i| PASS_PROOFS << i}
end
f.close

PASS_PROOFS.map!{|i| i + ".v"}

EXCLUDE_FOLDERS=["compcomp-linking", ".normal_build", "demo", "arm", "powerpc", "riscV", "x86_32", "cparser"]

EXCLUDE_FOLDER=EXCLUDE_FOLDERS.inject(""){|sum, i| sum + "! -path \'*" + i + "\/*\' "}

EXCLUDE_FILES=["Ctyping"]

EXCLUDE_FILE=EXCLUDE_FILES.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}

puts
puts "<<<PASS_PROOFS>>>"
puts
print_result(`coqwc #{PASS_PROOFS.join(" ")}`)

puts
puts "<<WHOLE>>"
puts
print_result(`find . -type f #{EXCLUDE_FOLDER} -name '*.v' #{EXCLUDE_FILE} | xargs coqwc`)
