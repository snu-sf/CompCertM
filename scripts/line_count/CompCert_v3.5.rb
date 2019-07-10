def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  puts
  puts "RESULTS: #{result[0].to_i + result[1].to_i}"
end

puts "Count CompCert v3.5"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["cfrontend/SimplExprproof", "cfrontend/SimplExprspec",
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

f = File.open("../line_count/Shared_Pass_Proof", "r")
f.each_line do |line|
  line.split(" ").map!{|i| PASS_PROOFS << i}
end
f.close

PASS_PROOFS.map!{|i| i + ".v"}

EXCLUDE_FOLDERS=["arm", "powerpc", "riscV", "x86_32", "cparser"]

EXCLUDE_FOLDER=EXCLUDE_FOLDERS.inject(""){|sum, i| sum + "! -path \'*" + i + "\/*\' "}

EXCLUDE_FILES=["Ctyping"]

EXCLUDE_FILE=EXCLUDE_FILES.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}

puts
puts "<<<PASS_PROOFS>>>"
puts
result=`coqwc #{PASS_PROOFS.join(" ")}`
print result
puts
puts "Cstrategy part for pass proof: 770"
puts
puts "NOTE: Cstrategy is counted by hand because it contains both semantics and pass proof."
puts
result=result.split("\n")[-1].split(" ")
puts "RESULTS: #{result[0].to_i + result[1].to_i + 770}"

puts
puts "<<WHOLE>>"
puts
print_result(`find . -type f #{EXCLUDE_FOLDER} -name '*.v' #{EXCLUDE_FILE} | xargs coqwc`)
