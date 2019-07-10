def print_result(result)
  printf result
  result=result.split("\n")[-1].split(" ")
  puts
  puts "RESULTS: #{result[0].to_i + result[1].to_i}"
end

puts "Count CompCert v2.1"
puts
puts "<<Preprocessing>>"
puts "make *.vp > *.v"
system("find . -name '*.vp' | xargs -I % bash -c 'vp=%; v=${vp/.vp/.v}; ./ndfun $vp > $v'")
puts

PASS_PROOFS=["ia32/SelectOpproof", "ia32/ConstpropOpproof", "ia32/CombineOpproof", "ia32/Asmgenproof", "ia32/Asmgenproof1", "backend/SelectLongproof"]

f = File.open("../../line_count/Shared_Pass_Proof", "r")
f.each_line do |line|
  line.split(" ").map!{|i| PASS_PROOFS << i}
end
f.close

PASS_PROOFS.map!{|i| i + ".v"}

EXCLUDE_FOLDERS=["arm", "powerpc"]

EXCLUDE_FOLDER=EXCLUDE_FOLDERS.inject(""){|sum, i| sum + "! -path \'*" + i + "\/*\' "}

EXCLUDE_FILES=["Cexec", "initializers", "initilizersproof", "Cstrategy", "Csem", "Csyntax", "SimplLocals", "SimplLocalsproof", "SimplExpr", "SimplExprproof", "Ctyping"]

EXCLUDE_FILE=EXCLUDE_FILES.inject(""){|sum, i| sum + "! -name \'" + i + ".v\' "}

puts
puts "<<<PASS_PROOFS>>>"
puts
print_result(`coqwc #{PASS_PROOFS.join(" ")}`)
puts

puts
puts "<<WHOLE>>"
puts
print_result(`find . -type f #{EXCLUDE_FOLDER} -name '*.v' #{EXCLUDE_FILE} | xargs coqwc`)
