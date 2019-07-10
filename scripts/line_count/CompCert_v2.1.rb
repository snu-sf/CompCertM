puts "Count CompCert v2.1"
# system("find . -name '*.v'| xargs coqwc")
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
system("coqwc #{PASS_PROOFS.join(" ")}")
puts

puts
puts "<<WHOLE>>"
puts
system("find . -type f " + EXCLUDE_FOLDER + "-name '*.v' " + EXCLUDE_FILE + " | xargs coqwc")
