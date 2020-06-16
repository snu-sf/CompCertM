COQMODULE    := compcomp
# COQTHEORIES  := $(wildcard */*.v) #*/*.v
COQTHEORIES  := $(shell find . -path ./ignored -prune -o -iname '*.v')


.PHONY: all proof proof-quick graph

all:
	$(MAKE) proof

graph:
		sh make_graph.sh

### Quick
# proof-quick: Makefile.coq $(COQTHEORIES)
# 	$(MAKE) -f Makefile.coq quick

proof-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQTHEORIES))

proof: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R ../lib compcert.lib"; \
   echo "-R ../common compcert.common"; \
   echo "-R ../x86 compcert.x86"; \
   echo "-R ../x86_64 compcert.x86_64"; \
   echo "-R ../backend compcert.backend"; \
   echo "-R ../cfrontend compcert.cfrontend"; \
   echo "-R ../driver compcert.driver"; \
   echo "-R ../flocq compcert.flocq"; \
   echo "-R ../exportclight compcert.exportclight"; \
   echo "-R ../cparser compcert.cparser"; \
   echo "-R ../demo compcert.demo"; \
			\
   echo "-R lib $(COQMODULE)"; \
   echo "-R common $(COQMODULE)"; \
   echo "-R x86 $(COQMODULE)"; \
   echo "-R x86_64 $(COQMODULE)"; \
   echo "-R backend $(COQMODULE)"; \
   echo "-R cfrontend $(COQMODULE)"; \
   echo "-R driver $(COQMODULE)"; \
   echo "-R bound $(COQMODULE)"; \
			\
   echo "-R compose $(COQMODULE)"; \
   echo "-R proof $(COQMODULE)"; \
   echo "-R demo $(COQMODULE)"; \
   echo "-R selfsim $(COQMODULE)"; \
   echo "-R specIR $(COQMODULE)"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

### All
# NORMAL_BULID_DIR=.normal_build

# all: Makefile.coq-rsync
# 	$(MAKE) -f Makefile.coq-rsync all

# all-rsync:
# 	rsync -av --copy-links --delete \
# 	--exclude "$(NORMAL_BULID_DIR)" --exclude '.git/*' \
# 	--include '*/' \
# 	--filter=':- .gitignore' \
# 	'./' "$(NORMAL_BULID_DIR)/"
# 	$(MAKE) -C $(NORMAL_BULID_DIR) all
# 	rsync -av \
# 	--include '*/' --include "ccomp" --include "compcert.ini" --include "*.ml" --include "*.mli" \
# 	--exclude '*' \
#  "$(NORMAL_BULID_DIR)/" './'

# Makefile.coq-rsync: Makefile $(COQTHEORIES)
# 	(echo "-R ../../lib compcert.lib"; \
#    echo "-R ../../common compcert.common"; \
#    echo "-R ../../x86 compcert.x86"; \
#    echo "-R ../../x86_64 compcert.x86_64"; \
#    echo "-R ../../backend compcert.backend"; \
#    echo "-R ../../cfrontend compcert.cfrontend"; \
#    echo "-R ../../driver compcert.driver"; \
#    echo "-R ../../flocq compcert.flocq"; \
#    echo "-R ../../exportclight compcert.exportclight"; \
#    echo "-R ../../cparser compcert.cparser"; \
#    echo $(COQTHEORIES)) > _CoqProject
# 	coq_makefile -f _CoqProject -o Makefile.coq-rsync

###
# %.vo: Makefile.coq
# 	$(MAKE) -f Makefile.coq "$@"

# %.vio: Makefile.coq
# 	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean || true
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
# $(MAKE) -f Makefile.coq-rsync clean || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
