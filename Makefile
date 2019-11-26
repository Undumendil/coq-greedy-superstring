SWITCH=main
PKG=~/.opam/${SWITCH}/lib/coq/user-contrib
FLAGS = -impredicative-set
FLAGS += -R $(PKG)/GraphBasics GraphBasics
FLAGS += -R $(PKG)/FreeGroups FreeGroups
FLAGS += -R $(PKG)/Hammer Hammer
SRC=String.v ListUtil.v StringGraph.v Collapse.v Main.v
SRCINC=-l String.v -l ListUtil.v -l StringGraph.v -l Collapse.v -l Main.v

all:
	opam exec -- coqc $(FLAGS) $(SRC)

cli:
	opam exec -- coqtop $(FLAGS) $(SRCINC)
