MODULES := pred prelude idynamic ordtype pperm finmap domain pcm unionmap heap spcm coding hgraphs

RELEASE := $(MODULES:%=%.v) Makefile Makefile.build

ssr.pname := ${COQTOP}/lib/coq/user-contrib/Ssreflect
ssr.lname := Ssreflect
mathcomp.pname := ${COQTOP}/lib/coq/user-contrib/MathComp
mathcomp.lname := MathComp
COQLIBS := ssr mathcomp

include Makefile.build

all: coq
