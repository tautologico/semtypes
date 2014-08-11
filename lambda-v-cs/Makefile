
all: LambdaSyntax.vo

Tactics.vo: Tactics.v
	coqc Tactics.v

SetUtil.vo: Tactics.vo SetUtil.v
	coqc SetUtil.v

LambdaSyntax.vo: SetUtil.vo LambdaSyntax.v
	coqc LambdaSyntax.v

DBVar.vo: LambdaSyntax.vo DBVar.v
	coqc DBVar.v

clean: 
	rm -f *.vo
	rm -f *.glob

