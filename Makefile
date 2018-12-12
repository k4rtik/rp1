all:
	coqc Monad.v && coqc Prelim.v && coqc Complex.v && coqc Matrix.v && coqc Quantum.v Maps.v

clean:
	rm -f *.vo *.glob .*.aux
