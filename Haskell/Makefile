GHC=ghc -XTypeOperators -XNullaryTypeClasses

all: gcderiv

gcderiv: GCDerivation.hs
	$(GHC) --make GCDerivation.hs Example23.hs Example31.hs \
	       Example51.hs Example53.hs Example54a.hs Example54b.hs \
	       Example56.hs Example58.hs

clean:
	find . -type f -name "*.o" -exec rm -fv {} \;
	find . -type f -name "*.hi" -exec rm -fv {} \;

