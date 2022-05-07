COQMFFLAGS := -Q . LF  

ALLVFILES := \
	Preface.v                 PrefaceTest.v \
	Basics.v                  BasicsTest.v \
	Induction.v               InductionTest.v \
	Lists.v                   ListsTest.v \
	Poly.v                    PolyTest.v \
	Tactics.v                 TacticsTest.v \
	Logic.v                   LogicTest.v \
	IndProp.v                 IndPropTest.v \
	Maps.v                    MapsTest.v \
	ProofObjects.v            ProofObjectsTest.v \
	IndPrinciples.v           IndPrinciplesTest.v \
	Rel.v                     RelTest.v \
	# Imp.v                     ImpTest.v \
	# ImpParser.v               ImpParserTest.v \
	# ImpCEvalFun.v             ImpCEvalFunTest.v \
	# Extraction.v              ExtractionTest.v \
	# Auto.v                    AutoTest.v \
	# AltAuto.v                 AltAutoTest.v \
	# Postscript.v              PostscriptTest.v \
	# Bib.v                     BibTest.v \


build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
