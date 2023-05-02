COQMFFLAGS := -Q . PLF  

ALLVFILES := \
	Maps.v                        MapsTest.v \
	Imp.v                         ImpTest.v \
	Preface.v                     PrefaceTest.v \
	Equiv.v                       EquivTest.v \
	Hoare.v                       HoareTest.v \
	Hoare2.v                      Hoare2Test.v \
	HoareAsLogic.v                HoareAsLogicTest.v \
	Smallstep.v                   SmallstepTest.v \
	Types.v                       TypesTest.v \
	Stlc.v                        StlcTest.v \
	StlcProp.v                    StlcPropTest.v \
	MoreStlc.v                    MoreStlcTest.v \
	Sub.v                         SubTest.v \
	Typechecking.v                TypecheckingTest.v \
	# Records.v                     RecordsTest.v \
	# References.v                  ReferencesTest.v \
	# RecordSub.v                   RecordSubTest.v \
	# Norm.v                        NormTest.v \
	# PE.v                          PETest.v \
	# Postscript.v                  PostscriptTest.v \
	# Bib.v                         BibTest.v \
	# LibTactics.v                  LibTacticsTest.v \
	# UseTactics.v                  UseTacticsTest.v \
	# UseAuto.v                     UseAutoTest.v \


build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
