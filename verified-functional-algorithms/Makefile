COQMFFLAGS := -Q . VFA  -arg "-w -omega-is-deprecated,-implicit-core-hint-db"

ALLVFILES := \
	# Maps.v                   MapsTest.v \
	# Preface.v                PrefaceTest.v \
	# Perm.v                   PermTest.v \
	# Sort.v                   SortTest.v \
	# Multiset.v               MultisetTest.v \
	# BagPerm.v                BagPermTest.v \
	# Selection.v              SelectionTest.v \
	# Merge.v                  MergeTest.v \
	# SearchTree.v             SearchTreeTest.v \
	# ADT.v                    ADTTest.v \
	# Extract.v                ExtractTest.v \
	# Redblack.v               RedblackTest.v \
	# Trie.v                   TrieTest.v \
	# Priqueue.v               PriqueueTest.v \
	# Binom.v                  BinomTest.v \
	# Decide.v                 DecideTest.v \
	# Color.v                  ColorTest.v \


build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) 

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
