FSTAR_HOME=../..
OTHERFLAGS+=--already_cached 'Prims FStar LowStar' --include parsing --record_hints
include ../Makefile.include
ROOTS=Test.fst Locals.Effect.fst LL.fst MSeqExn.fst Flights.fst FlightsExn.fst FlightsStExn.fst Z3EncodingIssue.fst #Buffers.fst

all: verify-all

.depend:
	$(FSTAR) --dep full $(ROOTS) > .depend

depend: .depend

include .depend

verify-all: $(ALL_CHECKED_FILES)

%.checked:
	$(FSTAR) --cache_checked_modules $<

clean:
	rm -f .depend *.checked parsing/*.checked
	rm -rf out

extract:
	fstar.exe --codegen OCaml --extract '-* LL' --odir out LL.fst
	krml -skip-compilation -tmpdir out -I parsing Buffers.fst parsing/Flights.fst parsing/FlightsExn.fst #parsing/FlightsStExn.fst -- double reification leaves a lambda around, which is not valid Low*
