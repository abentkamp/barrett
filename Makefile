CHARON_EXE = charon
AENEAS_EXE = aeneas

AENEAS_OPTIONS ?= -loops-to-rec

.PHONY: extract
extract: barrett.llbc
	$(AENEAS_EXE) -backend lean barrett.llbc -split-files -dest proofs/Barrett $(AENEAS_OPTIONS)

barrett.llbc: $(wildcard */*.rs)
	RUSTFLAGS="--cfg hax" $(CHARON_EXE) cargo --preset=aeneas --rustc-arg=--cfg=hax