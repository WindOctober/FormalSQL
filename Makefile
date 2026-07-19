ROCQ ?= rocq
JOBS ?= 1
ROCQ_MAKEFILE := src/Makefile.rocq

.PHONY: all install clean

$(ROCQ_MAKEFILE): src/_CoqProject
	cd src && $(ROCQ) makefile -f _CoqProject -o Makefile.rocq

all: $(ROCQ_MAKEFILE)
	$(MAKE) -C src -f Makefile.rocq -j$(JOBS)

install: $(ROCQ_MAKEFILE)
	$(MAKE) -C src -f Makefile.rocq -j$(JOBS) install

clean: $(ROCQ_MAKEFILE)
	$(MAKE) -C src -f Makefile.rocq clean
