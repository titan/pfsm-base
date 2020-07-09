NAME=pfsm-base
NAME-LINK=$(subst _,-,$(NAME))

include .config
ESCAPED-BUILDDIR = $(shell echo '$(BUILDDIR)' | sed 's%/%\\/%g')
TARGET=$(BUILDDIR)/build/exec/fsm-lint
SRCS=$(wildcard Pfsm/*.idr)
DSTSRCS=$(addprefix $(BUILDDIR)/Pfsm/, $(notdir $(SRCS)))
PRJCONF=$(NAME-LINK).ipkg

all: $(TARGET)

$(TARGET): $(DSTSRCS) $(BUILDDIR)/$(PRJCONF) | prebuild
	cd $(BUILDDIR); idris2 --build $(PRJCONF); cd -

$(BUILDDIR)/Pfsm/%.idr: Pfsm/%.idr | prebuild
	cp $< $@

$(BUILDDIR)/$(PRJCONF): $(PRJCONF) | prebuild
	cp $< $@

prebuild:
ifeq "$(wildcard $(BUILDDIR)/Pfsm)" ""
	@mkdir -p $(BUILDDIR)/Pfsm
endif

clean:
	@rm -rf $(BUILDDIR)

.PHONY: all clean prebuild
