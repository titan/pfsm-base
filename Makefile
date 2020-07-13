NAME=pfsm-base
NAME-LINK=$(subst _,-,$(NAME))

include .config
PKGPREFIX=Pfsm
TARGET=$(BUILDDIR)/build/ttc/$(PKGPREFIX)/Data.ttc
SRCS=$(wildcard $(PKGPREFIX)/*.idr)
DSTSRCS=$(addprefix $(BUILDDIR)/$(PKGPREFIX)/, $(notdir $(SRCS)))
PRJCONF=$(NAME-LINK).ipkg

all: $(TARGET)

$(TARGET): $(DSTSRCS) $(BUILDDIR)/$(PRJCONF) | prebuild
	@echo $(TARGET)
	@echo $(DSTSRCS)
	@echo $(BUILDDIR)/$(PRJCONF)
	cd $(BUILDDIR); idris2 --build $(PRJCONF); cd -

$(BUILDDIR)/$(PKGPREFIX)/%.idr: $(PKGPREFIX)/%.idr | prebuild
	cp $< $@

$(BUILDDIR)/$(PRJCONF): $(PRJCONF) | prebuild
	cp $< $@

prebuild:
ifeq "$(wildcard $(BUILDDIR)/$(PKGPREFIX))" ""
	@mkdir -p $(BUILDDIR)/$(PKGPREFIX)
endif

clean:
	@rm -rf $(BUILDDIR)

.PHONY: all clean prebuild .config
