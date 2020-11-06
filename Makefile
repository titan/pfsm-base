include .config
NAME-LINK=$(subst _,-,$(NAME))

SRCS=$(wildcard $(PKGPREFIX)/*.idr) $(wildcard *.idr)
DSTSRCS=$(SRCS:%=$(BUILDDIR)/%)
PRJCONF=$(NAME-LINK).ipkg
DSTCONF=$(BUILDDIR)/$(PRJCONF)

all: $(TARGET)

install: $(TARGET)
	cd $(BUILDDIR); idris2 --install $(PRJCONF); cd -

$(TARGET): $(DSTSRCS) $(DSTCONF) | prebuild
	cd $(BUILDDIR); idris2 --build $(PRJCONF); cd -

$(DSTSRCS): $(BUILDDIR)/%: % | prebuild
	cp $< $@

$(DSTCONF): $(PRJCONF) | prebuild
	cp $< $@

prebuild:
ifeq "$(wildcard $(BUILDDIR)/$(PKGPREFIX))" ""
	@mkdir -p $(BUILDDIR)/$(PKGPREFIX)
endif

clean:
	@rm -rf $(BUILDDIR)

.PHONY: all clean install prebuild .config
