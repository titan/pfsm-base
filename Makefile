include .config
NAME-LINK=$(subst _,-,$(NAME))

SRCS=$(wildcard $(PKGPREFIX)/*.idr) $(wildcard *.idr)
DSTSRCS=$(SRCS:%=$(BUILDDIR)/%)
PRJCONF=$(NAME-LINK).ipkg
DSTCONF=$(BUILDDIR)/$(PRJCONF)

all: $(TARGET)

install: $(TARGET)
	cd $(BUILDDIR); sudo idris2 --install $(PRJCONF); cd -
	sudo chmod -R 755 `idris2 --libdir`/$(LIBPREFIX)

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
