MAIN = paper
STYLE_URL = https://cgi.cse.unsw.edu.au/~eptcs/eptcsstyle.zip
STYLE_ZIP = eptcsstyle.zip
AGDA ?= agda
SVG_CONVERT ?= rsvg-convert
AGDA_SRC_DIR = ../src
AGDA_HTML_DIR = src
AGDA_HTML_ZIP = $(MAIN)-agda-html.zip
AGDA_HEN_SVG = agda.svg
AGDA_HEN_PDF = svg-inkscape/agda_svg-raw.pdf

.PHONY: all style agda-html agda-html-zip submission clean distclean

all: $(MAIN).pdf

submission: $(MAIN).pdf agda-html-zip

$(MAIN).pdf: $(MAIN).tex references.bib eptcs.cls eptcs.bst $(AGDA_HEN_PDF)
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

$(AGDA_HEN_PDF): $(AGDA_HEN_SVG)
	mkdir -p "$(@D)"
	$(SVG_CONVERT) -f pdf -o "$@" "$<"

agda-html:
	rm -rf "$(AGDA_HTML_DIR)"
	mkdir -p "$(AGDA_HTML_DIR)"
	$(AGDA) --html --html-dir="$(AGDA_HTML_DIR)" -i "$(AGDA_SRC_DIR)" "$(AGDA_SRC_DIR)/DualStopAtMu.agda"
	$(AGDA) --html --html-dir="$(AGDA_HTML_DIR)" -i "$(AGDA_SRC_DIR)" "$(AGDA_SRC_DIR)/Conversion.agda"
	$(AGDA) --html --html-dir="$(AGDA_HTML_DIR)" -i "$(AGDA_SRC_DIR)" "$(AGDA_SRC_DIR)/StopDualSoundness.agda"
	$(AGDA) --html --html-dir="$(AGDA_HTML_DIR)" -i "$(AGDA_SRC_DIR)" "$(AGDA_SRC_DIR)/ConversionStopDualSoundness.agda"
	$(AGDA) --html --html-dir="$(AGDA_HTML_DIR)" -i "$(AGDA_SRC_DIR)" "$(AGDA_SRC_DIR)/Examples.agda"

agda-html-zip: agda-html
	rm -f "$(AGDA_HTML_ZIP)"
	zip -qr "$(AGDA_HTML_ZIP)" "$(AGDA_HTML_DIR)"

style: eptcs.cls eptcs.bst

eptcs.cls eptcs.bst:
	curl -L "$(STYLE_URL)" -o "$(STYLE_ZIP)"
	unzip -o "$(STYLE_ZIP)" eptcs.cls eptcs.bst

clean:
	latexmk -C $(MAIN).tex
	rm -rf "$(AGDA_HTML_DIR)" "$(AGDA_HTML_ZIP)" "$(AGDA_HEN_PDF)"

distclean: clean
	rm -f eptcs.cls eptcs.bst "$(STYLE_ZIP)"
