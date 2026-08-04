# PLACES Paper Scaffold

This directory contains an EPTCS-style scaffold for a PLACES research paper:

```sh
make style
make
```

The `style` target downloads `eptcs.cls` and `eptcs.bst` from the official
EPTCS style distribution. These generated style files and LaTeX build products
are ignored locally.

The paper contains relative links into Agda-generated HTML. Build the linked
HTML bundle with:

```sh
make agda-html-zip
```

This creates `paper-agda-html.zip` with a top-level `src/` directory. For a
submission artifact, distribute the PDF and this zip file together. Readers can
unzip the archive next to the PDF; the links in the PDF then resolve into the
unzipped `src/` directory.

Guidelines checked against the PLACES 2026 CFP:

- Research papers use the EPTCS style.
- Research papers have a maximum length of 8 pages.
- Bibliography and appendices are not counted in that limit, but reviewers are
  not required to read appendices.
- Research papers are reviewed for novelty, clarity, and technical soundness.
- Talk proposals are 2 pages and are not included in proceedings.

The scaffold assumes a research-paper submission.
