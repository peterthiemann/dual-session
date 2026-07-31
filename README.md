# dual-session

This repository contains an Agda development about duality for recursive
session types.  The current focus is the "stop duality at mu" presentation:
duality is allowed to reduce through exposed communication heads, but it does
not reduce under a recursive binder.

The development has three main parts:

- a coinductive ground model of session types and equivalence;
- an inductive syntax for recursive session types with renamings and
  simultaneous substitutions;
- a stopped-duality operator and a syntactic conversion judgment, with
  soundness proofs into the coinductive model.

The Agda source is in `src/`.  The PLACES paper scaffold and generated Agda
HTML bundle are in `tex/`.

## Main Files

- `src/DualStopAtMu.agda` defines the stopped-duality operator by rewrite
  rules, observational stopped duality, examples, and the ground theorem
  relating stopped duality to coinductive duality.
- `src/Conversion.agda` defines the syntactic conversion judgment used in the
  paper and proves conversion soundness.  The renaming and substitution
  soundness proofs use explicit coalgebras, avoiding `TERMINATING` pragmas.
- `src/Examples.agda` collects useful examples from the older exploratory
  modules, including the Bernardi-Hennessy-shaped counterexample for naive
  syntactic duality.
- `src/Types/COI.agda` is the coinductive ground model.
- `src/Types/IND1.agda` is the current inductive syntax with ordinary
  variables, renamings, and simultaneous substitutions.

See `src/README.md` for a fuller module overview.

## Checking

The focused development can be checked with:

```sh
agda -i src src/Conversion.agda
agda -i src src/DualStopAtMu.agda
agda -i src src/Examples.agda
```

The `OutOfFocus` directory contains older or partial developments that are kept
for reference and are not part of the main proof chain.

## Paper

Build the paper from `tex/`:

```sh
make -C tex
```

Generate the Agda HTML bundle used by the links in the PDF with:

```sh
make -C tex agda-html-zip
```

That target creates `tex/paper-agda-html.zip`, whose top-level directory is
`src/`.
