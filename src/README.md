# Agda Source Overview

This directory contains the formal development for stopped duality and
recursive session types.  The main line of the development uses `Types.IND1`
for syntax, `Types.COI` as the coinductive semantics, and `DualTail1` as the
stack-based interpretation from inductive recursive types into the coinductive
model.

## Main Development

- `DualStopAtMu.agda`
  Defines the stopped-duality operator `dualS`/`dualG` by postulated rewrite
  equations for exposed guarded heads.  There are rewrite equations for
  `gdd`, `transmit`, `choice`, and `end`, but no rewrite equation for `rec` or
  `var`.  The module also defines observational stopped duality, proves its
  symmetry and involutive behavior, gives small examples, and proves `ground`,
  the comparison with coinductive duality.

- `Conversion.agda`
  Defines the syntactic conversion judgments `ConvT` and `ConvS`, including
  unrolling and stopped-duality conversion rules.  It proves soundness of
  conversion with respect to the coinductive model.  Renaming and substitution
  soundness are implemented through explicit coalgebras (`RenRel` and
  `SubRel`) behind the public facade lemmas `rename-soundS/G/T`,
  `lookupSub`, and `subst-soundS/G/T`.

- `StopDualSoundness.agda`
  Compares observational stopped duality with the coinductive relational
  duality in `Types.COI`.  It proves `sd-sound` and `sd-complete`, relating
  `S ⊥sd R` exactly to duality of the stack interpretations.  The proof uses
  explicit coalgebras for syntactic equivalence, semantic equivalence
  reflection, and stopped-duality observations.

- `ConversionStopDualSoundness.agda`
  Bridges the syntactic conversion presentation of stopped duality with the
  observational relation.  It proves `conv-dual-sound-sd`, deriving
  `S ⊥sd R` from a conversion proof that `dualS S` converts to `R`.  It also
  proves both directions of the equivalence-level characterization relating
  `S ⊥sd R` and syntactic equivalence between `dualS S` and `R`, and packages
  the main comparison results as `master-comparison`.

- `ConversionCompletenessCounterexample.agda`
  Records the period-collapse example behind the failure of the converse
  completeness direction for conversion.  The module proves observational
  stopped duality for `μX.?X` and `μX.!!X`; a finite conversion proof from
  `dualS (μX.?X)` to `μX.!!X` would have to solve the same obligation again.

- `Examples.agda`
  Collects small examples that are useful for the paper and for regression
  checking.  These include message-closure examples, stopped-duality examples,
  and a Bernardi-Hennessy-shaped counterexample showing non-involutivity of a
  naive syntactic duality operation.

## Semantic and Syntactic Infrastructure

- `Types/COI.agda`
  Coinductive session types, payload types, equivalence, relational duality,
  functional duality, and the basic properties connecting them.

- `Types/IND1.agda`
  Current inductive syntax for payload and session types with recursive
  binders and ordinary de Bruijn variables.  It also defines full renamings,
  simultaneous substitutions, weakening, and supporting lemmas.

- `DualTail1.agda`
  Stack-based interpretation of inductive recursive session types into the
  coinductive model.  Recursive bodies are stored in a stack and variables are
  unfolded by lookup.  The module also contains the tail-recursive comparison
  theorem for `Types.Tail1`.

- `Types/Tail1.agda`
  Tail-recursive session syntax with closed channel payloads and the direct
  structural duality operation used by the older tail-recursive comparison.

- `MessageClosure.agda`
  Translation from `Types.IND1` into `Types.Tail1` that closes channel payloads
  by replacing open payload occurrences with closed session types.

- `Types/Direction.agda`
  Send/receive directions and involution of direction duality.

- `Auxiliary/Extensionality.agda`
  Functional extensionality postulate used by syntax-manipulation lemmas.

## Older Or Supporting Modules

- `Duality.agda`
  Older development based on `Types.IND`, which has polarized variables and a
  more global syntactic duality proof.  It is useful historical context but is
  not the current stopped-duality line.

- `DualRel.agda`
  Inductive relational duality for the older `Types.IND` syntax.

- `STypeCongruence.agda`
  Congruence lemmas for coinductive session equivalence using session-type
  holes.

- `Types/IND.agda`
  Older inductive syntax with polarized variables, plus associated weakening,
  substitution, and duality operations.

## Out Of Focus

`OutOfFocus/` contains older or partial developments kept for reference:

- `OutOfFocus/DualContractive.agda`
  Exploration of contractive recursive session types and alternative
  substitution/weakening encodings.

- `OutOfFocus/Max.agda`
  Finite-index maximum lemmas used by the contractive exploration.

- `OutOfFocus/MessageClosureProperties.agda`
  Partial proof work about semantic preservation of message closure.
