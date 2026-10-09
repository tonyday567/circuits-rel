---
name: circuits-rel
description: Finite relations and cellular automata over groups, satellite of circuits. Circuit.Rel (two-grade reference semantics) plus Circuit.Cellular (shift-central maps, F_2[G] convolution, tori) with the circuits-rel-axioma oracle suite.
---

# circuits-rel — field guide

Satellite of `circuits` (stage 0 of the cellular arc split
`Circuit.Rel` out of core).  GF(2) group-ring convolution is
FinRel-over-G[G], hence the shared home.

## module map

```
Circuit.Rel       — finite relations, two reference grades: explicit
                    relations (Rel, Fin) and GF(2) linear relations
                    (FinRel).  Extracted verbatim from circuits core;
                    module name unchanged.
Circuit.Cellular  — cellular automata over groups (paper 197 section 7):
                    Config (bare g -> a), Group (Z via Integer, Z/n via
                    Mod n, S_3 via Perm3), shift, CA (memory + table),
                    LinCA (finite-support F_2[G]), convolution, torus
                    quotients, F_2 matrices.  The paper->circuits
                    dictionary lives in the module haddock.
```

## axioma topics (circuits-rel-axioma)

- **finrel** — the 39 FinRel oracles inherited from core.
- **cellular** — the five checks of loom/cellular.md: homomorphism on
  tori (S_3 makes the cd/dc order live), shift-centrality, the
  idempotent image characterization im(T_e) = fix(T_e), the projection
  law, and the 256-elementary-rule corpus (de Bruijn criterion
  cross-checked by torus enumeration).

## build and test

```bash
cabal build all
cabal run circuits-rel-axioma -- all
cabal-docspec
```

Same gate set as core: ormolu, hlint, cabal-gild (check mode,
positional argument), cabal check, ci project build.

## conventions

- Right-neighbor convention: (T_c x)(g) = sum c_u x(g u); the product
  is cd, not dc (paper Lemma 7.1's warning).  NEVER use unicode
  sub/superscript glyphs (U+2070-U+209C) anywhere in source — they
  silently truncate cabal-docspec extraction.
- Doctests are named witnesses only (no prop>); quantified laws live in
  the axioma topic, checked exhaustively over the finite instance.
