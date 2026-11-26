# Grothendieck Period Conjectures (Lean 4)

Formalization of structural aspects and concrete special cases of the Grothendieck period conjectures.

**Author:** Benjamin Stanley Frohman  
**License:** Apache License 2.0  
**Status:** Partial formalization of interfaces and special cases. The general conjecture over number fields remains open.

## Contents

- Abstract cohomological model of GPC^k(X) (Bost–Charles formulation)
- Special case for the Tate motive / P^1 reducing to the transcendence of π

## Build

```bash
elan default leanprover/lean4:v4.36.0
lake update
lake build
```

## CI

GitHub Actions runs `lake build` and prints axioms for key theorems.
