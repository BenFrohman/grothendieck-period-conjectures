# Grothendieck Period Conjectures in Lean 4

Formalization in **Lean 4** (v4.36.0) and **Mathlib** of the cohomological, linear-algebraic, and Tannakian structures surrounding the **Grothendieck Period Conjectures**, **Bost–Charles's $\mathrm{GPC}^k(X)$**, and **André's Generalized Period Conjecture**.

## Module Overview

| Module | Description | Proof Status |
| :--- | :--- | :--- |
| `GrothendieckPeriod/GPC.lean` | Bost–Charles cohomological model `VarietyCohomology k`, `HasRationalPeriods`, `GPC`, and `cycle_iff_rational_periods`. | **Closed (no sorry)** |
| `GrothendieckPeriod/TateMotive.lean` | Explicit realization `P1_H2 : VarietyCohomology 1` for $H^2(\mathbb{P}^1)$, unconditional proof `GPC_P1_H2`, and pullback functoriality `HasRationalPeriods.pullback`. | **Closed (no sorry)** |
| `GrothendieckPeriod/DirectSum.lean` | Point realization `SpecQBar_H0 : VarietyCohomology 0`, unconditional proof `GPC_SpecQBar_H0`, direct sums `X.directSum Y`, and `GPC.directSum`. | **Closed (no sorry)** |
| `GrothendieckPeriod/TensorProduct.lean` | Künneth tensor product `X.tensor Y : VarietyCohomology (k₁ + k₂)` and preservation of period rationality on pure tensors `HasRationalPeriods.tmul`. | **Closed (no sorry)** |
| `GrothendieckPeriod/PeriodTorsor.lean` | Rank-$n$ de Rham–Betti `ComparisonSystem n`, the period subalgebra $\mathbb{Q}[P_{ij}] \subseteq \mathbb{C}$, and unconditional proof `periodSubalgebra_changeOfBasis_eq` of invariance under $\mathrm{GL}_n(\mathbb{Q}) \times \mathrm{GL}_n(\mathbb{Q})$. | **Closed (no sorry)** |
| `GrothendieckPeriod/Tannakian.lean` | Nori-motive formulation `GrothendieckPeriodConjecture`, André's generalization `AndrePeriodConjecture`, and unconditional equivalence `Grothendieck_iff_Andre_over_Q` over $\mathbb{Q}$. | **Closed (no sorry)** |
| `GrothendieckPeriod/ClassicalBounds.lean` | Elliptic period quadruples, formal statement of Chudnovsky's bound, and unconditional deduction `GPC_CM_elliptic_curve` for CM elliptic curves. | Deduction closed (`chudnovsky_elliptic_periods` awaits Schneider–Lang in Mathlib) |
| `GrothendieckPeriod/AxiomCheck.lean` | `#print axioms` audit target confirming all proved theorems use only standard Lean axioms. | **Closed (no sorry)** |

## Building & Verifying

```bash
lake update
lake build
lake env lean GrothendieckPeriod/AxiomCheck.lean
```

## License

Apache-2.0 — Copyright 2026 Benjamin Stanley Frohman.
