/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import GrothendieckPeriod.GPC
import Mathlib.LinearAlgebra.Prod

/-!
# Point Cohomology GPC⁰(Spec Q̄) and Direct Sums

This module provides:
1. SpecQBar_H0: An explicit, concrete instantiation of VarietyCohomology 0
   modeling H⁰(Spec Q̄), with an **unconditional, sorry-free** proof
   GPC_SpecQBar_H0 : GPC SpecQBar_H0.
2. VarietyCohomology.directSum: The direct sum X ⊕ Y of two cohomological
   realizations in degree 2k (modeling disjoint unions of varieties X ⊔ Y
   or Künneth summands).
3. GPC.directSum: An **unconditional, sorry-free** proof that if GPC X
   and GPC Y hold, then GPC (X.directSum Y) holds.
-/

namespace GrothendieckPeriod

/-- The trivial period pairing (γ, α) ↦ γ * α on ℚ × ℚ → ℂ for H⁰(Spec Q̄). -/
noncomputable def pointPeriodPairing : ℚ →ₑ[ℚ] ℚ →ₑ[ℚ] ℂ where
  toFun γ :=
    { toFun := fun α => (γ : ℂ) * (α : ℂ)
      map_add' := fun α₁ α₂ => by push_cast; ring
      map_smul' := fun c α => by
        simp only [smul_eq_mul, RingHom.id_apply]
        push_cast
        ring }
  map_add' γ₁ γ₂ := by
    ext α
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    push_cast
    ring
  map_smul' c γ := by
    ext α
    simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply,
      LinearMap.smul_apply]
    push_cast
    ring

/-- Explicit cohomological realization of H⁰(Spec Q̄) (the unit motive ℚ(0)). -/
noncomputable def SpecQBar_H0 : VarietyCohomology 0 where
  H_dR := ℚ
  H_Betti := ℚ
  periodPairing := pointPeriodPairing
  algebraicCycleSubspace := ⊤
  cycle_periods_rational := by
    intro α _ γ
    refine ⟨γ * α, ?_⟩
    simp only [pointPeriodPairing, LinearMap.coe_mk, AddHom.coe_mk, pow_zero, mul_one]
    push_cast
    ring

/-- **Unconditional theorem**: Bost–Charles's GPC⁰(Spec Q̄) holds. -/
theorem GPC_SpecQBar_H0 : GPC SpecQBar_H0 := by
  intro _ _
  exact Submodule.mem_top

/-- Direct sum of two VarietyCohomology k structures (modeling disjoint unions X ⊔ Y). -/
noncomputable def VarietyCohomology.directSum {k : ℕ} (X Y : VarietyCohomology k) :
    VarietyCohomology k where
  H_dR := X.H_dR × Y.H_dR
  H_Betti := X.H_Betti × Y.H_Betti
  periodPairing :=
    { toFun := fun γ =>
        { toFun := fun α => X.periodPairing γ.1 α.1 + Y.periodPairing γ.2 α.2
          map_add' := fun α₁ α₂ => by
            simp only [Prod.fst_add, Prod.snd_add, map_add]
            ring
          map_smul' := fun c α => by
            simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply]
            ring }
      map_add' := fun γ₁ γ₂ => by
        ext α
        simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply,
          LinearMap.coe_mk, AddHom.coe_mk]
        ring
      map_smul' := fun c γ => by
        ext α
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_eq_mul, RingHom.id_apply,
          LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
        ring }
  algebraicCycleSubspace := X.algebraicCycleSubspace.prod Y.algebraicCycleSubspace
  cycle_periods_rational := by
    intro α hα γ
    rcases Submodule.mem_prod.mp hα with ⟨hα₁, hα₂⟩
    rcases X.cycle_periods_rational α.1 hα₁ γ.1 with ⟨q₁, hq₁⟩
    rcases Y.cycle_periods_rational α.2 hα₂ γ.2 with ⟨q₂, hq₂⟩
    refine ⟨q₁ + q₂, ?_⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, hq₁, hq₂]
    push_cast
    ring

/-- Left injection of H_Betti into the direct sum. -/
def VarietyCohomology.inlBetti {k : ℕ} (X Y : VarietyCohomology k) (γ : X.H_Betti) :
    (X.directSum Y).H_Betti :=
  (γ, 0)

/-- Right injection of H_Betti into the direct sum. -/
def VarietyCohomology.inrBetti {k : ℕ} (X Y : VarietyCohomology k) (γ : Y.H_Betti) :
    (X.directSum Y).H_Betti :=
  (0, γ)

/-- **Unconditional theorem**: If GPC^k(X) and GPC^k(Y) hold, then GPC^k(X ⊕ Y) holds. -/
theorem GPC.directSum {k : ℕ} {X Y : VarietyCohomology k}
    (hX : GPC X) (hY : GPC Y) : GPC (X.directSum Y) := by
  intro α hα
  apply Submodule.mem_prod.mpr
  constructor
  · apply hX
    intro γ₁
    rcases hα (X.inlBetti Y γ₁) with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simp only [VarietyCohomology.directSum, VarietyCohomology.inlBetti,
      LinearMap.coe_mk, AddHom.coe_mk, map_zero, LinearMap.zero_apply, add_zero] at hq
    exact hq
  · apply hY
    intro γ₂
    rcases hα (X.inrBetti Y γ₂) with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simp only [VarietyCohomology.directSum, VarietyCohomology.inrBetti,
      LinearMap.coe_mk, AddHom.coe_mk, map_zero, LinearMap.zero_apply, zero_add] at hq
    exact hq

end GrothendieckPeriod
