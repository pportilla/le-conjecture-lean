/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedCurveFullTwistGermAlgebra
public import OnLeConjecture.Analytic.InjectiveIntersectionParametrization
public import OnLeConjecture.Analytic.PlaneBranchPowerEquationCoverage
public import OnLeConjecture.Analytic.AnalyticPointBasis
public import OnLeConjecture.Analytic.DepressedCubicCoefficientOrder

/-!
# Power-normalized parametrizations of the branches

For an irreducible plane germ `g` meeting the axis `{ξ = 0}` finitely, this module produces a
parametrization `G : ℂ → ℂ²` of `g` on a disc with second coordinate `G(z)_1 = z^a`, injective
on the disc, where `a = i₀(ξ, g)` is the intersection multiplicity with the coordinate `ξ`.
The order of the first coordinate at `0` and `a` have minimum equal to the multiplicity of `g`.
The construction combines the injective intersection parametrizations of the module
`InjectiveIntersectionParametrization` with the power normalization of the source parameter
`PointedMapGerm.exists_injective_power_representative`.

This is the per-branch part of Corollary `J14:cor:germ` and Lemma `J14:lem:packaging` of the
written proof, with the existing injective parametrizations in place of the finite root
covering of Lemma `J14:lem:root-cover`.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ PlaneCurve

/-- Pulling back along a source automorphism preserves the vanishing order. -/
theorem vanishingOrder_pullback_symm_eq (e : PointedEquivGerm 1) (x : Germ 1) :
    vanishingOrder (e.inverse.pullbackRingHom x) = vanishingOrder x := by
  have h : ∀ n : ℕ, e.inverse.pullbackRingHom x ∈ maximalIdeal 1 ^ n ↔ x ∈ maximalIdeal 1 ^ n :=
    fun n => PointedEquivGerm.pullback_mem_maximalIdeal_pow_iff e.symm x
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    exact mem_maximalIdeal_one_pow_iff.mp ((h n).mp (mem_maximalIdeal_one_pow_iff.mpr hn))
  · rw [← ENat.forall_natCast_le_iff_le]
    intro n hn
    exact mem_maximalIdeal_one_pow_iff.mp ((h n).mpr (mem_maximalIdeal_one_pow_iff.mpr hn))

/-- **A power-normalized parametrization of a branch.** -/
theorem exists_power_branch_parametrization (g : Germ 2) (hirr : Irreducible g)
    (hfin : HasFiniteIntersection (coordinate (1 : Fin 2)) g) :
    ∃ (a : ℕ) (G : ℂ → Source 2) (R : ℝ), 0 < a ∧ 0 < R ∧
      a = intersectionMultiplicity (coordinate (1 : Fin 2)) g hfin ∧
      AnalyticOnNhd ℂ G (ball 0 R) ∧ InjOn G (ball 0 R) ∧ G 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) R, G z 1 = z ^ a) ∧
      (∀ (W : Source 2 → ℂ) (hW : AnalyticAt ℂ W 0), ofFunction W hW = g →
        ∀ᶠ z in 𝓝 (0 : ℂ), W (G z) = 0) ∧
      (∀ m : ℕ, g ∈ maximalIdeal 2 ^ m → g ∉ maximalIdeal 2 ^ (m + 1) →
        min (analyticOrderAt (fun z => G z 0) 0) (a : ℕ∞) = m) := by
  obtain ⟨P, hPi⟩ := exists_injective_intersectionParametrization_of_irreducible g hirr
  have hfin' : HasFiniteIntersection g (coordinate (1 : Fin 2)) :=
    (hasFiniteIntersection_comm _ _).mp hfin
  have hne : P.map.pullbackRingHom (coordinate (1 : Fin 2)) ≠ 0 := P.pullback_ne_zero _ hfin'
  set a := (vanishingOrder (P.map.pullbackRingHom (coordinate (1 : Fin 2)))).toNat with hadef
  have htop : vanishingOrder (P.map.pullbackRingHom (coordinate (1 : Fin 2))) ≠ ⊤ :=
    vanishingOrder_eq_top_iff.not.mpr hne
  have ho : vanishingOrder (P.map.1.component 1) = a := by
    rw [← P.map.pullback_coordinate, hadef, ENat.natCast_toNat htop]
  have ha : 0 < a := by
    have hmem : P.map.pullbackRingHom (coordinate (1 : Fin 2)) ∈ maximalIdeal 1 ^ 1 :=
      PointedMapGerm.pullback_mem_maximalIdeal_pow P.map
        (by simp [coordinate_mem_maximalIdeal 1])
    have h1 := mem_maximalIdeal_one_pow_iff.mp hmem
    rw [← P.map.pullback_coordinate] at ho
    rw [ho] at h1
    exact_mod_cast h1
  have hint : a = intersectionMultiplicity (coordinate (1 : Fin 2)) g hfin := by
    rw [intersectionMultiplicity_comm, P.intersection_order _ hfin']
  obtain ⟨e, G0, hG0, hG00, hg, R, hR, hFa, hFi, hp⟩ :=
    P.map.exists_injective_power_representative hPi 1 ha ho
  let G : ℂ → Source 2 := fun z => G0 (curveParameterEquiv.symm z)
  have hG0zero : G 0 = 0 := by
    change G0 (curveParameterEquiv.symm 0) = 0
    rw [map_zero, hG00]
  refine ⟨a, G, R, ha, hR, hint, hFa, hFi, hG0zero, hp, ?_, ?_⟩
  · intro W hW hWg
    have hzero : (PointedMapGerm.ofFunction G0 hG0 hG00).pullbackRingHom (ofFunction W hW) = 0 := by
      rw [← hg, hWg, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply, P.curve_eq_zero,
        map_zero]
    have hevent : ∀ᶠ x in 𝓝 (0 : Source 1), W (G0 x) = 0 :=
      Filter.Germ.coe_eq.mp (congrArg (fun q : Germ 1 => q.1) hzero)
    have ht := curveParameterEquiv.symm.continuous.continuousAt.tendsto (x := (0 : ℂ))
    rw [map_zero] at ht
    exact ht.eventually hevent
  · intro m hm hmn
    have hmin := P.min_component_orders_eq_equation_order hirr m hm hmn
    rw [ho] at hmin
    have hcomp : vanishingOrder (P.map.1.component 0) =
        analyticOrderAt (fun z => G z 0) 0 := by
      have h1 : (PointedMapGerm.ofFunction G0 hG0 hG00).pullbackRingHom (coordinate 0) =
          e.inverse.pullbackRingHom (P.map.pullbackRingHom (coordinate 0)) := by
        rw [← hg, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
      rw [← P.map.pullback_coordinate, ← vanishingOrder_pullback_symm_eq e, ← h1,
        PointedMapGerm.pullback_coordinate]
      have hAn : AnalyticAt ℂ (fun x => G0 x 0) 0 := analyticAt_pi_iff.mp hG0 0
      have hc : (PointedMapGerm.ofFunction G0 hG0 hG00).1.component 0 =
          ofFunction (fun x => G0 x 0) hAn := by
        apply Subtype.ext
        exact MapGerm.component_ofFunction G0 hG0 0
      rw [hc, vanishingOrder_ofFunction_eq_analyticOrderAt]
      rfl
    rw [← hcomp]
    exact hmin

end OnLeConjecture.Analytic
