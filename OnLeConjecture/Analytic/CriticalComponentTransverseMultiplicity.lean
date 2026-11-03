/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericTransverseSectionOrder
public import OnLeConjecture.Analytic.InjectiveCurveMultiplicity
public import OnLeConjecture.Analytic.CriticalJacobianDivisor

/-!
# Transverse branch multiplicities of critical components

Every irreducible factor of the common coordinate Jacobian divisor has
transverse plane branches of multiplicity one greater than its divisor
order. The branches are constructed at all sufficiently small nonzero
parameters of an injective parametrization of the component. The result
retains the source coordinates, selected target coordinate, injective
transverse parametrization, and irreducible image equation with its full
pullback kernel.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- A transverse plane branch at a point of a component equation, including
the coordinate changes and the exact order of its irreducible image equation. -/
def TransverseBranchEquationAt (G : Source 2 → Source 3) (P : Source 2 → ℂ)
    (x : Source 2) (m : ℕ) : Prop :=
  ∃ (hGx : AnalyticAt ℂ G x) (hPx : AnalyticAt ℂ P x)
    (i : Fin 3) (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2) (f : Germ 2),
    P x = 0 ∧
    e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction G x hGx).1.component i) =
      coordinate 0 ∧
    e.forward.pullbackRingHom (Germ.ofFunctionAt P x hPx) = coordinate 1 ∧
    (hyperplaneInclusionGerm 2).comp β =
      ((coordinateSwapPointedEquiv i).forward.comp
        (PointedMapGerm.recenterOfFunction G x hGx)).comp
          (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
    β.HasInjectiveRepresentative ∧ Irreducible f ∧ β.pullbackRingHom f = 0 ∧
    RingHom.ker β.pullbackRingHom = Ideal.span {f} ∧
    min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) = m ∧
    f ∈ maximalIdeal 2 ^ m ∧ f ∉ maximalIdeal 2 ^ (m + 1)

namespace CriticalJacobianFactorization

/-- The common-minor order determines the multiplicity of constructed
transverse branches along an injectively parametrized critical component. -/
theorem exists_generic_transverse_branch_equations
    {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)
    (hi : g.HasInjectiveRepresentative) (p : Germ 2) (hp : p ∈ D.support) :
    ∃ (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
      (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
      (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0),
      g = PointedMapGerm.ofFunction G hG hG0 ∧ p = Germ.ofFunction P hP ∧
      (PointedMapGerm.ofFunction C hC hC0).HasInjectiveRepresentative ∧
      (∀ h : Germ 2,
        (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        TransverseBranchEquationAt G P (C t) (D.order p + 1) := by
  classical
  obtain ⟨G, hG, hG0, hg, S, hS, hinj⟩ := hi
  obtain ⟨P, hP, hpP⟩ := exists_analyticRepresentative_allOrders p
  obtain ⟨γ, hγinj, hn, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible p (D.irreducible p hp)
  obtain ⟨C, hC, hC0, hγ⟩ := γ.exists_ofFunction
  rw [hγ] at hγinj hn hker
  have hdiv (i j : Fin 3) : Germ.ofFunction P hP ^ D.order p ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j) := by
    simpa only [← hpP, ← hg] using D.pow_dvd_minors p hp i j
  have hexact : ∃ i j : Fin 3, ¬ Germ.ofFunction P hP ^ (D.order p + 1) ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j) := by
    by_contra! h
    have hle := (D.order_maximal p hp (D.order p + 1)).mp
      (by simpa only [hpP, hg] using h)
    omega
  refine ⟨G, hG, hG0, P, hP, C, hC, hC0, hg, hpP, hγinj, hker, ?_⟩
  have ht := eventually_exists_injective_transverse_section_of_exact_common_power
    G hG hG0 S hS hinj P hP (hpP ▸ D.irreducible p hp) (D.order p) hdiv hexact
    C hC hC0 hn (by simpa only [← hpP] using hker)
  filter_upwards [ht] with t ht htn
  obtain ⟨hGt, hPt, i, e, β, hP0, he, hep, hβ, hβinj, horder⟩ := ht htn
  obtain ⟨f, hirr, hzero, hkernel, hf, hnext⟩ :=
    β.exists_irreducible_image_equation_of_order hβinj (D.order p + 1) horder
  exact ⟨hGt, hPt, i, e, β, f, hP0, he, hep, hβ, hβinj, hirr, hzero,
    hkernel, horder, hf, hnext⟩

end CriticalJacobianFactorization

namespace PointedMapGerm

/-- The canonical common Jacobian divisor supplies every algebraic input
to the transverse branch construction. -/
theorem exists_generic_transverse_branch_equations_of_critical_factor
    (g : PointedMapGerm 2 3) (hi : g.HasInjectiveRepresentative)
    (p : Germ 2) (hp : p ∈ (g.criticalJacobianFactorization hi).support) :
    ∃ (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
      (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
      (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0),
      g = ofFunction G hG hG0 ∧ p = Germ.ofFunction P hP ∧
      (ofFunction C hC hC0).HasInjectiveRepresentative ∧
      (∀ h : Germ 2, (ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        TransverseBranchEquationAt G P (C t) ((g.criticalJacobianFactorization hi).order p + 1) :=
  (g.criticalJacobianFactorization hi).exists_generic_transverse_branch_equations hi p hp

end PointedMapGerm

end OnLeConjecture.Analytic
