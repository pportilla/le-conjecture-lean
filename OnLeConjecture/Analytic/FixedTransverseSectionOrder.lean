/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FixedTransverseCoordinates
public import OnLeConjecture.Analytic.CriticalComponentTransverseMultiplicity
public import OnLeConjecture.Analytic.ReducedMemberCriticalIntersection

/-!
# Transverse branch order for a prescribed target coordinate

The target coordinate is fixed before choosing a point of the critical
component. Its nonzero restriction to that component proves transversality
throughout a punctured neighborhood. The previously constructed common
Jacobian factors then give the exact multiplicity of the plane image branch.

This does not yet choose all points in a single nonzero level of that
coordinate, or count those points. Those are separate remaining steps.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

/-- The common-power construction with the transverse coordinate prescribed
in advance, rather than selected separately at each point. -/
theorem eventually_fixed_transverse_section_of_exact_common_power
    (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (S : Set (Source 2)) (hS : S ∈ 𝓝 0) (hinj : InjOn G S)
    (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
    (hp : Irreducible (Germ.ofFunction P hP)) (k : ℕ)
    (hdiv : ∀ i j : Fin 3, Germ.ofFunction P hP ^ k ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (hexact : ∃ i j : Fin 3, ¬ Germ.ofFunction P hP ^ (k + 1) ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component i)
        ((PointedMapGerm.ofFunction G hG hG0).1.component j))
    (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0)
    (hker : ∀ h : Germ 2,
      (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ Germ.ofFunction P hP ∣ h)
    (i : Fin 3)
    (hnot : ¬ Germ.ofFunction P hP ∣ (PointedMapGerm.ofFunction G hG hG0).1.component i) :
    ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t))
        (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2),
        P (C t) = 0 ∧
        e.forward.pullbackRingHom ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component i) =
          coordinate 0 ∧
        e.forward.pullbackRingHom (Germ.ofFunctionAt P (C t) hPt) = coordinate 1 ∧
        (hyperplaneInclusionGerm 2).comp β =
          ((coordinateSwapPointedEquiv i).forward.comp
            (PointedMapGerm.recenterOfFunction G (C t) hGt)).comp
              (e.forward.comp (hyperplaneInclusionGerm 1)) ∧
        β.HasInjectiveRepresentative ∧
        min (vanishingOrder (β.1.component 0)) (vanishingOrder (β.1.component 1)) =
          (k + 1 : ℕ) := by
  have ht := PointedMapGerm.eventually_rebased_fixed_component_curve_jacobian_unit
    G hG hG0 P hP hp C hC hC0 hker i hnot
  have hchoice : ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
      ∃ (hGt : AnalyticAt ℂ G (C t)) (hPt : AnalyticAt ℂ P (C t)),
        P (C t) = 0 ∧ ∃ j : Fin 3, j = i ∧
          IsUnit (jacobian ((PointedMapGerm.recenterOfFunction G (C t) hGt).1.component j)
            (Germ.ofFunctionAt P (C t) hPt)) := by
    filter_upwards [ht] with t ht htn
    obtain ⟨hGt, hPt, hP0, hi⟩ := ht htn
    exact ⟨hGt, hPt, hP0, i, rfl, hi⟩
  have h := eventually_exists_transverse_section_preserving_coordinate_property
    G hG hG0 S hS hinj P hP hp k hdiv hexact C hC hC0 hker (fun j => j = i) hchoice
  filter_upwards [h] with t ht htn
  obtain ⟨hGt, hPt, j, e, β, rfl, hrest⟩ := ht htn
  exact ⟨hGt, hPt, e, β, hrest⟩

/-- A transverse image branch whose section coordinate is specified. -/
def FixedTransverseBranchEquationAt (G : Source 2 → Source 3) (P : Source 2 → ℂ)
    (i : Fin 3) (x : Source 2) (m : ℕ) : Prop :=
  ∃ (hGx : AnalyticAt ℂ G x) (hPx : AnalyticAt ℂ P x)
    (e : PointedEquivGerm 2) (β : PointedMapGerm 1 2) (f : Germ 2),
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

/-- A reduced coordinate section cannot contain a critical component of
an injective map. Thus the fixed-coordinate transversality condition follows
from the squarefreeness already supplied by the generic section. -/
theorem not_dvd_squarefree_component
    {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)
    (hi : g.HasInjectiveRepresentative) (p : Germ 2) (hp : p ∈ D.support)
    (i : Fin 3) (hsq : Squarefree (g.1.component i)) : ¬ p ∣ g.1.component i := by
  intro hpf
  have hall (j : Fin 3) : p ∣ g.1.component j :=
    dvd_of_prime_dvd_reduced_and_jacobian (g.1.component i) (g.1.component j) p hsq
      (g.coordinateIdeal_le_maximalIdeal (g.1.component_mem_coordinateIdeal j))
      (D.irreducible p hp).prime hpf
      ((dvd_pow_self p (D.order_pos p hp).ne').trans (D.pow_dvd_minors p hp i j))
  obtain ⟨N, hN⟩ := g.exists_maximalIdeal_pow_le_coordinateIdeal
    (g.injective_isFiniteAtOrigin_two hi)
  apply not_maximalIdeal_pow_le_span_singleton p (D.component_mem p hp)
  refine ⟨N, hN.trans ?_⟩
  rw [MapGerm.coordinateIdeal_le]
  exact fun j => Ideal.mem_span_singleton.mpr (hall j)

/-- The factor multiplicity is realized by every sufficiently nearby
transverse branch in the same chosen coordinate direction. -/
theorem exists_fixed_transverse_branch_equations
    {g : PointedMapGerm 2 3} (D : CriticalJacobianFactorization g)
    (hi : g.HasInjectiveRepresentative) (p : Germ 2) (hp : p ∈ D.support)
    (i : Fin 3) (hsq : Squarefree (g.1.component i)) :
    ∃ (G : Source 2 → Source 3) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
      (P : Source 2 → ℂ) (hP : AnalyticAt ℂ P 0)
      (C : Source 1 → Source 2) (hC : AnalyticAt ℂ C 0) (hC0 : C 0 = 0),
      g = PointedMapGerm.ofFunction G hG hG0 ∧ p = Germ.ofFunction P hP ∧
      (PointedMapGerm.ofFunction C hC hC0).HasInjectiveRepresentative ∧
      (∀ h : Germ 2,
        (PointedMapGerm.ofFunction C hC hC0).pullbackRingHom h = 0 ↔ p ∣ h) ∧
      ∀ᶠ t in 𝓝 (0 : Source 1), t ≠ 0 →
        FixedTransverseBranchEquationAt G P i (C t) (D.order p + 1) := by
  have hnot := D.not_dvd_squarefree_component hi p hp i hsq
  obtain ⟨G, hG, hG0, hg, S, hS, hinj⟩ := hi
  obtain ⟨P, hP, hpP⟩ := exists_analyticRepresentative_allOrders p
  obtain ⟨γ, hγinj, _, hker⟩ :=
    exists_injective_parametrization_with_kernel_of_irreducible p (D.irreducible p hp)
  obtain ⟨C, hC, hC0, hγ⟩ := γ.exists_ofFunction
  rw [hγ] at hγinj hker
  have hdiv (a b : Fin 3) : Germ.ofFunction P hP ^ D.order p ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component a)
        ((PointedMapGerm.ofFunction G hG hG0).1.component b) := by
    simpa only [← hpP, ← hg] using D.pow_dvd_minors p hp a b
  have hexact : ∃ a b : Fin 3, ¬ Germ.ofFunction P hP ^ (D.order p + 1) ∣
      jacobian ((PointedMapGerm.ofFunction G hG hG0).1.component a)
        ((PointedMapGerm.ofFunction G hG hG0).1.component b) := by
    by_contra! h
    have hle := (D.order_maximal p hp (D.order p + 1)).mp
      (by simpa only [hpP, hg] using h)
    omega
  have hnot' : ¬ Germ.ofFunction P hP ∣
      (PointedMapGerm.ofFunction G hG hG0).1.component i := by
    simpa only [← hg, ← hpP] using hnot
  have ht := eventually_fixed_transverse_section_of_exact_common_power
    G hG hG0 S hS hinj P hP (hpP ▸ D.irreducible p hp) (D.order p) hdiv hexact
    C hC hC0 (by simpa only [← hpP] using hker) i hnot'
  refine ⟨G, hG, hG0, P, hP, C, hC, hC0, hg, hpP, hγinj, hker, ?_⟩
  filter_upwards [ht] with t ht htn
  obtain ⟨hGt, hPt, e, β, hP0, he, hep, hβ, hβinj, horder⟩ := ht htn
  obtain ⟨f, hirr, hzero, hkernel, hf, hnext⟩ :=
    β.exists_irreducible_image_equation_of_order hβinj (D.order p + 1) horder
  exact ⟨hGt, hPt, e, β, f, hP0, he, hep, hβ, hβinj, hirr, hzero,
    hkernel, horder, hf, hnext⟩

end CriticalJacobianFactorization

end OnLeConjecture.Analytic
