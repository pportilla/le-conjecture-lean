/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ReducedSectionImage
public import OnLeConjecture.Analytic.PlaneProductOrder
public import OnLeConjecture.Analytic.InjectiveCurveMultiplicity

/-!
# Multiplicity of the reduced section image

Each image branch has a positive order equal to the minimum component
order of its injective normalization. The sum of these orders is the
exact maximal-ideal order of the constructed reduced plane image equation.
-/

public noncomputable section

open scoped BigOperators

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

namespace PointedMapGerm

theorem sectionBranch_component (g : PointedMapGerm 2 3)
    (γ : PointedMapGerm 1 2) (i : Fin 2) :
    (g.sectionBranch γ).1.component i = γ.pullbackRingHom (g.1.component i.succ) := by
  have htail : (hyperplaneTailGerm 2).1.component i = coordinate i.succ := by
    apply Subtype.ext
    rfl
  rw [sectionBranch, component_comp_eq_pullback, htail, pullback_coordinate,
    component_comp_eq_pullback]

theorem sectionBranch_min_component_order (g : PointedMapGerm 2 3)
    (γ : PointedMapGerm 1 2) (hz : γ.pullbackRingHom (g.1.component 0) = 0) :
    (⨅ i : Fin 3, vanishingOrder (γ.pullbackRingHom (g.1.component i))) =
      min (vanishingOrder ((g.sectionBranch γ).1.component 0))
        (vanishingOrder ((g.sectionBranch γ).1.component 1)) := by
  rw [sectionBranch_component, sectionBranch_component]
  apply le_antisymm
  · exact le_min (iInf_le _ 1) (iInf_le _ 2)
  · apply le_iInf
    intro i
    fin_cases i
    · change _ ≤ vanishingOrder (γ.pullbackRingHom (g.1.component 0))
      rw [hz, vanishingOrder_zero]
      exact le_top
    · exact min_le_left _ _
    · exact min_le_right _ _

end PointedMapGerm

namespace SectionImageFactorization

variable {g : PointedMapGerm 2 3} (D : SectionImageFactorization g)

/-- Branch multiplicities and the total image multiplicity are constructed
from the irreducible image equations. All component orders use the same
source branch normalizations. -/
theorem exists_image_branch_orders (hg : g.HasInjectiveRepresentative) :
    ∃ m : D.branches → ℕ,
      (∀ i, 0 < m i ∧ D.equation i ∈ maximalIdeal 2 ^ m i ∧
        D.equation i ∉ maximalIdeal 2 ^ (m i + 1) ∧
        (⨅ j : Fin 3, vanishingOrder
          ((D.parametrization i).pullbackRingHom (g.1.component j))) = m i) ∧
      D.imageEquation ∈ maximalIdeal 2 ^ (∑ i, m i) ∧
      D.imageEquation ∉ maximalIdeal 2 ^ ((∑ i, m i) + 1) := by
  classical
  choose m hm hnext using fun i : D.branches =>
    exists_exact_maximalIdeal_order_of_ne_zero (D.equation i) (D.imageIrreducible i).ne_zero
  refine ⟨m, ?_, exact_maximalIdeal_order_finset_prod Finset.univ D.equation m
    (fun i _ => hm i) (fun i _ => hnext i)⟩
  intro i
  have hmem : D.equation i ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff,
      ← (g.sectionBranch (D.parametrization i)).valueRingHom_pullback (D.equation i),
      D.imageAnnihilates i, map_zero]
  refine ⟨?_, hm i, hnext i, ?_⟩
  · by_contra hn
    have hz : m i = 0 := by omega
    exact hnext i (by simpa only [hz, zero_add, pow_one] using hmem)
  · rw [g.sectionBranch_min_component_order _ (D.section_zero i)]
    exact PointedMapGerm.min_component_orders_eq_equation_order_of_injective_curve
      (g.sectionBranch (D.parametrization i))
        (D.image_injective hg i) _ (D.imageIrreducible i) (D.imageAnnihilates i)
        (m i) (hm i) (hnext i)

/-- A companion attaining the minimum order on every normalization computes
the exact multiplicity of the constructed image equation. -/
theorem imageEquation_exact_order_of_minimum
    (hg : g.HasInjectiveRepresentative) (q : Germ 2)
    (hfinite : PlaneCurve.HasFiniteIntersection (g.1.component 0)
      (g.pullbackRingHom (hyperplaneExtension 2 q)))
    (hminimum : ∀ i : D.branches,
      vanishingOrder ((D.parametrization i).pullbackRingHom
        (g.pullbackRingHom (hyperplaneExtension 2 q))) =
          ⨅ j : Fin 3, vanishingOrder
            ((D.parametrization i).pullbackRingHom (g.1.component j))) :
    D.imageEquation ∈ maximalIdeal 2 ^
        PlaneCurve.intersectionMultiplicity (g.1.component 0)
          (g.pullbackRingHom (hyperplaneExtension 2 q)) hfinite ∧
      D.imageEquation ∉ maximalIdeal 2 ^
        (PlaneCurve.intersectionMultiplicity (g.1.component 0)
          (g.pullbackRingHom (hyperplaneExtension 2 q)) hfinite + 1) := by
  obtain ⟨m, hm, hW, hWnext⟩ := D.exists_image_branch_orders hg
  have himage := (D.intersection_finite_iff hg q).mpr hfinite
  have hbranches (i : D.branches) : PlaneCurve.HasFiniteIntersection (D.equation i) q :=
    (PlaneCurve.hasFiniteIntersection_finset_prod_left_iff _ _ _).mp himage i
      (Finset.mem_univ i)
  have horder (i : D.branches) :
      PlaneCurve.intersectionMultiplicity (D.equation i) q (hbranches i) = m i := by
    rw [D.branch_intersection_eq hg i q (hbranches i)
      ((D.branch_intersection_finite_iff hg i q).mp (hbranches i)),
      (D.parametrization i).intersectionMultiplicity_eq_pullback_order_of_injective_curve
        (D.parametrizationInjective i) _ (D.sourceIrreducible i) (D.sourceAnnihilates i)]
    rw [hminimum i, (hm i).2.2.2]
    rfl
  have hsum : PlaneCurve.intersectionMultiplicity (g.1.component 0)
      (g.pullbackRingHom (hyperplaneExtension 2 q)) hfinite = ∑ i, m i := by
    rw [← D.intersection_eq hg q himage hfinite]
    change PlaneCurve.intersectionMultiplicity (∏ i, D.equation i) q himage = _
    rw [PlaneCurve.intersectionMultiplicity_finset_prod_left _ _ _ hbranches himage]
    exact Finset.sum_congr rfl fun i _ => horder i
  rw [hsum]
  exact ⟨hW, hWnext⟩

end SectionImageFactorization
end OnLeConjecture.Analytic
