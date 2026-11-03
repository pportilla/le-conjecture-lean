/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FixedTangentGenericAvoidance
public import OnLeConjecture.Analytic.GenericPointBasisOpenChoice

/-!
# Fixed tangent avoidance in a prescribed open set

The directions in this statement are fixed before the coefficient vector
is chosen. Exact orders and tangent avoidance can be imposed inside any
nonempty open set of coefficient vectors.
-/

public section

namespace OnLeConjecture.Analytic.WeakTransformIdealData

open OnLeConjecture.Analytic.Germ

theorem exists_coefficients_exact_orders_tangent_avoidance_mem_open
    {N : ℕ} {c : AnalyticPointBasis N} {ι κ : Type*} [Fintype ι] [Finite κ]
    (d : WeakTransformIdealData c ι) (directions : κ → ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      ∀ j, d.AvoidsRootTangentCancellation q (directions j) := by
  classical
  let K := {j : κ // d.rootWeakValueLinearForm (directions j) ≠ 0}
  obtain ⟨q, hqU, horder, havoid⟩ :=
    d.exists_coefficients_exact_orders_linear_conditions_mem_open
      (fun j : K => d.rootWeakValueLinearForm (directions j.1)) (fun j => j.2) U hU hUne
  refine ⟨q, hqU, horder, ?_⟩
  intro j
  by_cases hz : d.rootWeakValueLinearForm (directions j) = 0
  · exact Or.inl hz
  · exact Or.inr (havoid ⟨j, hz⟩)

/-- In particular, the tangent of one fixed critical equation can be
avoided while retaining all properties supplied on the open set. -/
theorem exists_coefficients_exact_orders_fixed_tangent_mem_open
    {N : ℕ} {c : AnalyticPointBasis N} {ι : Type*} [Fintype ι]
    (d : WeakTransformIdealData c ι) (ζ : ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ q ∈ U,
      (∀ p, germLinearCombination (d.generators p) q ∈ maximalIdeal 2 ^ c.multiplicity p ∧
        germLinearCombination (d.generators p) q ∉ maximalIdeal 2 ^ (c.multiplicity p + 1)) ∧
      d.AvoidsRootTangentCancellation q ζ := by
  obtain ⟨q, hqU, horder, havoid⟩ :=
    d.exists_coefficients_exact_orders_tangent_avoidance_mem_open
      (fun _ : Unit => ζ) U hU hUne
  exact ⟨q, hqU, horder, havoid ()⟩

end OnLeConjecture.Analytic.WeakTransformIdealData
