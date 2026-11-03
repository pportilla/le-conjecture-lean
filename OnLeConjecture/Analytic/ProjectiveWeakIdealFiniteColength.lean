/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.WeakBlowupCoordinateTransport
public import OnLeConjecture.Analytic.FiniteIdealRegularCoordinates

/-!
# Finite colength and order in both projective weak charts

Finiteness and the weak-order bound hold in either chart, without a
transversality assumption. At a proper weak ideal its positive exact
order and an attaining generator are constructed from finite colength.
-/

public section

namespace OnLeConjecture.Analytic.Germ

theorem pullback_generatorIdeal_quotient_moduleFinite
    {ι : Type*} (e : PointedEquivGerm 2) (F : ι → Germ 2)
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F))) :
    Module.Finite ℂ (Germ 2 ⧸
      Ideal.span (Set.range (fun i => e.forward.pullbackRingHom (F i)))) := by
  apply (quotient_moduleFinite_iff_of_map_eq _ _ e.pullbackAlgEquiv ?_).mp hfinite
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem projectiveWeakIdeal_quotient_moduleFinite
    {ι : Type*} [Finite ι] (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, F i ∉ maximalIdeal 2 ^ (m + 1))
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (t : Option ℂ) :
    Module.Finite ℂ (Germ 2 ⧸
      Ideal.span (Set.range (projectiveWeakGenerators m F hF t))) := by
  apply weakIdeal_quotient_moduleFinite (projectiveChartCenter t) m
    (fun i => (projectiveChartSource t).forward.pullbackRingHom (F i)) _
    (pullback_generatorIdeal_quotient_moduleFinite (projectiveChartSource t) F hfinite)
    (fun i => (projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow (hF i))
  · obtain ⟨i, hi⟩ := hexact
    exact ⟨i, fun h => hi (((projectiveChartSource t).pullback_mem_maximalIdeal_pow_iff _).mp h)⟩
  · intro i
    exact pointBlowupTransform_factor (projectiveChartCenter t) m _ _

theorem exists_projectiveWeakIdeal_exact_order
    {ι : Type*} [Finite ι] (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, F i ∉ maximalIdeal 2 ^ (m + 1))
    (hfinite : Module.Finite ℂ (Germ 2 ⧸ Ideal.span (Set.range F)))
    (t : Option ℂ) (ht : t ∈ projectiveExceptionalBasepointSet m F hF) :
    ∃ k : ℕ, 0 < k ∧ k ≤ m ∧
      (∀ i, projectiveWeakGenerators m F hF t i ∈ maximalIdeal 2 ^ k) ∧
      ∃ i, projectiveWeakGenerators m F hF t i ∉ maximalIdeal 2 ^ (k + 1) := by
  have hweakFinite := projectiveWeakIdeal_quotient_moduleFinite m F hF hexact hfinite t
  obtain ⟨k, hk, horder, hnext⟩ :=
    exists_exact_generator_order_of_finite_colength (projectiveWeakGenerators m F hF t)
      ht hweakFinite
  refine ⟨k, hk, ?_, horder, hnext⟩
  obtain ⟨i, hi⟩ := hexact
  have hi' : (projectiveChartSource t).forward.pullbackRingHom (F i) ∉
      maximalIdeal 2 ^ (m + 1) :=
    fun h => hi (((projectiveChartSource t).pullback_mem_maximalIdeal_pow_iff _).mp h)
  have hweakNext := pointBlowupTransform_order_bound (projectiveChartCenter t) m
    ((projectiveChartSource t).forward.pullbackRingHom (F i))
    ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow (hF i)) hi'
  by_contra hn
  exact hweakNext ((Ideal.pow_le_pow_right (by omega)) (horder i))

end OnLeConjecture.Analytic.Germ
