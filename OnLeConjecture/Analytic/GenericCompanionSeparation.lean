/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.GenericFiniteCompanion
public import OnLeConjecture.Analytic.RawWeakBlowupGenericCompleteness
public import OnLeConjecture.Polynomial.GenericCommonZeroCompanion

/-!
# Companions whose common transforms are recorded

For a fixed member of exact ideal order, a common coefficient row can be
chosen so that every common zero of the two strict transforms is a common
zero of the weak generators. The construction works in both projective
charts and at every vertex of a finite weak-blowup tree. The companion
can also have the exact ideal orders and finite local intersections.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

/-- Every common exceptional zero of a fixed exact-order member and a
companion in a constructed open set is a weak-ideal basepoint. -/
theorem exists_open_companion_transforms_common_zero
    {κ ι : Type*} [Finite κ] [Fintype ι]
    (F : κ → ι → Germ 2) (m : κ → ℕ)
    (hF : ∀ k i, F k i ∈ maximalIdeal 2 ^ m k)
    (q : ι → ℂ)
    (hq : ∀ k, germLinearCombination (F k) q ∉ maximalIdeal 2 ^ (m k + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ r ∈ V, ∀ k c,
        pointBlowupTransform c (m k) (germLinearCombination (F k) q)
          (germLinearCombination_mem _ _ (hF k) q) ∈ maximalIdeal 2 →
        pointBlowupTransform c (m k) (germLinearCombination (F k) r)
          (germLinearCombination_mem _ _ (hF k) r) ∈ maximalIdeal 2 →
        ∀ i, pointBlowupTransform c (m k) (F k i) (hF k i) ∈ maximalIdeal 2 := by
  classical
  choose P hdegree hrestriction using fun k i =>
    exists_exceptional_restriction_polynomial_of_mem (m k) (F k i) (hF k i)
  have hlinear (k : κ) (r : ι → ℂ) (c : ℂ) :
      pointBlowupExceptionalLine.pullbackRingHom
        (pointBlowupTransform c (m k) (germLinearCombination (F k) r)
          (germLinearCombination_mem _ _ (hF k) r)) =
        oneVariablePolynomialEvaluation
          ((OnLeConjecture.Polynomial.polynomialLinearCombination (P k) r).comp (X + C c)) := by
    simpa only [OnLeConjecture.Polynomial.polynomialLinearCombination,
      LinearMap.coe_mk, AddHom.coe_mk, smul_eq_C_mul] using
      exceptional_restriction_linearCombination (m k) (F k) (hF k) (P k)
        (hrestriction k) r c
  have hnonzero (k : κ) :
      OnLeConjecture.Polynomial.polynomialLinearCombination (P k) q ≠ 0 := by
    have hn := pointBlowupTransform_exceptionalRestriction_ne_zero 0 (m k)
      (germLinearCombination (F k) q)
      (pointBlowupTransform 0 (m k) _ (germLinearCombination_mem _ _ (hF k) q))
      (germLinearCombination_mem _ _ (hF k) q) (hq k)
      (pointBlowupTransform_factor _ _ _ (germLinearCombination_mem _ _ (hF k) q))
    intro hz
    apply hn
    rw [hlinear, hz, zero_comp, map_zero]
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    OnLeConjecture.Polynomial.exists_open_companion_common_zeros
      (fun k => OnLeConjecture.Polynomial.polynomialLinearCombination (P k) q)
      hnonzero P U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro r hr k c hqzero hrzero i
  apply (mem_maximalIdeal_iff_exceptional_polynomial_root _ _ _ (hrestriction k i c)).mpr
  apply hV r hr k c
  · exact (mem_maximalIdeal_iff_exceptional_polynomial_root _ _ _ (hlinear k q c)).mp hqzero
  · exact (mem_maximalIdeal_iff_exceptional_polynomial_root _ _ _ (hlinear k r c)).mp hrzero

end OnLeConjecture.Analytic.Germ

namespace OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree

open OnLeConjecture.Analytic.Germ

variable {ι : Type*} [Fintype ι] {F : ι → Germ 2}

/-- All common transforms of a fixed exact-order member and any companion
in one nonempty open coefficient set occur at recorded children. -/
theorem exists_open_companion_common_zero_complete
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ V : Set (ι → ℂ), IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
      ∀ r ∈ V, ∀ (p : T.Vertex) (t : Option ℂ) (H K : Germ 2),
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) q)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * H →
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) r)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * K →
        H ∈ maximalIdeal 2 → K ∈ maximalIdeal 2 →
        ∃ v, v ≠ T.root ∧ T.predecessor v = p ∧ T.chartPoint v = t := by
  classical
  let e : Bool → PointedEquivGerm 2 := fun b =>
    if b then coordinateSwapPointedEquiv (1 : Fin 2) else PointedEquivGerm.identity 2
  let A : T.Vertex × Bool → ι → Germ 2 := fun k i =>
    (e k.2).forward.pullbackRingHom (T.generators k.1 i)
  let m : T.Vertex × Bool → ℕ := fun k => T.multiplicity k.1
  have hA (k : T.Vertex × Bool) (i : ι) : A k i ∈ maximalIdeal 2 ^ m k :=
    (e k.2).forward.pullback_mem_maximalIdeal_pow (T.generator_mem k.1 i)
  have hmember (s : ι → ℂ) (p : T.Vertex) (b : Bool) :
      germLinearCombination (A (p, b)) s =
      (e b).forward.pullbackRingHom (germLinearCombination (T.generators p) s) := by
    rw [pullback_germLinearCombination]
  have hqA (k : T.Vertex × Bool) :
      germLinearCombination (A k) q ∉ maximalIdeal 2 ^ (m k + 1) := by
    rw [hmember]
    exact fun h => hq k.1 (((e k.2).pullback_mem_maximalIdeal_pow_iff _).mp h)
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    exists_open_companion_transforms_common_zero A m hA q hqA U hU hUne
  refine ⟨V, hVopen, hVne, hVU, ?_⟩
  intro r hr p t H K hH hK hHz hKz
  have hcommon (b : Bool) (c : ℂ)
      (hHb : (pointBlowupChartGerm c).pullbackRingHom
        (germLinearCombination (A (p, b)) q) = coordinate (1 : Fin 2) ^ m (p, b) * H)
      (hKb : (pointBlowupChartGerm c).pullbackRingHom
        (germLinearCombination (A (p, b)) r) = coordinate (1 : Fin 2) ^ m (p, b) * K) :
      ∀ i, pointBlowupTransform c (m (p, b)) (A (p, b) i) (hA (p, b) i) ∈
        maximalIdeal 2 := by
    apply hV r hr (p, b) c
    · have heq := pointBlowupTransform_unique c (m (p, b))
        (germLinearCombination (A (p, b)) q) _ H
        (pointBlowupTransform_factor _ _ _ (germLinearCombination_mem _ _ (hA (p, b)) q)) hHb
      exact heq.symm ▸ hHz
    · have heq := pointBlowupTransform_unique c (m (p, b))
        (germLinearCombination (A (p, b)) r) _ K
        (pointBlowupTransform_factor _ _ _ (germLinearCombination_mem _ _ (hA (p, b)) r)) hKb
      exact heq.symm ▸ hKz
  apply T.realizes_common_zero p t
  intro i
  cases t with
  | none =>
      have h := hcommon true 0 (by
        rw [hmember]
        simpa only [e, ↓reduceIte, m, projectiveChartCenter, projectiveChartSource] using hH)
        (by
          rw [hmember]
          simpa only [e, ↓reduceIte, m, projectiveChartCenter, projectiveChartSource] using hK) i
      simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
        A, e, ↓reduceIte, m] using h
  | some c =>
      have h := hcommon false c (by
        rw [hmember]
        simpa only [e, Bool.false_eq_true, ↓reduceIte, m,
          projectiveChartCenter, projectiveChartSource] using hH)
        (by
          rw [hmember]
          simpa only [e, Bool.false_eq_true, ↓reduceIte, m,
            projectiveChartCenter, projectiveChartSource] using hK) i
      simpa only [projectiveWeakGenerators, projectiveChartCenter, projectiveChartSource,
        A, e, Bool.false_eq_true, ↓reduceIte, m] using h

/-- A companion in any prescribed nonempty open set has exact orders,
finite intersections, and no common transform outside the recorded tree. -/
theorem exists_exact_finite_companion_common_zero_complete
    (T : RawProjectiveWeakBlowupTree F) (q : ι → ℂ)
    (hq : ∀ p, germLinearCombination (T.generators p) q ∉
      maximalIdeal 2 ^ (T.multiplicity p + 1))
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ r ∈ U,
      (∀ p, germLinearCombination (T.generators p) r ∉
        maximalIdeal 2 ^ (T.multiplicity p + 1)) ∧
      (∀ p, PlaneCurve.HasFiniteIntersection
        (germLinearCombination (T.generators p) q)
        (germLinearCombination (T.generators p) r)) ∧
      ∀ (p : T.Vertex) (t : Option ℂ) (H K : Germ 2),
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) q)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * H →
        (pointBlowupChartGerm (projectiveChartCenter t)).pullbackRingHom
          ((projectiveChartSource t).forward.pullbackRingHom
            (germLinearCombination (T.generators p) r)) =
              coordinate (1 : Fin 2) ^ T.multiplicity p * K →
        H ∈ maximalIdeal 2 → K ∈ maximalIdeal 2 →
        ∃ v, v ≠ T.root ∧ T.predecessor v = p ∧ T.chartPoint v = t := by
  obtain ⟨V, hVopen, hVne, hVU, hV⟩ :=
    T.exists_open_companion_common_zero_complete q hq U hU hUne
  obtain ⟨r, hrV, hrexact, hrfinite⟩ :=
    T.exists_exact_finite_companion q hq V hVopen hVne
  exact ⟨r, hVU hrV, hrexact, hrfinite, hV r hrV⟩

end OnLeConjecture.Analytic.RawProjectiveWeakBlowupTree
