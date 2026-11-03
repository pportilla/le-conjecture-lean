/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PointBlowupCenters
public import OnLeConjecture.Analytic.RegularBlowupCharts
public import OnLeConjecture.Analytic.TwoChartBlowupLift

/-!
# Finite enumeration of exceptional weak basepoints

An exact-order generator has a nonzero polynomial initial form on the
exceptional line. All common zeros of the constructed weak transforms
belong to its finite root set. Filtering those roots gives the exact
basepoint set, with cardinality at most the ideal order. Neither a
principalization nor an enumeration of its centers is assumed.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial

theorem eval_ordinary_initial_chart (P : MvPolynomial (Fin 2) ℂ) (ζ : ℂ) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P).eval ζ =
      MvPolynomial.eval ![ζ, 1] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ]
  | mul_X P i hP =>
    rw [map_mul, eval_mul, hP, MvPolynomial.eval_mul]
    congr 1
    fin_cases i <;> simp

/-- Common weak-transform zeros on the finite exceptional chart. The
weak transforms are constructed by analytic division by the exceptional
coordinate power. -/
@[expose] def finiteExceptionalBasepointSet
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m) : Set ℂ :=
  {ζ | ∀ i, pointBlowupTransform ζ m (f i) (hf i) ∈ maximalIdeal 2}

/-- The nonzero initial polynomial of one exact-order generator contains
every common exceptional zero among its roots. -/
theorem exists_initial_polynomial_covering_exceptional_basepoints
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ T : ℂ[X], T ≠ 0 ∧ T.natDegree ≤ m ∧
      ∀ ζ ∈ finiteExceptionalBasepointSet m f hf, T.IsRoot ζ := by
  obtain ⟨i, hi⟩ := hexact
  obtain ⟨V, P, T, _hfactor, _hPne, hP, htail, hTchart, hT, hdegree,
    _hrestriction, _hVnext⟩ := exists_pointBlowupTransform_with_initial 0 m (f i) (hf i) hi
  have hchart : T = MvPolynomial.aeval (![X, 1] : Fin 2 → ℂ[X]) P := by
    simpa only [map_zero, C_0, add_zero] using hTchart
  refine ⟨T, hT, hdegree, ?_⟩
  intro ζ hζ
  have hzero := initial_eval_eq_zero_of_vanishing_pointBlowupTransform ζ m (f i)
    (pointBlowupTransform ζ m (f i) (hf i)) P (hf i) hi hP htail
    (pointBlowupTransform_factor ζ m (f i) (hf i)) (hζ i)
  rw [Polynomial.IsRoot, hchart, eval_ordinary_initial_chart]
  exact hzero

/-- Filtering the explicitly obtained polynomial root set enumerates
exactly the common weak basepoints. In particular, there are at most `m`. -/
theorem exists_finiteExceptionalBasepoint_finset
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ s : Finset ℂ, s.card ≤ m ∧
      ∀ ζ, ζ ∈ s ↔ ζ ∈ finiteExceptionalBasepointSet m f hf := by
  classical
  obtain ⟨T, hT, hdegree, hcover⟩ :=
    exists_initial_polynomial_covering_exceptional_basepoints m f hf hexact
  let s := T.roots.toFinset.filter fun ζ => ζ ∈ finiteExceptionalBasepointSet m f hf
  refine ⟨s, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans
      ((Multiset.toFinset_card_le T.roots).trans ((card_roots' T).trans hdegree))
  · intro ζ
    simp only [s, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hT]
    exact ⟨fun h => h.2, fun h => ⟨hcover ζ h, h⟩⟩

theorem finite_finiteExceptionalBasepointSet
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1)) :
    (finiteExceptionalBasepointSet m f hf).Finite := by
  obtain ⟨s, _hcard, hs⟩ := exists_finiteExceptionalBasepoint_finset m f hf hexact
  exact s.finite_toSet.subset (fun ζ hζ => (hs ζ).mpr hζ)

/-- First-axis regularity of one generator rules out a common zero in
the complementary chart, using the actual constructed weak transforms. -/
theorem complementary_not_common_weak_zero_of_regular
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hregular : ∃ i, IsRegularInFirstCoordinateOfOrder (f i) m) :
    ¬ ∀ i, pointBlowupTransform 0 m
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (f i))
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow (hf i))
        ∈ maximalIdeal 2 := by
  intro hzero
  obtain ⟨i, hi⟩ := hregular
  have hfi := (coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullback_mem_maximalIdeal_pow
    (hf i)
  have hunit := complementaryBlowupTransform_isUnit_of_regular m (f i) _ hi
    (pointBlowupTransform_factor 0 m
      ((coordinateSwapPointedEquiv (1 : Fin 2)).forward.pullbackRingHom (f i)) hfi)
  exact (valueRingHom_ne_zero_of_isUnit hunit) (mem_maximalIdeal_iff.mp (hzero i))

/-- Common weak basepoints in the two projective charts. `none` denotes
the single complementary point, not a further affine line. -/
@[expose] def projectiveExceptionalBasepointSet
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m) : Set (Option ℂ) :=
  {t | ∀ i, pointBlowupTransform (projectiveChartCenter t) m
      ((projectiveChartSource t).forward.pullbackRingHom (f i))
      ((projectiveChartSource t).forward.pullback_mem_maximalIdeal_pow (hf i))
        ∈ maximalIdeal 2}

@[simp] theorem some_mem_projectiveExceptionalBasepointSet
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m) (ζ : ℂ) :
    some ζ ∈ projectiveExceptionalBasepointSet m f hf ↔
      ζ ∈ finiteExceptionalBasepointSet m f hf := by
  simp only [projectiveExceptionalBasepointSet, finiteExceptionalBasepointSet,
    Set.mem_ofPred_eq, projectiveChartCenter, projectiveChartSource,
    Analytic.PointedEquivGerm.identity_forward,
    Analytic.PointedMapGerm.pullbackRingHom_identity, RingHom.id_apply]

theorem none_not_mem_projectiveExceptionalBasepointSet_of_regular
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hregular : ∃ i, IsRegularInFirstCoordinateOfOrder (f i) m) :
    none ∉ projectiveExceptionalBasepointSet m f hf :=
  complementary_not_common_weak_zero_of_regular m f hf hregular

/-- An exact finite enumeration in both projective charts. The bound
allows one additional point for the complementary chart. -/
theorem exists_projectiveExceptionalBasepoint_finset
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ s : Finset (Option ℂ), s.card ≤ m + 1 ∧
      ∀ t, t ∈ s ↔ t ∈ projectiveExceptionalBasepointSet m f hf := by
  classical
  obtain ⟨s, hcard, hs⟩ := exists_finiteExceptionalBasepoint_finset m f hf hexact
  let cover := insert none (s.image some)
  let points := cover.filter fun t => t ∈ projectiveExceptionalBasepointSet m f hf
  have hcover : ∀ t ∈ projectiveExceptionalBasepointSet m f hf, t ∈ cover := by
    intro t ht
    cases t with
    | none => exact Finset.mem_insert_self _ _
    | some ζ =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨ζ, (hs ζ).mpr ?_, rfl⟩
      exact (some_mem_projectiveExceptionalBasepointSet m f hf ζ).mp ht
  refine ⟨points, ?_, ?_⟩
  · have hfilter : points.card ≤ cover.card := Finset.card_filter_le _ _
    have hinsert : cover.card ≤ (s.image some).card + 1 := Finset.card_insert_le _ _
    have himage : (s.image some).card ≤ s.card := Finset.card_image_le
    omega
  · intro t
    simp only [points, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hcover t h, h⟩⟩

theorem finite_projectiveExceptionalBasepointSet
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1)) :
    (projectiveExceptionalBasepointSet m f hf).Finite := by
  obtain ⟨s, _hcard, hs⟩ := exists_projectiveExceptionalBasepoint_finset m f hf hexact
  exact s.finite_toSet.subset (fun t ht => (hs t).mpr ht)

/-- With a first-axis regular generator, every projective weak basepoint
is finite and the exact projective enumeration has cardinality at most `m`. -/
theorem exists_projectiveExceptionalBasepoint_finset_of_regular
    {ι : Type*} (m : ℕ) (f : ι → Germ 2)
    (hf : ∀ i, f i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, f i ∉ maximalIdeal 2 ^ (m + 1))
    (hregular : ∃ i, IsRegularInFirstCoordinateOfOrder (f i) m) :
    ∃ s : Finset (Option ℂ), s.card ≤ m ∧ none ∉ s ∧
      ∀ t, t ∈ s ↔ t ∈ projectiveExceptionalBasepointSet m f hf := by
  classical
  obtain ⟨s, hcard, hs⟩ := exists_finiteExceptionalBasepoint_finset m f hf hexact
  refine ⟨s.image some, Finset.card_image_le.trans hcard, ?_, ?_⟩
  · simp
  · intro t
    cases t with
    | none =>
      simp only [Finset.mem_image, Option.some_ne_none, and_false, exists_false,
        false_iff]
      exact none_not_mem_projectiveExceptionalBasepointSet_of_regular m f hf hregular
    | some ζ =>
      simpa only [Finset.mem_image, Option.some.injEq, exists_eq_right,
        some_mem_projectiveExceptionalBasepointSet] using hs ζ

end OnLeConjecture.Analytic.Germ
