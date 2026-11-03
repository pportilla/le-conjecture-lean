/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ProjectiveExceptionalIntersectionBound
public import OnLeConjecture.Analytic.WeakBlowupFiniteColength
public import OnLeConjecture.Analytic.GenericFiniteGermFamilyChoice

/-!
# Polynomial exceptional restrictions for analytic generators

Membership in an ordinary maximal-ideal power constructs a polynomial
for each generator, including generators of strictly larger order.
The same polynomial controls the restrictions in all finite blowup
charts. At least one polynomial is nonzero when the ideal has the
specified exact order. Linear combinations retain their original
coefficient row throughout this construction.
-/

public section

namespace OnLeConjecture.Analytic.Germ

open _root_.Polynomial
open scoped BigOperators

/-- Evaluation at the origin of a translated polynomial restriction
is evaluation of the polynomial at the chart center. -/
theorem value_oneVariablePolynomialEvaluation_translation (P : ℂ[X]) (c : ℂ) :
    valueRingHom 1 (oneVariablePolynomialEvaluation (P.comp (X + C c))) = P.eval c := by
  have heval : oneVariablePolynomialEvaluation (P.comp (X + C c)) =
      aeval (coordinate (0 : Fin 1) + constRingHom 1 c) P := by
    simp [oneVariablePolynomialEvaluation, aeval_def, eval₂_comp,
      show algebraMap ℂ (Germ 1) = constRingHom 1 from rfl]
  rw [heval, value_translated_polynomial_aeval]

/-- The zeros of a polynomial exceptional restriction are exactly the
chart centers where its analytic equation vanishes. Zero polynomials
are allowed. -/
theorem mem_maximalIdeal_iff_exceptional_polynomial_root
    (f : Germ 2) (P : ℂ[X]) (c : ℂ)
    (hrestriction : pointBlowupExceptionalLine.pullbackRingHom f =
      oneVariablePolynomialEvaluation (P.comp (X + C c))) :
    f ∈ maximalIdeal 2 ↔ P.IsRoot c := by
  have hvalue := congrArg (valueRingHom 1) hrestriction
  rw [PointedMapGerm.valueRingHom_pullback,
    value_oneVariablePolynomialEvaluation_translation] at hvalue
  rw [mem_maximalIdeal_iff, Polynomial.IsRoot, hvalue]

/-- A nonzero exceptional restriction forces the original germ to
have exactly the order divided out in constructing its strict transform. -/
theorem not_mem_succ_of_pointBlowupTransform_exceptionalRestriction_ne_zero
    (c : ℂ) (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m)
    (hne : pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f hf) ≠ 0) :
    f ∉ maximalIdeal 2 ^ (m + 1) := by
  intro hnext
  have htransform : pointBlowupTransform c m f hf =
      coordinate (1 : Fin 2) * pointBlowupTransform c (m + 1) f hnext := by
    apply pointBlowupTransform_unique c m f _ _ (pointBlowupTransform_factor c m f hf)
    rw [pointBlowupTransform_factor c (m + 1) f hnext, pow_succ]
    ring
  apply hne
  rw [htransform, map_mul, pointBlowupExceptionalLine_pullback_one, zero_mul]

/-- Every germ in the `m`th maximal-ideal power has polynomial
exceptional restrictions of degree at most `m`. Its polynomial may be zero. -/
theorem exists_exceptional_restriction_polynomial_of_mem
    (m : ℕ) (f : Germ 2) (hf : f ∈ maximalIdeal 2 ^ m) :
    ∃ P : ℂ[X], P.natDegree ≤ m ∧ ∀ c : ℂ,
      pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m f hf) =
        oneVariablePolynomialEvaluation (P.comp (X + C c)) := by
  have hfweight : f ∈ weightedOrderIdeal 1 m := by
    simpa only [weightedOrderIdeal_one_eq_maximalIdeal_pow] using hf
  obtain ⟨a, ha⟩ := (mem_weightedOrderIdeal_iff 1 m f).mp hfweight
  refine ⟨∑ k : Fin (m + 1), C (valueRingHom 2 (a k)) * X ^ k.val, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (by simpa only [natDegree_X_pow] using (show k.val ≤ m by omega))
  · exact exceptional_restriction_of_generator_expansion m f hf a ha

/-- Actual analytic generators determine a common polynomial family,
with at least one nonzero member whenever one generator has exact order. -/
theorem exists_exceptional_restriction_polynomial_family
    {ι : Type*} (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m)
    (hexact : ∃ i, F i ∉ maximalIdeal 2 ^ (m + 1)) :
    ∃ P : ι → ℂ[X],
      (∀ i, (P i).natDegree ≤ m) ∧ (∃ i, P i ≠ 0) ∧
      ∀ (i : ι) (c : ℂ),
        pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m (F i) (hF i)) =
          oneVariablePolynomialEvaluation ((P i).comp (X + C c)) := by
  choose P hdegree hrestriction using
    fun i => exists_exceptional_restriction_polynomial_of_mem m (F i) (hF i)
  refine ⟨P, hdegree, ?_, hrestriction⟩
  obtain ⟨i, hi⟩ := hexact
  refine ⟨i, ?_⟩
  have hne := pointBlowupTransform_exceptionalRestriction_ne_zero 0 m (F i)
    (pointBlowupTransform 0 m (F i) (hF i)) (hF i) hi
    (pointBlowupTransform_factor 0 m (F i) (hF i))
  intro hz
  apply hne
  rw [hrestriction i 0, hz, zero_comp, map_zero]

/-- Exceptional division commutes with constant linear combinations
because the exceptional coordinate power is a common nonzero factor. -/
theorem pointBlowupTransform_linearCombination
    {ι : Type*} [Fintype ι] (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) (q : ι → ℂ) (c : ℂ) :
    pointBlowupTransform c m (germLinearCombination F q)
      (germLinearCombination_mem _ _ hF q) =
      germLinearCombination (fun i => pointBlowupTransform c m (F i) (hF i)) q := by
  apply pointBlowupTransform_unique c m (germLinearCombination F q) _ _
    (pointBlowupTransform_factor c m _ (germLinearCombination_mem _ _ hF q))
  simp only [germLinearCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    PointedMapGerm.pullback_complex_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pointBlowupTransform_factor c m (F i) (hF i)]
  exact (mul_smul_comm _ _ _).symm

/-- The polynomial restriction of a linear combination uses precisely
the same coefficient row as the original analytic generators. -/
theorem exceptional_restriction_linearCombination
    {ι : Type*} [Fintype ι] (m : ℕ) (F : ι → Germ 2)
    (hF : ∀ i, F i ∈ maximalIdeal 2 ^ m) (P : ι → ℂ[X])
    (hP : ∀ (i : ι) (c : ℂ),
      pointBlowupExceptionalLine.pullbackRingHom (pointBlowupTransform c m (F i) (hF i)) =
        oneVariablePolynomialEvaluation ((P i).comp (X + C c)))
    (q : ι → ℂ) (c : ℂ) :
    pointBlowupExceptionalLine.pullbackRingHom
      (pointBlowupTransform c m (germLinearCombination F q)
        (germLinearCombination_mem _ _ hF q)) =
      oneVariablePolynomialEvaluation ((∑ i, C (q i) * P i).comp (X + C c)) := by
  rw [pointBlowupTransform_linearCombination m F hF q c]
  simp only [germLinearCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
    PointedMapGerm.pullback_complex_smul, hP, sum_comp, mul_comp, C_comp,
    oneVariablePolynomialEvaluation, map_mul, aeval_C]
  apply Finset.sum_congr rfl
  intro i _
  exact Algebra.smul_def _ _

end OnLeConjecture.Analytic.Germ
