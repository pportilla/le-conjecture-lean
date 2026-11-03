/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ThreeVariableBanachExtension
public import OnLeConjecture.Analytic.GeneralFunctionalPreparation

/-!
# Independence of finite analytic division remainders

The remainder projection of a companion endomorphism depends only on the
input remainder, not on the evaluation coordinate. This relation is
preserved by ordered products, homogeneous Taylor coefficients, and
convergent sums.
-/

public section

open scoped BigOperators

namespace OnLeConjecture.Analytic.Germ

section ProjectedProducts

variable {S T : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

/-- Matching endomorphisms preserve equality under a linear projection,
and their ordered products preserve the same relation. -/
theorem projected_list_prod_eq {n : ℕ} (L : S →L[ℂ] T)
    (X Y : Fin n → S →L[ℂ] S)
    (hL : ∀ i s t, L s = L t → L (X i s) = L (Y i t))
    (w : List (Fin n)) (s t : S) (hst : L s = L t) :
    L ((w.map X).prod s) = L ((w.map Y).prod t) := by
  induction w generalizing s t with
  | nil => simpa using hst
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp]
      exact hL i _ _ (ih s t hst)

/-- Projection of each Banach-extended coefficient preserves the same
endomorphism relation. -/
theorem projected_finiteBanachExtensionSeries_eq {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (L : S →L[ℂ] T)
    (X Y : Fin n → S →L[ℂ] S)
    (hL : ∀ i s t, L s = L t → L (X i s) = L (Y i t))
    (d : ℕ) (s t : S) (hst : L s = L t) :
    L (finiteBanachExtensionSeries p d (fun _ => X) s) =
      L (finiteBanachExtensionSeries p d (fun _ => Y) t) := by
  rw [finiteBanachExtensionSeries_apply_diagonal,
    finiteBanachExtensionSeries_apply_diagonal]
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro w _hw
  congr 1
  simpa only [List.map_ofFn, Function.comp_def] using
    projected_list_prod_eq L X Y hL (List.ofFn w) s t hst

/-- Projection of the convergent extension preserves the endomorphism
relation. -/
theorem projected_finiteBanachExtensionSeries_sum_eq [CompleteSpace S] {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source n) ℂ) (L : S →L[ℂ] T)
    (X Y : Fin n → S →L[ℂ] S)
    (hL : ∀ i s t, L s = L t → L (X i s) = L (Y i t))
    (s t : S) (hst : L s = L t)
    (hX : X ∈ Metric.eball 0 (finiteBanachExtensionSeries (A := S →L[ℂ] S) p).radius)
    (hY : Y ∈ Metric.eball 0 (finiteBanachExtensionSeries (A := S →L[ℂ] S) p).radius) :
    L ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).sum X s) =
      L ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).sum Y t) := by
  let es := L.comp (ContinuousLinearMap.apply ℂ S s)
  let et := L.comp (ContinuousLinearMap.apply ℂ S t)
  have hx := es.hasSum ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).hasSum hX)
  have hy := et.hasSum ((finiteBanachExtensionSeries (A := S →L[ℂ] S) p).hasSum hY)
  have hterms : (fun d => es (finiteBanachExtensionSeries p d (fun _ => X))) =
      (fun d => et (finiteBanachExtensionSeries p d (fun _ => Y))) := by
    funext d
    exact projected_finiteBanachExtensionSeries_eq p L X Y hL d s t hst
  rw [hterms] at hx
  exact hx.unique hy

end ProjectedProducts

/-- Companion operators at different evaluation coordinates give equal
remainders whenever their input remainders agree. -/
theorem generalDivisionOperator_remainder_congr {d : ℕ}
    (x y : ℂ) (a : GeneralCoefficientSpace d)
    (s t : GeneralDivisionState d) (hst : s.2 = t.2) :
    (generalDivisionOperator x a s).2 = (generalDivisionOperator y a t).2 := by
  funext i
  induction i using Fin.cases with
  | zero => simp only [generalDivisionOperator_snd_zero, hst]
  | succ i => simp only [generalDivisionOperator_snd_succ, hst]

/-- A scaled companion operator with all retained coordinates acting by
scalar identities. Its coefficients have already been rescaled. -/
@[expose] noncomputable def scaledDivisionInput {n : ℕ} (d : ℕ)
    (c x : ℂ) (y : Source n) (a : GeneralCoefficientSpace d) :
    Fin (n + 1) → GeneralDivisionEndomorphism d :=
  Fin.cases (c • generalDivisionOperator (c⁻¹ * x) a)
    (fun i => y i • (1 : GeneralDivisionEndomorphism d))

/-- Scaled division inputs at different first coordinates preserve
equality of remainders. -/
theorem scaledDivisionInput_remainder_congr {n : ℕ} (d : ℕ)
    (c x z : ℂ) (y : Source n) (a : GeneralCoefficientSpace d)
    (i : Fin (n + 1)) (s t : GeneralDivisionState d) (hst : s.2 = t.2) :
    (scaledDivisionInput d c x y a i s).2 =
      (scaledDivisionInput d c z y a i t).2 := by
  induction i using Fin.cases with
  | zero =>
      change (c • generalDivisionOperator (c⁻¹ * x) a s).2 =
        (c • generalDivisionOperator (c⁻¹ * z) a t).2
      exact congrArg (fun r : GeneralCoefficientSpace d => c • r)
        (generalDivisionOperator_remainder_congr (c⁻¹ * x) (c⁻¹ * z) a s t hst)
  | succ i =>
      change (y i • s).2 = (y i • t).2
      exact congrArg (fun r : GeneralCoefficientSpace d => y i • r) hst

/-- The analytic remainder computed from scaled division inputs is
independent of the first evaluation coordinate. -/
theorem scaledDivisionInput_extension_remainder_independent {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Source (n + 1)) ℂ) (d : ℕ)
    (c x z : ℂ) (y : Source n) (a : GeneralCoefficientSpace d)
    (hX : scaledDivisionInput d c x y a ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).radius)
    (hZ : scaledDivisionInput d c z y a ∈ Metric.eball 0
      (finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).radius) :
    (((finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).sum
      (scaledDivisionInput d c x y a)) (generalDivisionInitialState d)).2 =
    (((finiteBanachExtensionSeries (A := GeneralDivisionEndomorphism d) p).sum
      (scaledDivisionInput d c z y a)) (generalDivisionInitialState d)).2 := by
  exact projected_finiteBanachExtensionSeries_sum_eq p (generalRemainderProjection d)
    (scaledDivisionInput d c x y a) (scaledDivisionInput d c z y a)
    (scaledDivisionInput_remainder_congr d c x z y a)
    (generalDivisionInitialState d) (generalDivisionInitialState d) rfl hX hZ

end OnLeConjecture.Analytic.Germ
