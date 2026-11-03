/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicComponentChartVanishing
public import OnLeConjecture.DTwo.HomogeneousEqualizerQuotientIso
public import OnLeConjecture.Polynomial.WeightedSubstitution

/-!
# From affine initial comparisons to polynomial component identities

The component identities are proved in every complex algebra whose three
chosen elements satisfy the cyclic component relation. In particular they
hold in the existing iterated equalizer quotient. The conclusions do not
assume an associated-graded fiber-product description.
-/

public section

namespace OnLeConjecture.DTwo

@[expose] noncomputable def cyclicSourcePolynomial :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval ![MvPolynomial.X 1, MvPolynomial.X 2]

@[expose] noncomputable def cyclicRotatedPolynomial (ζ : ℂ) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C ζ * MvPolynomial.X 2]

theorem cyclicSourcePolynomial_homogeneous (L d : ℕ)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![L, 2] d) :
    (cyclicSourcePolynomial P).IsWeightedHomogeneous ![L, L, 2] d := by
  apply OnLeConjecture.Polynomial.isWeightedHomogeneous_aeval ![L, 2] ![L, L, 2]
    ![MvPolynomial.X 1, MvPolynomial.X 2] _ hP
  intro i
  fin_cases i
  · simpa using MvPolynomial.isWeightedHomogeneous_X ℂ (![L, L, 2] : Fin 3 → ℕ) 1
  · simpa using MvPolynomial.isWeightedHomogeneous_X ℂ (![L, L, 2] : Fin 3 → ℕ) 2

theorem cyclicRotatedPolynomial_homogeneous (L d : ℕ) (ζ : ℂ)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![L, 2] d) :
    (cyclicRotatedPolynomial ζ P).IsWeightedHomogeneous ![L, L, 2] d := by
  apply OnLeConjecture.Polynomial.isWeightedHomogeneous_aeval ![L, 2] ![L, L, 2]
    ![MvPolynomial.X 0, MvPolynomial.C ζ * MvPolynomial.X 2] _ hP
  intro i
  fin_cases i
  · simpa using MvPolynomial.isWeightedHomogeneous_X ℂ (![L, L, 2] : Fin 3 → ℕ) 0
  · simpa using
      (MvPolynomial.isWeightedHomogeneous_X ℂ (![L, L, 2] : Fin 3 → ℕ) 2).C_mul ζ

theorem aeval_cyclicSourcePolynomial {A : Type*} [CommRing A] [Algebra ℂ A]
    (X x y : A) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval ![X, x, y] (cyclicSourcePolynomial P) = MvPolynomial.aeval ![x, y] P := by
  have h : (MvPolynomial.aeval ![X, x, y]).comp cyclicSourcePolynomial =
      MvPolynomial.aeval ![x, y] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cyclicSourcePolynomial]
  exact DFunLike.congr_fun h P

theorem aeval_cyclicRotatedPolynomial {A : Type*} [CommRing A] [Algebra ℂ A]
    (X x y : A) (ζ : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.aeval ![X, x, y] (cyclicRotatedPolynomial ζ P) =
      MvPolynomial.aeval ![X, algebraMap ℂ A ζ * y] P := by
  have h : (MvPolynomial.aeval ![X, x, y]).comp (cyclicRotatedPolynomial ζ) =
      MvPolynomial.aeval ![X, algebraMap ℂ A ζ * y] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cyclicRotatedPolynomial]
  exact DFunLike.congr_fun h P

private theorem eval_cyclicSourcePolynomial (S s y : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![S, s, y] (cyclicSourcePolynomial P) = MvPolynomial.eval ![s, y] P := by
  simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id] using
    aeval_cyclicSourcePolynomial S s y P

private theorem eval_cyclicRotatedPolynomial (S s y ζ : ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval ![S, s, y] (cyclicRotatedPolynomial ζ P) =
      MvPolynomial.eval ![S, ζ * y] P := by
  simpa only [MvPolynomial.aeval_def, Algebra.algebraMap_self,
    RingHom.id_apply, MvPolynomial.eval₂_id] using aeval_cyclicRotatedPolynomial S s y ζ P

/-- A homogeneous affine equalizer identity is polynomial divisibility
by the equation of the entire cyclic component. -/
theorem cyclicInitial_difference_dvd_of_chart_identity
    (L d : ℕ) (c ζ : ℂ) (hc : c ≠ 0) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![L, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = 0) :
    cyclicComponentRelation L c ∣ cyclicSourcePolynomial P - cyclicRotatedPolynomial ζ P := by
  apply cyclicComponentRelation_dvd_of_weighted_chart_vanishing L d c hc _
    ((cyclicSourcePolynomial_homogeneous L d P hP).sub
      (cyclicRotatedPolynomial_homogeneous L d ζ P hP))
  intro s S hS hpoint
  simpa only [MvPolynomial.eval_sub, eval_cyclicSourcePolynomial,
    eval_cyclicRotatedPolynomial, mul_one] using hchart s S hS hpoint

/-- The nonzero primitive affine comparison also holds modulo the full
component equation. This polynomial bridge itself does not need oddness. -/
theorem cyclicInitial_primitive_difference_dvd_of_chart_identity
    (L N : ℕ) (c ζ cD : ℂ) (hc : c ≠ 0) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![L, 2] (L * N))
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    cyclicComponentRelation L c ∣
      cyclicSourcePolynomial P - cyclicRotatedPolynomial ζ P -
        MvPolynomial.C cD * (MvPolynomial.X 1 - MvPolynomial.X 0) ^ N := by
  have hdiff : MvPolynomial.IsWeightedHomogeneous ![L, L, 2]
      (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) L := by
    exact (MvPolynomial.isWeightedHomogeneous_X ℂ ![L, L, 2] 1).sub
      (MvPolynomial.isWeightedHomogeneous_X ℂ ![L, L, 2] 0)
  have hright : MvPolynomial.IsWeightedHomogeneous ![L, L, 2]
      (MvPolynomial.C cD *
        (MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) ^ N) (L * N) := by
    simpa [nsmul_eq_mul, mul_comm] using (hdiff.pow N).C_mul cD
  apply cyclicComponentRelation_dvd_of_weighted_chart_vanishing L (L * N) c hc _
    (((cyclicSourcePolynomial_homogeneous L (L * N) P hP).sub
      (cyclicRotatedPolynomial_homogeneous L (L * N) ζ P hP)).sub hright)
  intro s S hS hpoint
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, eval_cyclicSourcePolynomial,
    eval_cyclicRotatedPolynomial, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, hchart s S hS hpoint, sub_self]

private theorem aeval_eq_zero_of_cyclicComponentRelation_dvd
    {A : Type*} [CommRing A] [Algebra ℂ A] (L : ℕ) (c : ℂ)
    (X x y : A) (hpoint : X ^ 2 = x ^ 2 + algebraMap ℂ A c * y ^ L)
    (Q : MvPolynomial (Fin 3) ℂ) (hQ : cyclicComponentRelation L c ∣ Q) :
    MvPolynomial.aeval ![X, x, y] Q = 0 := by
  obtain ⟨R, hR⟩ := hQ
  rw [hR, map_mul]
  have hzero : MvPolynomial.aeval ![X, x, y] (cyclicComponentRelation L c) = 0 := by
    simp only [cyclicComponentRelation, map_sub, map_pow, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, hpoint]
    change x ^ 2 + algebraMap ℂ A c * y ^ L - x ^ 2 - algebraMap ℂ A c * y ^ L = 0
    ring
  rw [hzero, zero_mul]

/-- The zero affine comparison gives an identity in every algebra on
the cyclic component, including its coordinate quotient. -/
theorem cyclicInitial_equalizer_identity_of_chart
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (L d : ℕ) (c ζ : ℂ) (hc : c ≠ 0) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![L, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = 0)
    (X x y : A) (hpoint : X ^ 2 = x ^ 2 + algebraMap ℂ A c * y ^ L) :
    MvPolynomial.aeval ![x, y] P =
      MvPolynomial.aeval ![X, algebraMap ℂ A ζ * y] P := by
  have h := aeval_eq_zero_of_cyclicComponentRelation_dvd L c X x y hpoint _
    (cyclicInitial_difference_dvd_of_chart_identity L d c ζ hc P hP hchart)
  rw [map_sub, aeval_cyclicSourcePolynomial, aeval_cyclicRotatedPolynomial, sub_eq_zero] at h
  exact h

/-- The primitive affine comparison gives the exact quotient identity,
with the same comparison scalar at every point. -/
theorem cyclicInitial_primitive_identity_of_chart
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (L N : ℕ) (c ζ cD : ℂ) (hc : c ≠ 0) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![L, 2] (L * N))
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + c →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N)
    (X x y : A) (hpoint : X ^ 2 = x ^ 2 + algebraMap ℂ A c * y ^ L) :
    MvPolynomial.aeval ![x, y] P -
      MvPolynomial.aeval ![X, algebraMap ℂ A ζ * y] P =
        algebraMap ℂ A cD * (x - X) ^ N := by
  have h := aeval_eq_zero_of_cyclicComponentRelation_dvd L c X x y hpoint _
    (cyclicInitial_primitive_difference_dvd_of_chart_identity L N c ζ cD hc P hP hchart)
  simp only [map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    aeval_cyclicSourcePolynomial, aeval_cyclicRotatedPolynomial,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_zero] at h
  exact h

/-- Eliminating the parameter `T` in the iterated quotient gives precisely
the component relation with coefficient `τ*(1-χ)`. -/
theorem iteratedCoordinate_cyclicComponentRelation (L : ℕ) (τ χ : ℂ) (hτ : τ ≠ 0) :
    iteratedCoordinate τ χ L .component ^ 2 =
      iteratedCoordinate τ χ L .source ^ 2 +
        algebraMap ℂ (EqualizerSectorRing τ χ L) (τ * (1 - χ)) *
          iteratedCoordinate τ χ L .sector ^ L := by
  rw [iteratedComponentCoordinate_sq, iteratedSectorCoordinate_pow]
  congr 1
  rw [← mul_assoc, ← map_mul]
  congr 1
  congr 1
  field_simp

/-- The affine equalizer comparison holds in the iterated quotient used
by the homogeneous equalizer descent. -/
theorem cyclicInitial_iterated_equalizer_identity_of_chart
    (k j d : ℕ) (τ ζ : ℂ) (hτ : τ ≠ 0) (hcharacter : ζ ^ j ≠ 1)
    (P : MvPolynomial (Fin 2) ℂ) (hP : P.IsWeightedHomogeneous ![k + j, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + τ * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = 0) :
    MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .source,
          iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P =
      MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .component,
          algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) ζ *
            iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P :=
  cyclicInitial_equalizer_identity_of_chart (k + j) d (τ * (1 - ζ ^ j)) ζ
    (mul_ne_zero hτ (sub_ne_zero.mpr (Ne.symm hcharacter))) P hP hchart _ _ _
      (iteratedCoordinate_cyclicComponentRelation (k + j) τ (ζ ^ j) hτ)

/-- The primitive affine comparison holds with its original scalar in
the same iterated quotient. -/
theorem cyclicInitial_iterated_primitive_identity_of_chart
    (k j N : ℕ) (τ ζ cD : ℂ) (hτ : τ ≠ 0) (hcharacter : ζ ^ j ≠ 1)
    (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![k + j, 2] ((k + j) * N))
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + τ * (1 - ζ ^ j) →
      MvPolynomial.eval ![s, 1] P - MvPolynomial.eval ![S, ζ] P = cD * (s - S) ^ N) :
    MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .source,
          iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P -
      MvPolynomial.aeval
        ![iteratedCoordinate τ (ζ ^ j) (k + j) .component,
          algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) ζ *
            iteratedCoordinate τ (ζ ^ j) (k + j) .sector] P =
      algebraMap ℂ (EqualizerSectorRing τ (ζ ^ j) (k + j)) cD *
        (iteratedCoordinate τ (ζ ^ j) (k + j) .source -
          iteratedCoordinate τ (ζ ^ j) (k + j) .component) ^ N :=
  cyclicInitial_primitive_identity_of_chart (k + j) N (τ * (1 - ζ ^ j)) ζ cD
    (mul_ne_zero hτ (sub_ne_zero.mpr (Ne.symm hcharacter))) P hP hchart _ _ _
      (iteratedCoordinate_cyclicComponentRelation (k + j) τ (ζ ^ j) hτ)

end OnLeConjecture.DTwo
