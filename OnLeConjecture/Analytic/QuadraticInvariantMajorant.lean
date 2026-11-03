/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.QuadraticDecomposition
public import OnLeConjecture.Analytic.WeierstrassPreparation
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Formal quadratic invariant descent

This file proves the formal algebra underlying descent through
`(x, y) ↦ (x², y)`. A series in the outer variable is fixed by replacing that
variable with its negative exactly when it is obtained by expanding another
series by a factor of two.

The remaining analytic assertion is isolated after the formal result. It asks
that compression of the even outer Taylor coefficients of an analytic germ is
again the completed Taylor series of an analytic germ.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Compression of the coefficients with even outer index. -/
@[expose] noncomputable def evenOuterCompression
    (p : PowerSeries (PowerSeries ℂ)) : PowerSeries (PowerSeries ℂ) :=
  PowerSeries.mk fun k ↦ PowerSeries.coeff (2 * k) p

@[simp]
theorem coeff_evenOuterCompression
    (p : PowerSeries (PowerSeries ℂ)) (k : ℕ) :
    PowerSeries.coeff k (Germ.evenOuterCompression p) =
      PowerSeries.coeff (2 * k) p := by
  simp [Germ.evenOuterCompression]

/-- A series fixed by outer reflection has zero coefficients in every odd
degree. -/
theorem odd_outer_coeff_eq_zero_of_rescale_neg_one_eq
    {p : PowerSeries (PowerSeries ℂ)}
    (hp : PowerSeries.rescale (-1 : PowerSeries ℂ) p = p)
    {k : ℕ} (hk : Odd k) :
    PowerSeries.coeff k p = 0 := by
  have hcoeff := congrArg (PowerSeries.coeff k) hp
  rw [PowerSeries.coeff_rescale] at hcoeff
  have hpow : (-1 : PowerSeries ℂ) ^ k = -1 := by
    simpa using Odd.neg_one_pow hk
  rw [hpow, neg_one_mul] at hcoeff
  apply PowerSeries.ext
  intro n
  have hinner := congrArg (PowerSeries.coeff n) hcoeff
  exact CharZero.neg_eq_self_iff.mp (by simpa using hinner)

/-- Expanding the compression of a reflected series recovers the original
series. -/
theorem expand_evenOuterCompression_of_rescale_neg_one_eq
    {p : PowerSeries (PowerSeries ℂ)}
    (hp : PowerSeries.rescale (-1 : PowerSeries ℂ) p = p) :
    PowerSeries.expand 2 (by norm_num)
        (Germ.evenOuterCompression p) = p := by
  apply PowerSeries.ext
  intro k
  rcases k.even_or_odd with hk | hk
  · obtain ⟨j, rfl⟩ := hk
    rw [show j + j = 2 * j by omega]
    simp
  · rw [PowerSeries.coeff_expand_of_not_dvd]
    · exact (Germ.odd_outer_coeff_eq_zero_of_rescale_neg_one_eq hp hk).symm
    · intro hdiv
      exact (Nat.not_even_iff_odd.mpr hk) ((even_iff_two_dvd).mpr hdiv)

/-- Expansion by two is fixed by outer reflection. -/
theorem rescale_neg_one_expand_two
    (q : PowerSeries (PowerSeries ℂ)) :
    PowerSeries.rescale (-1 : PowerSeries ℂ)
        (PowerSeries.expand 2 (by norm_num) q) =
      PowerSeries.expand 2 (by norm_num) q := by
  apply PowerSeries.ext
  intro k
  by_cases hk : 2 ∣ k
  · obtain ⟨j, rfl⟩ := hk
    simp [PowerSeries.coeff_rescale, pow_mul]
  · simp [PowerSeries.coeff_rescale,
      PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) q hk]

/-- Outer reflection invariance is equivalent to belonging to the image of
expansion by two. -/
theorem rescale_neg_one_eq_iff_exists_expand_two
    (p : PowerSeries (PowerSeries ℂ)) :
    PowerSeries.rescale (-1 : PowerSeries ℂ) p = p ↔
      ∃ q : PowerSeries (PowerSeries ℂ),
        PowerSeries.expand 2 (by norm_num) q = p := by
  constructor
  · intro hp
    exact ⟨Germ.evenOuterCompression p,
      Germ.expand_evenOuterCompression_of_rescale_neg_one_eq hp⟩
  · rintro ⟨q, rfl⟩
    exact Germ.rescale_neg_one_expand_two q

/-- The formal preimage of an outer reflection invariant series is unique. -/
theorem existsUnique_expand_two_of_rescale_neg_one_eq
    {p : PowerSeries (PowerSeries ℂ)}
    (hp : PowerSeries.rescale (-1 : PowerSeries ℂ) p = p) :
    ∃! q : PowerSeries (PowerSeries ℂ),
      PowerSeries.expand 2 (by norm_num) q = p := by
  refine ⟨Germ.evenOuterCompression p,
    Germ.expand_evenOuterCompression_of_rescale_neg_one_eq hp, ?_⟩
  intro q hq
  apply PowerSeries.ext
  intro k
  have hcoeff := congrArg (PowerSeries.coeff (2 * k)) hq
  simpa using hcoeff

/-- A germ extended from the coordinate hyperplane is fixed by first
coordinate reflection. -/
theorem reflection_hyperplaneExtension (r : Germ 1) :
    Germ.reflectionAlgEquiv (Germ.hyperplaneExtension 1 r) =
      Germ.hyperplaneExtension 1 r := by
  rcases r with ⟨r, hr⟩
  induction r using Filter.Germ.inductionOn with
  | _ r =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hr
      change Germ.reflectionAlgEquiv
          (Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)) =
        Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)
      rw [Germ.hyperplaneExtension_ofFunction]
      change Germ.reflectionAlgEquiv
          (Germ.ofFunction (r ∘ Germ.hyperplaneTail 1) _) = _
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by
        change r (Germ.hyperplaneTail 1
          (Germ.firstCoordinateReflection z)) =
          r (Germ.hyperplaneTail 1 z)
        congr 1

/-- First coordinate division changes sign under reflection. -/
theorem firstCoordinateTail_reflection (f : Germ 2) :
    Germ.firstCoordinateTail (Germ.reflectionAlgEquiv f) =
      -Germ.reflectionAlgEquiv (Germ.firstCoordinateTail f) := by
  apply (Germ.firstCoordinate_division_eq (n := 1) (f :=
    Germ.reflectionAlgEquiv f) (q :=
      -Germ.reflectionAlgEquiv (Germ.firstCoordinateTail f))
      (r := Germ.firstCoordinateCoefficient f) ?_).1
  calc
    Germ.reflectionAlgEquiv f = Germ.reflectionAlgEquiv
        (Germ.coordinate (0 : Fin 2) * Germ.firstCoordinateTail f +
          Germ.hyperplaneExtension 1
            (Germ.firstCoordinateCoefficient f)) := by
      exact congrArg Germ.reflectionAlgEquiv
        (Germ.firstCoordinate_decomposition f)
    _ = Germ.coordinate (0 : Fin 2) *
          (-Germ.reflectionAlgEquiv (Germ.firstCoordinateTail f)) +
        Germ.hyperplaneExtension 1
          (Germ.firstCoordinateCoefficient f) := by
      rw [map_add, map_mul, Germ.reflectionAlgEquiv_coordinate_zero,
        Germ.reflection_hyperplaneExtension]
      ring

/-- First coordinate division commutes with negation. -/
theorem firstCoordinateTail_neg (f : Germ 2) :
    Germ.firstCoordinateTail (-f) = -Germ.firstCoordinateTail f := by
  apply (Germ.firstCoordinate_division_eq (n := 1) (f := -f)
    (q := -Germ.firstCoordinateTail f)
    (r := -Germ.firstCoordinateCoefficient f) ?_).1
  calc
    -f = -(Germ.coordinate (0 : Fin 2) * Germ.firstCoordinateTail f +
        Germ.hyperplaneExtension 1
          (Germ.firstCoordinateCoefficient f)) := by
      exact congrArg Neg.neg (Germ.firstCoordinate_decomposition f)
    _ = Germ.coordinate (0 : Fin 2) *
          (-Germ.firstCoordinateTail f) +
        Germ.hyperplaneExtension 1
          (-Germ.firstCoordinateCoefficient f) := by
      rw [map_neg]
      ring

/-- Iterated first coordinate division transforms by the corresponding sign
under reflection. -/
theorem firstCoordinateTailIterate_reflection (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTailIterate k (Germ.reflectionAlgEquiv f) =
      ((-1 : ℂ) ^ k) • Germ.reflectionAlgEquiv
        (Germ.firstCoordinateTailIterate k f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show k + 1 = k + 1 from rfl,
        Germ.firstCoordinateTailIterate_succ, ih]
      rcases k.even_or_odd with hk | hk
      · rw [hk.neg_one_pow, one_smul,
          Germ.firstCoordinateTail_reflection,
          Germ.firstCoordinateTailIterate_succ,
          pow_succ, hk.neg_one_pow, one_mul, neg_one_smul]
      · rw [hk.neg_one_pow, neg_one_smul,
          Germ.firstCoordinateTail_neg,
          Germ.firstCoordinateTail_reflection, neg_neg,
          Germ.firstCoordinateTailIterate_succ,
          pow_succ, hk.neg_one_pow, neg_one_mul, neg_neg, one_smul]

/-- Reflection multiplies the `k`th analytic coefficient in the first
coordinate by `(-1)^k`. -/
theorem firstCoordinateTaylorCoefficient_reflection (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTaylorCoefficient k
        (Germ.reflectionAlgEquiv f) =
      ((-1 : ℂ) ^ k) • Germ.firstCoordinateTaylorCoefficient k f := by
  rw [Germ.firstCoordinateTaylorCoefficient,
    Germ.firstCoordinateTailIterate_reflection]
  rcases k.even_or_odd with hk | hk
  · rw [hk.neg_one_pow, one_smul, one_smul]
    exact Germ.hyperplaneRestriction_reflection
      (Germ.firstCoordinateTailIterate k f)
  · rw [hk.neg_one_pow, neg_one_smul]
    change Germ.hyperplaneRestriction 1
        (-Germ.reflectionAlgEquiv
          (Germ.firstCoordinateTailIterate k f)) =
      (-1 : ℂ) • Germ.hyperplaneRestriction 1
        (Germ.firstCoordinateTailIterate k f)
    rw [neg_one_smul]
    rw [map_neg, neg_inj]
    exact Germ.hyperplaneRestriction_reflection
      (Germ.firstCoordinateTailIterate k f)

/-- Completed Taylor expansion intertwines first coordinate reflection with
outer rescaling by `-1`. -/
theorem completedPlaneTaylor_reflection (f : Germ 2) :
    Germ.completedPlaneTaylorRingHom (Germ.reflectionAlgEquiv f) =
      PowerSeries.rescale (-1 : PowerSeries ℂ)
        (Germ.completedPlaneTaylorRingHom f) := by
  apply PowerSeries.ext
  intro k
  rw [Germ.completedPlaneTaylorRingHom_coeff,
    Germ.firstCoordinateTaylorCoefficient_reflection,
    PowerSeries.coeff_rescale,
    Germ.completedPlaneTaylorRingHom_coeff]
  change Germ.oneVariableTaylorAlgHom
      (((-1 : ℂ) ^ k) • Germ.firstCoordinateTaylorCoefficient k f) = _
  rw [map_smul]
  rw [Algebra.smul_def]
  congr 1
  simp

/-- An invariant analytic germ has a completed Taylor series obtained by
expansion by two. -/
theorem completedPlaneTaylor_eq_expand_evenOuterCompression
    {f : Germ 2} (hf : Germ.reflectionAlgEquiv f = f) :
    PowerSeries.expand 2 (by norm_num)
        (Germ.evenOuterCompression
          (Germ.completedPlaneTaylorRingHom f)) =
      Germ.completedPlaneTaylorRingHom f := by
  apply Germ.expand_evenOuterCompression_of_rescale_neg_one_eq
  rw [← Germ.completedPlaneTaylor_reflection, hf]

/-- Pullback by the quadratic map fixes a germ extended from the coordinate
hyperplane. -/
theorem quadraticSubstitution_hyperplaneExtension (r : Germ 1) :
    Germ.quadraticSubstitutionAlgHom (Germ.hyperplaneExtension 1 r) =
      Germ.hyperplaneExtension 1 r := by
  rcases r with ⟨r, hr⟩
  induction r using Filter.Germ.inductionOn with
  | _ r =>
      rw [mem_analyticGermSubring, isAnalyticGerm_ofFun] at hr
      change Germ.quadraticSubstitutionAlgHom
          (Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)) =
        Germ.hyperplaneExtension 1 (Germ.ofFunction r hr)
      rw [Germ.hyperplaneExtension_ofFunction]
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun z ↦ by
        change r (Germ.hyperplaneTail 1 (Germ.quadraticMap z)) =
          r (Germ.hyperplaneTail 1 z)
        congr 1

/-- Restriction to the first coordinate hyperplane commutes with quadratic
substitution. -/
theorem hyperplaneRestriction_quadraticSubstitution (f : Germ 2) :
    Germ.hyperplaneRestriction 1
        (Germ.quadraticSubstitutionAlgHom f) =
      Germ.hyperplaneRestriction 1 f := by
  have hdecomposition := congrArg Germ.quadraticSubstitutionAlgHom
    (Germ.firstCoordinate_decomposition f)
  rw [map_add, map_mul,
    Germ.quadraticSubstitutionAlgHom_coordinate_zero,
    Germ.quadraticSubstitution_hyperplaneExtension] at hdecomposition
  rw [hdecomposition, map_add, map_mul, map_pow,
    Germ.hyperplaneRestriction_coordinate_zero, zero_pow (by norm_num),
    zero_mul, zero_add]
  exact DFunLike.congr_fun
    (Germ.hyperplaneRestriction_comp_extension 1)
    (Germ.firstCoordinateCoefficient f)

/-- One division of a quadratic pullback leaves one factor of the first
coordinate. -/
theorem firstCoordinateTail_quadraticSubstitution (f : Germ 2) :
    Germ.firstCoordinateTail (Germ.quadraticSubstitutionAlgHom f) =
      Germ.coordinate (0 : Fin 2) *
        Germ.quadraticSubstitutionAlgHom
          (Germ.firstCoordinateTail f) := by
  apply (Germ.firstCoordinate_division_eq (n := 1)
    (f := Germ.quadraticSubstitutionAlgHom f)
    (q := Germ.coordinate (0 : Fin 2) *
      Germ.quadraticSubstitutionAlgHom (Germ.firstCoordinateTail f))
    (r := Germ.firstCoordinateCoefficient f) ?_).1
  calc
    Germ.quadraticSubstitutionAlgHom f =
        Germ.quadraticSubstitutionAlgHom
          (Germ.coordinate (0 : Fin 2) *
              Germ.firstCoordinateTail f +
            Germ.hyperplaneExtension 1
              (Germ.firstCoordinateCoefficient f)) := by
      exact congrArg Germ.quadraticSubstitutionAlgHom
        (Germ.firstCoordinate_decomposition f)
    _ = Germ.coordinate (0 : Fin 2) *
          (Germ.coordinate (0 : Fin 2) *
            Germ.quadraticSubstitutionAlgHom
              (Germ.firstCoordinateTail f)) +
        Germ.hyperplaneExtension 1
          (Germ.firstCoordinateCoefficient f) := by
      rw [map_add, map_mul,
        Germ.quadraticSubstitutionAlgHom_coordinate_zero,
        Germ.quadraticSubstitution_hyperplaneExtension]
      ring

/-- Two divisions of a quadratic pullback equal the quadratic pullback of
one division. -/
theorem firstCoordinateTail_twice_quadraticSubstitution (f : Germ 2) :
    Germ.firstCoordinateTail
        (Germ.firstCoordinateTail
          (Germ.quadraticSubstitutionAlgHom f)) =
      Germ.quadraticSubstitutionAlgHom
        (Germ.firstCoordinateTail f) := by
  rw [Germ.firstCoordinateTail_quadraticSubstitution,
    Germ.firstCoordinateTail_coordinate_mul]

/-- An even number of divisions of a quadratic pullback descends to half as
many divisions before pullback. -/
theorem firstCoordinateTailIterate_two_mul_quadraticSubstitution
    (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTailIterate (2 * k)
        (Germ.quadraticSubstitutionAlgHom f) =
      Germ.quadraticSubstitutionAlgHom
        (Germ.firstCoordinateTailIterate k f) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Germ.firstCoordinateTailIterate (2 * (k + 1))
            (Germ.quadraticSubstitutionAlgHom f) =
            Germ.firstCoordinateTail
              (Germ.firstCoordinateTail
                (Germ.firstCoordinateTailIterate (2 * k)
                  (Germ.quadraticSubstitutionAlgHom f))) := by
          rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
            Germ.firstCoordinateTailIterate_succ,
            Germ.firstCoordinateTailIterate_succ]
        _ = Germ.firstCoordinateTail
              (Germ.firstCoordinateTail
                (Germ.quadraticSubstitutionAlgHom
                  (Germ.firstCoordinateTailIterate k f))) := by
          rw [ih]
        _ = Germ.quadraticSubstitutionAlgHom
              (Germ.firstCoordinateTail
                (Germ.firstCoordinateTailIterate k f)) :=
          Germ.firstCoordinateTail_twice_quadraticSubstitution _
        _ = Germ.quadraticSubstitutionAlgHom
              (Germ.firstCoordinateTailIterate (k + 1) f) := by
          rw [Germ.firstCoordinateTailIterate_succ]

/-- An odd number of divisions of a quadratic pullback leaves one first
coordinate factor. -/
theorem firstCoordinateTailIterate_two_mul_add_one_quadraticSubstitution
    (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTailIterate (2 * k + 1)
        (Germ.quadraticSubstitutionAlgHom f) =
      Germ.coordinate (0 : Fin 2) *
        Germ.quadraticSubstitutionAlgHom
          (Germ.firstCoordinateTailIterate (k + 1) f) := by
  rw [Germ.firstCoordinateTailIterate_succ,
    Germ.firstCoordinateTailIterate_two_mul_quadraticSubstitution,
    Germ.firstCoordinateTail_quadraticSubstitution,
    Germ.firstCoordinateTailIterate_succ]

/-- Even first coordinate coefficients of a quadratic pullback are the
coefficients before pullback with half the index. -/
theorem firstCoordinateTaylorCoefficient_two_mul_quadraticSubstitution
    (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTaylorCoefficient (2 * k)
        (Germ.quadraticSubstitutionAlgHom f) =
      Germ.firstCoordinateTaylorCoefficient k f := by
  rw [Germ.firstCoordinateTaylorCoefficient,
    Germ.firstCoordinateTailIterate_two_mul_quadraticSubstitution]
  exact Germ.hyperplaneRestriction_quadraticSubstitution
    (Germ.firstCoordinateTailIterate k f)

/-- Odd first coordinate coefficients of a quadratic pullback vanish. -/
theorem firstCoordinateTaylorCoefficient_two_mul_add_one_quadraticSubstitution
    (k : ℕ) (f : Germ 2) :
    Germ.firstCoordinateTaylorCoefficient (2 * k + 1)
        (Germ.quadraticSubstitutionAlgHom f) = 0 := by
  rw [Germ.firstCoordinateTaylorCoefficient,
    Germ.firstCoordinateTailIterate_two_mul_add_one_quadraticSubstitution]
  change Germ.hyperplaneRestriction 1
      (Germ.coordinate (0 : Fin 2) *
        Germ.quadraticSubstitutionAlgHom
          (Germ.firstCoordinateTailIterate (k + 1) f)) = 0
  rw [map_mul, Germ.hyperplaneRestriction_coordinate_zero, zero_mul]

/-- Completed Taylor expansion intertwines quadratic substitution with
expansion of the outer variable by two. -/
theorem completedPlaneTaylor_quadraticSubstitution (f : Germ 2) :
    Germ.completedPlaneTaylorRingHom
        (Germ.quadraticSubstitutionAlgHom f) =
      PowerSeries.expand 2 (by norm_num)
        (Germ.completedPlaneTaylorRingHom f) := by
  apply PowerSeries.ext
  intro k
  rcases k.even_or_odd with hk | hk
  · obtain ⟨j, hj⟩ := hk
    rw [show k = 2 * j by omega,
      Germ.completedPlaneTaylorRingHom_coeff,
      Germ.firstCoordinateTaylorCoefficient_two_mul_quadraticSubstitution,
      PowerSeries.coeff_expand_mul,
      Germ.completedPlaneTaylorRingHom_coeff]
  · obtain ⟨j, hj⟩ := hk
    rw [show k = 2 * j + 1 by omega,
      Germ.completedPlaneTaylorRingHom_coeff,
      Germ.firstCoordinateTaylorCoefficient_two_mul_add_one_quadraticSubstitution]
    change Germ.oneVariableTaylorRingHom 0 = _
    rw [map_zero, PowerSeries.coeff_expand_of_not_dvd]
    intro hdiv
    omega

/-- Compressing a series expanded by two recovers the original series. -/
@[simp]
theorem evenOuterCompression_expand_two
    (p : PowerSeries (PowerSeries ℂ)) :
    Germ.evenOuterCompression
        (PowerSeries.expand 2 (by norm_num) p) = p := by
  apply PowerSeries.ext
  intro k
  simp

/-- The exact convergence assertion needed for quadratic invariant descent.
It says that the completed Taylor image is closed under compression of even
outer coefficients whenever the outer series is fixed by reflection. -/
def EvenOuterTaylorImageClosure : Prop :=
  ∀ p : PowerSeries (PowerSeries ℂ),
    p ∈ Set.range Germ.completedPlaneTaylorRingHom →
      PowerSeries.rescale (-1 : PowerSeries ℂ) p = p →
        Germ.evenOuterCompression p ∈
          Set.range Germ.completedPlaneTaylorRingHom

/-- Closure of the analytic Taylor image under even compression is
equivalent to quadratic invariant descent. -/
theorem evenOuterTaylorImageClosure_iff_quadraticInvariantDescent :
    Germ.EvenOuterTaylorImageClosure ↔ Germ.QuadraticInvariantDescent := by
  constructor
  · intro hclosure
    unfold Germ.QuadraticInvariantDescent
    intro f hf
    have hrescale : PowerSeries.rescale (-1 : PowerSeries ℂ)
        (Germ.completedPlaneTaylorRingHom f) =
        Germ.completedPlaneTaylorRingHom f := by
      rw [← Germ.completedPlaneTaylor_reflection, hf]
    rcases hclosure (Germ.completedPlaneTaylorRingHom f)
        ⟨f, rfl⟩ hrescale with ⟨a, ha⟩
    refine ⟨a, Germ.completedPlaneTaylorRingHom_injective ?_⟩
    rw [Germ.completedPlaneTaylor_quadraticSubstitution, ha,
      Germ.expand_evenOuterCompression_of_rescale_neg_one_eq hrescale]
  · intro hdescent
    unfold Germ.QuadraticInvariantDescent at hdescent
    intro p hp hreflection
    rcases hp with ⟨f, rfl⟩
    have hf : Germ.reflectionAlgEquiv f = f := by
      apply Germ.completedPlaneTaylorRingHom_injective
      rw [Germ.completedPlaneTaylor_reflection, hreflection]
    rcases hdescent f hf with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← ha, Germ.completedPlaneTaylor_quadraticSubstitution,
      Germ.evenOuterCompression_expand_two]

end Germ

end OnLeConjecture.Analytic
