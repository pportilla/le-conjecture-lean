/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneElimination
public import OnLeConjecture.Analytic.WeightedPolynomialInitialForm

/-!
# Divisibility of weighted polynomial initial forms

Membership in a weighted order ideal imposes the corresponding divisibility
on every coefficient in the first coordinate. This supplies the coefficient
comparison needed when an analytic germ is divisible by a power of the second
coordinate.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators

namespace Germ

/-- The weighted order ideal with threshold zero is the whole germ ring. -/
theorem weightedOrderIdeal_zero_eq_top (a : ℕ) :
    Germ.weightedOrderIdeal a 0 = ⊤ := by
  apply top_unique
  intro f _
  rw [Germ.mem_weightedOrderIdeal_iff]
  refine ⟨fun _ ↦ f, ?_⟩
  simp [Germ.weightedOrderGenerator]

/-- Differentiation in the first coordinate lowers a weighted threshold by
`a`, with truncated subtraction when the threshold is smaller than `a`. -/
theorem partialDerivative_zero_mem_weightedOrderIdeal_sub
    (a E : ℕ) (ha : 0 < a) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a E) :
    Germ.partialDerivative (0 : Fin 2) f ∈
      Germ.weightedOrderIdeal a (E - a) := by
  by_cases haE : a ≤ E
  · apply Germ.partialDerivative_zero_mem_weightedOrderIdeal
      a (E - a) ha
    simpa only [Nat.sub_add_cancel haE] using hf
  · have hsub : E - a = 0 := by omega
    rw [hsub, Germ.weightedOrderIdeal_zero_eq_top]
    exact Submodule.mem_top

/-- Multiplication by a power of the first coordinate shifts the analytic
coefficients by that power. -/
theorem firstCoordinateTaylorCoefficient_mul_coordinate_pow
    (f : Germ 2) (j k : ℕ) :
    Germ.firstCoordinateTaylorCoefficient k
        (f * Germ.coordinate (0 : Fin 2) ^ j) =
      if j ≤ k then
        Germ.firstCoordinateTaylorCoefficient (k - j) f
      else 0 := by
  have hseries :
      Germ.firstCoordinateFormalRingHom 1
          (f * Germ.coordinate (0 : Fin 2) ^ j) =
        Germ.firstCoordinateFormalRingHom 1 f * PowerSeries.X ^ j := by
    rw [map_mul, map_pow, Germ.firstCoordinateFormalRingHom_coordinate]
  have hcoeff := congrArg (PowerSeries.coeff k) hseries
  simpa only [Germ.firstCoordinateFormalRingHom_apply,
    Germ.firstCoordinateFormalSeries_coeff,
    PowerSeries.coeff_mul_X_pow'] using hcoeff

/-- Every coefficient of a germ in a weighted order ideal has the
corresponding power of the second coordinate as a divisor. -/
theorem coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_weightedOrderIdeal
    (a D : ℕ) (f : Germ 2)
    (hf : f ∈ Germ.weightedOrderIdeal a D) (k : ℕ) :
    Germ.coordinate (0 : Fin 1) ^ (D - a * k) ∣
      Germ.firstCoordinateTaylorCoefficient k f := by
  rw [Germ.mem_weightedOrderIdeal_iff] at hf
  obtain ⟨c, hc⟩ := hf
  have hcoefficient :
      Germ.firstCoordinateTaylorCoefficient k f =
        ∑ j, Germ.firstCoordinateTaylorCoefficient k
          (c j * Germ.weightedOrderGenerator a D j) := by
    have hseries := congrArg (Germ.firstCoordinateFormalRingHom 1) hc
    have hcoefficient := congrArg (PowerSeries.coeff k) hseries
    simpa only [map_sum, Germ.firstCoordinateFormalRingHom_apply,
      Germ.firstCoordinateFormalSeries_coeff] using hcoefficient.symm
  rw [hcoefficient]
  apply Finset.dvd_sum
  intro j _
  let u : ℕ := j
  let v : ℕ := D - a * u
  let e : ℕ := D - a * k
  have hterm :
      Germ.firstCoordinateTaylorCoefficient k
          (c j * Germ.weightedOrderGenerator a D j) =
        Germ.coordinate (0 : Fin 1) ^ v *
          Germ.firstCoordinateTaylorCoefficient k
            (c j * Germ.coordinate (0 : Fin 2) ^ u) := by
    have hy :
        Germ.hyperplaneExtension 1
            (Germ.coordinate (0 : Fin 1) ^ v) =
          Germ.coordinate (1 : Fin 2) ^ v := by
      rw [map_pow, Germ.hyperplaneExtension_coordinate_plane]
    rw [Germ.weightedOrderGenerator]
    change Germ.firstCoordinateTaylorCoefficient k
        (c j * (Germ.coordinate (0 : Fin 2) ^ u *
          Germ.coordinate (1 : Fin 2) ^ v)) = _
    rw [← hy]
    rw [show c j * (Germ.coordinate (0 : Fin 2) ^ u *
          Germ.hyperplaneExtension 1
            (Germ.coordinate (0 : Fin 1) ^ v)) =
        Germ.hyperplaneExtension 1
            (Germ.coordinate (0 : Fin 1) ^ v) *
          (c j * Germ.coordinate (0 : Fin 2) ^ u) by ring]
    exact Germ.firstCoordinateTaylorCoefficient_hyperplaneExtension_mul
      (Germ.coordinate (0 : Fin 1) ^ v)
        (c j * Germ.coordinate (0 : Fin 2) ^ u)
  rw [hterm]
  by_cases huk : u ≤ k
  · have he : e ≤ v := by
      simpa only [e, v, u] using
        Nat.sub_le_sub_left (Nat.mul_le_mul_left a huk) D
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ he) _
  · rw [Germ.firstCoordinateTaylorCoefficient_mul_coordinate_pow,
      if_neg huk]
    simp

private noncomputable def coordinatePolynomialFinSuccSeries :
    MvPolynomial (Fin 2) ℂ →+* PowerSeries (Germ 1) :=
  Polynomial.coeToPowerSeries.ringHom.comp
    ((Polynomial.mapRingHom
      (Germ.coordinatePolynomialAlgHom 1).toRingHom).comp
        (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom)

private theorem firstCoordinateFormalRingHom_coordinatePolynomial
    (P : MvPolynomial (Fin 2) ℂ) :
    Germ.firstCoordinateFormalRingHom 1
        (Germ.coordinatePolynomialAlgHom 2 P) =
      coordinatePolynomialFinSuccSeries P := by
  let left : MvPolynomial (Fin 2) ℂ →+* PowerSeries (Germ 1) :=
    (Germ.firstCoordinateFormalRingHom 1).comp
      (Germ.coordinatePolynomialAlgHom 2).toRingHom
  have hequality : left = coordinatePolynomialFinSuccSeries := by
    apply MvPolynomial.ringHom_ext
    · intro c
      dsimp only [left, RingHom.comp_apply]
      change Germ.firstCoordinateFormalRingHom 1
          (Germ.coordinatePolynomialAlgHom 2 (MvPolynomial.C c)) = _
      rw [Germ.coordinatePolynomialAlgHom_C]
      have hconstant :
          Germ.constRingHom 2 c =
            Germ.hyperplaneExtension 1 (Germ.constRingHom 1 c) := by
        exact (PointedMapGerm.pullback_constRingHom
          (Germ.hyperplaneTailGerm 1) c).symm
      rw [hconstant,
        Germ.firstCoordinateFormalRingHom_hyperplaneExtension]
      rw [coordinatePolynomialFinSuccSeries]
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        Polynomial.coeToPowerSeries.ringHom_apply]
      change PowerSeries.C (Germ.constRingHom 1 c) =
        ((Polynomial.map (Germ.coordinatePolynomialAlgHom 1).toRingHom
          (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.C c)) :
            Polynomial (Germ 1)) : PowerSeries (Germ 1))
      have hfin :
          MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.C c) =
            Polynomial.C (MvPolynomial.C c) := by
        change MvPolynomial.finSuccEquiv ℂ 1
            (algebraMap ℂ (MvPolynomial (Fin 2) ℂ) c) =
          algebraMap ℂ (Polynomial (MvPolynomial (Fin 1) ℂ)) c
        exact (MvPolynomial.finSuccEquiv ℂ 1).commutes c
      rw [hfin, Polynomial.map_C, Polynomial.coe_C]
      congr 1
      change Germ.constRingHom 1 c =
        Germ.coordinatePolynomialAlgHom 1 (MvPolynomial.C c)
      rw [Germ.coordinatePolynomialAlgHom_C]
    · intro i
      fin_cases i
      · dsimp only [left, RingHom.comp_apply]
        change Germ.firstCoordinateFormalRingHom 1
            (Germ.coordinatePolynomialAlgHom 2
              (MvPolynomial.X (0 : Fin 2))) = _
        rw [Germ.coordinatePolynomialAlgHom_X]
        change Germ.firstCoordinateFormalRingHom 1
            (Germ.coordinate (0 : Fin 2)) = _
        rw [Germ.firstCoordinateFormalRingHom_coordinate]
        rw [coordinatePolynomialFinSuccSeries]
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          Polynomial.coeToPowerSeries.ringHom_apply]
        change PowerSeries.X =
          ((Polynomial.map (Germ.coordinatePolynomialAlgHom 1).toRingHom
            (MvPolynomial.finSuccEquiv ℂ 1
              (MvPolynomial.X (0 : Fin 2))) :
                Polynomial (Germ 1)) : PowerSeries (Germ 1))
        rw [MvPolynomial.finSuccEquiv_X_zero,
          Polynomial.map_X, Polynomial.coe_X]
      · dsimp only [left, RingHom.comp_apply]
        change Germ.firstCoordinateFormalRingHom 1
            (Germ.coordinatePolynomialAlgHom 2
              (MvPolynomial.X (1 : Fin 2))) = _
        rw [Germ.coordinatePolynomialAlgHom_X]
        change Germ.firstCoordinateFormalRingHom 1
            (Germ.coordinate (1 : Fin 2)) = _
        rw [← Germ.hyperplaneExtension_coordinate_plane,
          Germ.firstCoordinateFormalRingHom_hyperplaneExtension]
        rw [coordinatePolynomialFinSuccSeries]
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
          Polynomial.coeToPowerSeries.ringHom_apply]
        change PowerSeries.C (Germ.coordinate (0 : Fin 1)) =
          ((Polynomial.map (Germ.coordinatePolynomialAlgHom 1).toRingHom
            (MvPolynomial.finSuccEquiv ℂ 1
              (MvPolynomial.X (1 : Fin 2))) :
                Polynomial (Germ 1)) : PowerSeries (Germ 1))
        rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by rfl,
          MvPolynomial.finSuccEquiv_X_succ,
          Polynomial.map_C, Polynomial.coe_C]
        congr 1
        change Germ.coordinate (0 : Fin 1) =
          Germ.coordinatePolynomialAlgHom 1
            (MvPolynomial.X (0 : Fin 1))
        rw [Germ.coordinatePolynomialAlgHom_X]
  change left P = coordinatePolynomialFinSuccSeries P
  exact RingHom.congr_fun hequality P

/-- The coefficient in the first coordinate of a coordinate polynomial is
the coordinate germ of the corresponding coefficient under `finSuccEquiv`.
-/
theorem firstCoordinateTaylorCoefficient_coordinatePolynomial
    (P : MvPolynomial (Fin 2) ℂ) (k : ℕ) :
    Germ.firstCoordinateTaylorCoefficient k
        (Germ.coordinatePolynomialAlgHom 2 P) =
      Germ.coordinatePolynomialAlgHom 1
        ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k) := by
  have hseries := firstCoordinateFormalRingHom_coordinatePolynomial P
  have hcoefficient := congrArg (PowerSeries.coeff k) hseries
  simpa [coordinatePolynomialFinSuccSeries] using hcoefficient

private theorem finSuccEquiv_coeff_eq_weighted_monomial
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (k : ℕ) :
    (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k =
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 1) (D - a * k))
        ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k |>.coeff
          (Finsupp.single (0 : Fin 1) (D - a * k))) := by
  apply MvPolynomial.eq_monomial_of_support_subset_singleton
  intro d hd
  have hdne :
      MvPolynomial.coeff d
          ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hfullne : MvPolynomial.coeff (Finsupp.cons k d) P ≠ 0 := by
    rwa [← MvPolynomial.finSuccEquiv_coeff_coeff]
  have hweight := hP hfullne
  apply Finsupp.ext
  intro i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rw [Finsupp.single_eq_same]
  have hweight' :
      k * a + (Finsupp.cons k d) (1 : Fin 2) = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using hweight
  have hcons : (Finsupp.cons k d) (1 : Fin 2) = d (0 : Fin 1) := by
    rfl
  rw [hcons] at hweight'
  apply Nat.eq_sub_of_add_eq
  calc
    d 0 + a * k = k * a + d 0 := by ac_rfl
    _ = D := hweight'

/-- A first coordinate exponent whose weight exceeds the weighted degree has
zero coefficient in a weighted homogeneous polynomial. -/
theorem finSuccEquiv_coeff_eq_zero_of_weight_exceeds_degree
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (k : ℕ)
    (hk : D < a * k) :
    (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.coeff_zero,
    MvPolynomial.finSuccEquiv_coeff_coeff]
  apply hP.coeff_eq_zero
  intro hweight
  have hweight' :
      k * a + (Finsupp.cons k d) (1 : Fin 2) = D := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype,
      Fin.sum_univ_two] using hweight
  have hcons : (Finsupp.cons k d) (1 : Fin 2) = d (0 : Fin 1) := by
    rfl
  rw [hcons] at hweight'
  have hle : a * k ≤ D := by
    calc
      a * k = k * a := by rw [mul_comm]
      _ ≤ k * a + d 0 := Nat.le_add_right _ _
      _ = D := hweight'
  exact (not_lt_of_ge hle) hk

/-- The first coordinate coefficient of a weighted homogeneous coordinate
polynomial is a scalar multiple of its forced second coordinate power. -/
theorem firstCoordinateTaylorCoefficient_coordinatePolynomial_of_weightedHomogeneous
    (a D : ℕ) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D) (k : ℕ) :
    Germ.firstCoordinateTaylorCoefficient k
        (Germ.coordinatePolynomialAlgHom 2 P) =
      Germ.constRingHom 1
          ((MvPolynomial.finSuccEquiv ℂ 1 P).coeff k |>.coeff
            (Finsupp.single (0 : Fin 1) (D - a * k))) *
        Germ.coordinate (0 : Fin 1) ^ (D - a * k) := by
  let c := (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k |>.coeff
    (Finsupp.single (0 : Fin 1) (D - a * k))
  change Germ.firstCoordinateTaylorCoefficient k
      (Germ.coordinatePolynomialAlgHom 2 P) =
    Germ.constRingHom 1 c *
      Germ.coordinate (0 : Fin 1) ^ (D - a * k)
  have hmonomial :
      (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k =
        MvPolynomial.monomial
          (Finsupp.single (0 : Fin 1) (D - a * k)) c := by
    simpa only [c] using
      finSuccEquiv_coeff_eq_weighted_monomial a D P hP k
  rw [Germ.firstCoordinateTaylorCoefficient_coordinatePolynomial,
    hmonomial,
    ← MvPolynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    Germ.coordinatePolynomialAlgHom_C,
    Germ.coordinatePolynomialAlgHom_X]

/-- A scalar multiple of the `e`th coordinate power cannot be divisible by
the next power unless the scalar is zero. -/
theorem scalar_eq_zero_of_succ_coordinate_pow_dvd
    (c : ℂ) (e : ℕ)
    (hdiv : Germ.coordinate (0 : Fin 1) ^ (e + 1) ∣
      Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ e) :
    c = 0 := by
  by_contra hc
  have hunit : IsUnit (Germ.constRingHom 1 c) := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    simpa using hc
  have horder :
      Germ.vanishingOrder
          (Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ e) = e := by
    apply Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hunit
    ring
  have hle := Germ.vanishingOrder_le_iff_dvd.mpr hdiv
  rw [Germ.vanishingOrder_coordinate_pow, horder] at hle
  have hnat : e + 1 ≤ e := ENat.natCast_le_natCast.mp hle
  omega

/-- Analytic divisibility by a second coordinate power eliminates every
coefficient of the weighted polynomial initial form whose forced second
coordinate exponent is smaller than that power. -/
theorem finSuccEquiv_coeff_eq_zero_of_dvd_weighted_initial_form
    (a D N : ℕ) (h : Germ 2) (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (htail : h - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (D + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ N ∣ h)
    (k : ℕ) (hak : a * k ≤ D) (hexponent : D - a * k < N) :
    (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k = 0 := by
  let e := D - a * k
  let q := (MvPolynomial.finSuccEquiv ℂ 1 P).coeff k
  let c := q.coeff (Finsupp.single (0 : Fin 1) e)
  let tail := h - Germ.coordinatePolynomialAlgHom 2 P
  have he : D + 1 - a * k = e + 1 := by
    dsimp only [e]
    omega
  have htailDiv :
      Germ.coordinate (0 : Fin 1) ^ (e + 1) ∣
        Germ.firstCoordinateTaylorCoefficient k tail := by
    have hraw :=
      Germ.coordinate_pow_dvd_firstCoordinateTaylorCoefficient_of_mem_weightedOrderIdeal
        a (D + 1) tail htail k
    simpa only [he] using hraw
  have hcoordinate :
      Germ.hyperplaneExtension 1
          (Germ.coordinate (0 : Fin 1) ^ N) =
        Germ.coordinate (1 : Fin 2) ^ N := by
    rw [map_pow, Germ.hyperplaneExtension_coordinate_plane]
  have hhDivN :
      Germ.coordinate (0 : Fin 1) ^ N ∣
        Germ.firstCoordinateTaylorCoefficient k h := by
    obtain ⟨r, hr⟩ := hdiv
    refine ⟨Germ.firstCoordinateTaylorCoefficient k r, ?_⟩
    rw [hr, ← hcoordinate,
      Germ.firstCoordinateTaylorCoefficient_hyperplaneExtension_mul]
  have heN : e + 1 ≤ N := by
    dsimp only [e] at hexponent ⊢
    omega
  have hhDiv :
      Germ.coordinate (0 : Fin 1) ^ (e + 1) ∣
        Germ.firstCoordinateTaylorCoefficient k h :=
    dvd_trans (pow_dvd_pow _ heN) hhDivN
  have htailAdd :
      tail + Germ.coordinatePolynomialAlgHom 2 P = h := by
    dsimp only [tail]
    ring
  have hseries := congrArg (Germ.firstCoordinateFormalRingHom 1) htailAdd
  have hcoefficient := congrArg (PowerSeries.coeff k) hseries
  have hcoefficientAdd :
      Germ.firstCoordinateTaylorCoefficient k tail +
          Germ.firstCoordinateTaylorCoefficient k
            (Germ.coordinatePolynomialAlgHom 2 P) =
        Germ.firstCoordinateTaylorCoefficient k h := by
    simpa only [map_add, Germ.firstCoordinateFormalRingHom_apply,
      Germ.firstCoordinateFormalSeries_coeff] using hcoefficient
  have hpolynomialCoefficient :
      Germ.firstCoordinateTaylorCoefficient k
          (Germ.coordinatePolynomialAlgHom 2 P) =
        Germ.firstCoordinateTaylorCoefficient k h -
          Germ.firstCoordinateTaylorCoefficient k tail := by
    apply eq_sub_of_add_eq
    simpa only [add_comm] using hcoefficientAdd
  have hpolynomialDiv :
      Germ.coordinate (0 : Fin 1) ^ (e + 1) ∣
        Germ.firstCoordinateTaylorCoefficient k
          (Germ.coordinatePolynomialAlgHom 2 P) := by
    rw [hpolynomialCoefficient]
    exact dvd_sub hhDiv htailDiv
  have hformula :
      Germ.firstCoordinateTaylorCoefficient k
          (Germ.coordinatePolynomialAlgHom 2 P) =
        Germ.constRingHom 1 c * Germ.coordinate (0 : Fin 1) ^ e := by
    simpa only [e, q, c] using
      Germ.firstCoordinateTaylorCoefficient_coordinatePolynomial_of_weightedHomogeneous
        a D P hP k
  have hc : c = 0 := by
    apply Germ.scalar_eq_zero_of_succ_coordinate_pow_dvd c e
    simpa only [← hformula] using hpolynomialDiv
  have hmonomial :
      q = MvPolynomial.monomial
        (Finsupp.single (0 : Fin 1) e) c := by
    simpa only [e, q, c] using
      finSuccEquiv_coeff_eq_weighted_monomial a D P hP k
  change q = 0
  rw [hmonomial, hc]
  simp

end Germ

end OnLeConjecture.Analytic
