/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PolynomialCoordinates
public import OnLeConjecture.Analytic.OneVariableOrder
public import OnLeConjecture.Analytic.Pullback
public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra
public import OnLeConjecture.Polynomial.WeightedJacobian

/-!
# Weighted polynomial initial forms

Coordinate evaluation sends a weighted homogeneous polynomial of degree `D`
to the weighted order ideal with threshold `D`. Partial differentiation lowers
the threshold by the weight of the chosen coordinate. These facts identify the
weighted polynomial initial form of an analytic Jacobian.
-/

public section

namespace OnLeConjecture.Analytic

open scoped BigOperators

/-- Evaluation of a weighted homogeneous polynomial commutes with weighted
scalar multiplication in any commutative target semiring. -/
theorem eval₂_weighted_smul_of_isWeightedHomogeneous
    {R S sigma : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) {P : MvPolynomial sigma R} {w : sigma → ℕ} {D : ℕ}
    (hP : P.IsWeightedHomogeneous w D) (lambda : S) (z : sigma → S) :
    MvPolynomial.eval₂ f (fun i ↦ lambda ^ w i * z i) P =
      lambda ^ D * MvPolynomial.eval₂ f z P := by
  classical
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [MvPolynomial.eval₂_add, ihp, ihq, mul_add]
  | monomial d c hd =>
      rw [MvPolynomial.eval₂_monomial, MvPolynomial.eval₂_monomial]
      simp only [Finsupp.prod]
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.prod_mul_distrib]
      rw [Finset.prod_pow_eq_pow_sum]
      have hsum : ∑ i ∈ d.support, w i * d i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum, mul_comm] using hd
      rw [hsum]
      ring

namespace Germ

/-- The weighted analytic line through `z`. -/
@[expose]
noncomputable def weightedLineMap
    (a : ℕ) (z : Source 2) (t : Source 1) : Source 2 :=
  fun i ↦ t 0 ^ ![a, 1] i * z i

theorem weightedLineMap_analyticAt (a : ℕ) (z : Source 2) :
    AnalyticAt ℂ (Germ.weightedLineMap a z) 0 := by
  apply AnalyticAt.pi
  intro i
  exact (((ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 1 ↦ ℂ) (0 : Fin 1)).analyticAt 0).pow
      (![a, 1] i)).mul analyticAt_const

theorem weightedLineMap_zero
    (a : ℕ) (ha : 0 < a) (z : Source 2) :
    Germ.weightedLineMap a z (0 : Source 1) = 0 := by
  funext i
  fin_cases i
  · simp [Germ.weightedLineMap, zero_pow ha.ne']
  · simp [Germ.weightedLineMap]

/-- The pointed germ represented by the weighted analytic line through `z`.
-/
@[expose]
noncomputable def weightedLineMapGerm
    (a : ℕ) (ha : 0 < a) (z : Source 2) : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (Germ.weightedLineMap a z)
    (Germ.weightedLineMap_analyticAt a z)
    (Germ.weightedLineMap_zero a ha z)

@[simp]
theorem weightedLineMapGerm_pullback_coordinate
    (a : ℕ) (ha : 0 < a) (z : Source 2) (i : Fin 2) :
    (Germ.weightedLineMapGerm a ha z).pullbackRingHom
        (Germ.coordinate i) =
      Germ.coordinate (0 : Fin 1) ^ ![a, 1] i *
        Germ.constRingHom 1 (z i) := by
  rw [PointedMapGerm.pullback_coordinate]
  simp only [Germ.weightedLineMapGerm, PointedMapGerm.ofFunction]
  apply Subtype.ext
  rw [MapGerm.component_ofFunction]
  rfl

/-- Pulling back a coordinate polynomial evaluates it at the pulled back
coordinates. -/
theorem PointedMapGerm.pullback_coordinatePolynomialAlgHom
    {n m : ℕ} (gamma : PointedMapGerm n m)
    (P : MvPolynomial (Fin m) ℂ) :
    gamma.pullbackRingHom (Germ.coordinatePolynomialAlgHom m P) =
      MvPolynomial.eval₂ (Germ.constRingHom n)
        (fun i ↦ gamma.pullbackRingHom (Germ.coordinate i)) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [Germ.coordinatePolynomialAlgHom_C,
        PointedMapGerm.pullback_constRingHom, MvPolynomial.eval₂_C]
  | add P Q hP hQ =>
      rw [map_add, map_add, MvPolynomial.eval₂_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, hP, Germ.coordinatePolynomialAlgHom_X]

/-- Evaluating a complex polynomial at constant germs gives the constant germ
of its scalar evaluation. -/
theorem eval₂_constRingHom_eq_constRingHom_eval
    {n m : ℕ} (z : Fin m → ℂ) (P : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.eval₂ (Germ.constRingHom n)
        (fun i ↦ Germ.constRingHom n (z i)) P =
      Germ.constRingHom n (MvPolynomial.eval z P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      rw [MvPolynomial.eval₂_add, hP, hQ]
      rw [MvPolynomial.eval_add, map_add]
  | mul_X P i hP =>
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hP]
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, map_mul]

/-- Pulling back a weighted homogeneous coordinate polynomial to a weighted
line produces its scalar value times the prescribed coordinate power. -/
theorem weightedLineMapGerm_pullback_coordinatePolynomial
    (a D : ℕ) (ha : 0 < a) (z : Source 2)
    {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![a, 1] D) :
    (Germ.weightedLineMapGerm a ha z).pullbackRingHom
        (Germ.coordinatePolynomialAlgHom 2 P) =
      Germ.coordinate (0 : Fin 1) ^ D *
        Germ.constRingHom 1 (MvPolynomial.eval z P) := by
  rw [PointedMapGerm.pullback_coordinatePolynomialAlgHom]
  simp_rw [Germ.weightedLineMapGerm_pullback_coordinate]
  rw [eval₂_weighted_smul_of_isWeightedHomogeneous
    (Germ.constRingHom 1) hP]
  rw [Germ.eval₂_constRingHom_eq_constRingHom_eval]

/-- Pullback to a weighted line sends the weighted order ideal with threshold
`D` into the `D`th power of the one variable maximal ideal. -/
theorem weightedLineMapGerm_pullback_mem_maximalIdeal_pow
    (a D : ℕ) (ha : 0 < a) (z : Source 2) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a D) :
    (Germ.weightedLineMapGerm a ha z).pullbackRingHom f ∈
      Germ.maximalIdeal 1 ^ D := by
  rw [Germ.mem_weightedOrderIdeal_iff] at hf
  obtain ⟨c, hc⟩ := hf
  rw [← hc, map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [map_mul]
  apply Ideal.mul_mem_left
  let u := (k : ℕ)
  let v := D - a * u
  let W := a * u + v
  have hweight : D ≤ W := by
    dsimp only [W, v, u]
    omega
  have hcoordinate :
      (Germ.weightedLineMapGerm a ha z).pullbackRingHom
          (Germ.weightedOrderGenerator a D k) =
        (Germ.constRingHom 1 (z 0) ^ u *
            Germ.constRingHom 1 (z 1) ^ v) *
          Germ.coordinate (0 : Fin 1) ^ W := by
    simp only [Germ.weightedOrderGenerator, map_mul, map_pow,
      Germ.weightedLineMapGerm_pullback_coordinate, u, v, W]
    norm_num
    rw [mul_pow, mul_pow, ← pow_mul]
    calc
      Germ.coordinate (0 : Fin 1) ^ (a * (k : ℕ)) *
            Germ.constRingHom 1 (z 0) ^ (k : ℕ) *
          (Germ.coordinate (0 : Fin 1) ^ (D - a * (k : ℕ)) *
            Germ.constRingHom 1 (z 1) ^ (D - a * (k : ℕ))) =
        (Germ.constRingHom 1 (z 0) ^ (k : ℕ) *
            Germ.constRingHom 1 (z 1) ^ (D - a * (k : ℕ))) *
          (Germ.coordinate (0 : Fin 1) ^ (a * (k : ℕ)) *
            Germ.coordinate (0 : Fin 1) ^ (D - a * (k : ℕ))) := by
              ring
      _ = _ := by rw [← pow_add]
  rw [hcoordinate]
  apply Ideal.mul_mem_left
  exact Ideal.pow_le_pow_right hweight
    (Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal 0) W)

/-- A weighted homogeneous polynomial of degree `D` cannot evaluate into the
weighted order ideal with threshold `D+1` unless it is zero. -/
theorem eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ
    (a D : ℕ) (ha : 0 < a) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (hmem : Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (D + 1)) :
    P = 0 := by
  apply MvPolynomial.funext
  intro z
  change MvPolynomial.eval z P = 0
  by_contra hz
  have hpull :
      (Germ.weightedLineMapGerm a ha z).pullbackRingHom
          (Germ.coordinatePolynomialAlgHom 2 P) ∈
        Germ.maximalIdeal 1 ^ (D + 1) :=
    Germ.weightedLineMapGerm_pullback_mem_maximalIdeal_pow
      a (D + 1) ha z hmem
  have hscale := Germ.weightedLineMapGerm_pullback_coordinatePolynomial
    a D ha z hP
  have hu : IsUnit (Germ.constRingHom 1 (MvPolynomial.eval z P)) := by
    apply Germ.isUnit_of_valueRingHom_ne_zero
    simpa using hz
  have horder :
      Germ.vanishingOrder
          ((Germ.weightedLineMapGerm a ha z).pullbackRingHom
            (Germ.coordinatePolynomialAlgHom 2 P)) = D := by
    rw [hscale]
    exact Germ.vanishingOrder_eq_of_eq_coordinate_pow_mul_unit hu rfl
  have hle := Germ.mem_maximalIdeal_one_pow_iff.mp hpull
  rw [horder] at hle
  have hlt : (D : ℕ∞) < ((D + 1 : ℕ) : ℕ∞) :=
    ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self D)
  have hlt' : (D : ℕ∞) < (D : ℕ∞) + 1 := by
    simpa using hlt
  exact (not_lt_of_ge hle) hlt'

/-- If an analytic germ with weighted initial form `P` is divisible by the
`D`th power of the second coordinate, then `P` is a scalar multiple of that
power. -/
theorem exists_eq_C_mul_second_pow_of_dvd_coordinatePolynomial_initialForm
    (a D : ℕ) (ha : 0 < a) (h : Germ 2)
    (P : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] D)
    (htail : h - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (D + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ D ∣ h) :
    ∃ c : ℂ,
      P = MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ D := by
  obtain ⟨q, hq⟩ := hdiv
  let c := Germ.valueRingHom 2 q
  have hqTail : q - Germ.constRingHom 2 c ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    simp [c]
  have hqWeighted : q - Germ.constRingHom 2 c ∈
      Germ.weightedOrderIdeal a 1 := by
    rw [Germ.weightedOrderIdeal_one_eq_maximalIdeal a ha]
    exact hqTail
  have hyOrder : Germ.coordinate (1 : Fin 2) ^ D ∈
      Germ.weightedOrderIdeal a D := by
    simpa only [pow_zero, one_mul] using
      Germ.monomial_mem_weightedOrderIdeal_of_threshold
        a D 0 D ha (by simp)
  have hproduct := Germ.weightedOrderIdeal_mul_mem
    a D 1 ha hyOrder hqWeighted
  have hhTail :
      h - Germ.coordinate (1 : Fin 2) ^ D * Germ.constRingHom 2 c ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    rw [hq]
    convert hproduct using 1
    ring
  have hpolynomialGerm :
      Germ.coordinatePolynomialAlgHom 2 P -
          Germ.coordinate (1 : Fin 2) ^ D * Germ.constRingHom 2 c ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    have hsum := (Germ.weightedOrderIdeal a (D + 1)).add_mem
      ((Germ.weightedOrderIdeal a (D + 1)).neg_mem htail) hhTail
    convert hsum using 1
    ring
  have hyHomogeneous :
      (MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ D :
          MvPolynomial (Fin 2) ℂ).IsWeightedHomogeneous ![a, 1] D := by
    have hy := (MvPolynomial.isWeightedHomogeneous_X
      ℂ ![a, 1] (1 : Fin 2)).pow D
    norm_num at hy
    exact hy.C_mul c
  have hdifferenceHomogeneous :
      MvPolynomial.IsWeightedHomogeneous ![a, 1]
        (P - MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ D) D :=
    hP.sub hyHomogeneous
  have hdifferenceGerm :
      Germ.coordinatePolynomialAlgHom 2
          (P - MvPolynomial.C c * MvPolynomial.X (1 : Fin 2) ^ D) ∈
        Germ.weightedOrderIdeal a (D + 1) := by
    simpa only [map_sub, map_mul, map_pow,
      Germ.coordinatePolynomialAlgHom_C,
      Germ.coordinatePolynomialAlgHom_X, mul_comm] using hpolynomialGerm
  have hdifferenceZero :=
    Germ.eq_zero_of_isWeightedHomogeneous_coordinatePolynomial_mem_succ
      a D ha hdifferenceHomogeneous hdifferenceGerm
  refine ⟨c, ?_⟩
  exact sub_eq_zero.mp hdifferenceZero

private theorem finsupp_prod_coordinate_fin_two
    (d : Fin 2 →₀ ℕ) :
    d.prod (fun i e ↦ Germ.coordinate i ^ e) =
      Germ.coordinate (0 : Fin 2) ^ d 0 *
        Germ.coordinate (1 : Fin 2) ^ d 1 := by
  rw [Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two]
  · intro i
    simp

/-- Coordinate evaluation of a weighted homogeneous polynomial belongs to
the weighted order ideal determined by its degree. -/
theorem coordinatePolynomial_mem_weightedOrderIdeal
    (a D : ℕ) (ha : 0 < a) {P : MvPolynomial (Fin 2) ℂ}
    (hP : P.IsWeightedHomogeneous ![a, 1] D) :
    Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a D := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact (Germ.weightedOrderIdeal a D).add_mem ihp ihq
  | monomial d c hd =>
      rw [Germ.coordinatePolynomialAlgHom,
        MvPolynomial.aeval_monomial]
      change Germ.constRingHom 2 c *
          d.prod (fun i e ↦ Germ.coordinate i ^ e) ∈ _
      rw [finsupp_prod_coordinate_fin_two]
      apply Ideal.mul_mem_left
      apply Germ.monomial_mem_weightedOrderIdeal_of_threshold
        a D (d 0) (d 1) ha
      have hsum : ∑ i : Fin 2, d i * ![a, 1] i = D := by
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using hd
      rw [Fin.sum_univ_two] at hsum
      norm_num at hsum ⊢
      calc
        D = d 0 * a + d 1 := hsum.symm
        _ = a * d 0 + d 1 := by rw [mul_comm]
        _ ≤ a * d 0 + d 1 := le_rfl

/-- Partial differentiation commutes with evaluation at the coordinate
germs. -/
theorem partialDerivative_coordinatePolynomialAlgHom
    {n : ℕ} (i : Fin n) (P : MvPolynomial (Fin n) ℂ) :
    Germ.partialDerivative i (Germ.coordinatePolynomialAlgHom n P) =
      Germ.coordinatePolynomialAlgHom n (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [Germ.coordinatePolynomialAlgHom_C,
        Germ.partialDerivative_const, MvPolynomial.pderiv_C, map_zero]
  | add P Q hP hQ =>
      rw [map_add, Germ.partialDerivative_add, map_add, map_add, hP, hQ]
  | mul_X P j hP =>
      rw [map_mul, Germ.partialDerivative_mul, hP,
        MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
      rw [Germ.coordinatePolynomialAlgHom_X]
      by_cases hij : i = j
      · subst j
        rw [MvPolynomial.pderiv_X_self,
          Germ.partialDerivative_coordinate_same, map_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij),
          Germ.partialDerivative_coordinate_ne hij, map_zero]

/-- The analytic Jacobian of coordinate polynomials is their polynomial
Jacobian evaluated at the coordinate germs. -/
theorem jacobian_coordinatePolynomialAlgHom
    (P Q : MvPolynomial (Fin 2) ℂ) :
    Germ.jacobian (Germ.coordinatePolynomialAlgHom 2 P)
        (Germ.coordinatePolynomialAlgHom 2 Q) =
      Germ.coordinatePolynomialAlgHom 2
        (OnLeConjecture.Polynomial.jacobian P Q) := by
  simp only [Germ.jacobian_eq, OnLeConjecture.Polynomial.jacobian,
    Germ.partialDerivative_coordinatePolynomialAlgHom, map_mul, map_sub]

/-- The Jacobian of two analytic germs has the Jacobian of their weighted
initial forms as its weighted initial form. -/
theorem jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
    (a m n : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1)) :
    Germ.jacobian f g -
        Germ.coordinatePolynomialAlgHom 2
          (OnLeConjecture.Polynomial.jacobian P Q) ∈
      Germ.weightedOrderIdeal a (m + n - a) := by
  let PGerm := Germ.coordinatePolynomialAlgHom 2 P
  let QGerm := Germ.coordinatePolynomialAlgHom 2 Q
  have hmone : 1 ≤ m := by omega
  have hnone : 1 ≤ n := by omega
  have hfzero :
      Germ.partialDerivative (0 : Fin 2) f -
          Germ.partialDerivative 0 PGerm ∈
        Germ.weightedOrderIdeal a (m - a + 1) := by
    rw [← Germ.partialDerivative_sub]
    apply Germ.partialDerivative_zero_mem_weightedOrderIdeal a (m - a + 1) ha
    simpa only [show m - a + 1 + a = m + 1 by omega] using hf
  have hfone :
      Germ.partialDerivative (1 : Fin 2) f -
          Germ.partialDerivative 1 PGerm ∈
        Germ.weightedOrderIdeal a m := by
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_one_mem_weightedOrderIdeal a m ha hf
  have hgzero :
      Germ.partialDerivative (0 : Fin 2) g -
          Germ.partialDerivative 0 QGerm ∈
        Germ.weightedOrderIdeal a (n - a + 1) := by
    rw [← Germ.partialDerivative_sub]
    apply Germ.partialDerivative_zero_mem_weightedOrderIdeal a (n - a + 1) ha
    simpa only [show n - a + 1 + a = n + 1 by omega] using hg
  have hgone :
      Germ.partialDerivative (1 : Fin 2) g -
          Germ.partialDerivative 1 QGerm ∈
        Germ.weightedOrderIdeal a n := by
    rw [← Germ.partialDerivative_sub]
    exact Germ.partialDerivative_one_mem_weightedOrderIdeal a n ha hg
  have hPzero : Germ.partialDerivative (0 : Fin 2) PGerm ∈
      Germ.weightedOrderIdeal a (m - a) := by
    change Germ.partialDerivative (0 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 P) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (m - a) ha (hP.pderiv (Nat.sub_add_cancel ham))
  have hPone : Germ.partialDerivative (1 : Fin 2) PGerm ∈
      Germ.weightedOrderIdeal a (m - 1) := by
    change Germ.partialDerivative (1 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 P) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (m - 1) ha (hP.pderiv (Nat.sub_add_cancel hmone))
  have hQzero : Germ.partialDerivative (0 : Fin 2) QGerm ∈
      Germ.weightedOrderIdeal a (n - a) := by
    change Germ.partialDerivative (0 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 Q) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (n - a) ha (hQ.pderiv (Nat.sub_add_cancel han))
  have hQone : Germ.partialDerivative (1 : Fin 2) QGerm ∈
      Germ.weightedOrderIdeal a (n - 1) := by
    change Germ.partialDerivative (1 : Fin 2)
      (Germ.coordinatePolynomialAlgHom 2 Q) ∈ _
    rw [Germ.partialDerivative_coordinatePolynomialAlgHom]
    exact Germ.coordinatePolynomial_mem_weightedOrderIdeal
      a (n - 1) ha (hQ.pderiv (Nat.sub_add_cancel hnone))
  have hfzeroOrder : Germ.partialDerivative (0 : Fin 2) f ∈
      Germ.weightedOrderIdeal a (m - a) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (m - a) (m - a + 1) ha (by omega) hfzero
    have hsum := (Germ.weightedOrderIdeal a (m - a)).add_mem
      htail hPzero
    convert hsum using 1
    ring
  have hfoneOrder : Germ.partialDerivative (1 : Fin 2) f ∈
      Germ.weightedOrderIdeal a (m - 1) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (m - 1) m ha (by omega) hfone
    have hsum := (Germ.weightedOrderIdeal a (m - 1)).add_mem
      htail hPone
    convert hsum using 1
    ring
  have hgzeroOrder : Germ.partialDerivative (0 : Fin 2) g ∈
      Germ.weightedOrderIdeal a (n - a) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (n - a) (n - a + 1) ha (by omega) hgzero
    have hsum := (Germ.weightedOrderIdeal a (n - a)).add_mem
      htail hQzero
    convert hsum using 1
    ring
  have hgoneOrder : Germ.partialDerivative (1 : Fin 2) g ∈
      Germ.weightedOrderIdeal a (n - 1) := by
    have htail := Germ.weightedOrderIdeal_antitone
      a (n - 1) n ha (by omega) hgone
    have hsum := (Germ.weightedOrderIdeal a (n - 1)).add_mem
      htail hQone
    convert hsum using 1
    ring
  have hfirstTail := Germ.weightedOrderIdeal_mul_mem
    a (m - a + 1) (n - 1) ha hfzero hgoneOrder
  have hfirstPolynomial := Germ.weightedOrderIdeal_mul_mem
    a (m - a) n ha hPzero hgone
  have hfirst :
      Germ.partialDerivative (0 : Fin 2) f *
            Germ.partialDerivative (1 : Fin 2) g -
          Germ.partialDerivative 0 PGerm *
            Germ.partialDerivative 1 QGerm ∈
        Germ.weightedOrderIdeal a (m + n - a) := by
    have htail :
        (Germ.partialDerivative (0 : Fin 2) f -
              Germ.partialDerivative 0 PGerm) *
            Germ.partialDerivative (1 : Fin 2) g ∈
          Germ.weightedOrderIdeal a (m + n - a) := by
      simpa only [show m - a + 1 + (n - 1) = m + n - a by omega] using
        hfirstTail
    have hpolynomial :
        Germ.partialDerivative (0 : Fin 2) PGerm *
            (Germ.partialDerivative (1 : Fin 2) g -
              Germ.partialDerivative 1 QGerm) ∈
          Germ.weightedOrderIdeal a (m + n - a) := by
      simpa only [show m - a + n = m + n - a by omega] using
        hfirstPolynomial
    have hsum := (Germ.weightedOrderIdeal a (m + n - a)).add_mem
      htail hpolynomial
    convert hsum using 1
    ring
  have hsecondTail := Germ.weightedOrderIdeal_mul_mem
    a m (n - a) ha hfone hgzeroOrder
  have hsecondPolynomial := Germ.weightedOrderIdeal_mul_mem
    a (m - 1) (n - a + 1) ha hPone hgzero
  have hsecond :
      Germ.partialDerivative (1 : Fin 2) f *
            Germ.partialDerivative (0 : Fin 2) g -
          Germ.partialDerivative 1 PGerm *
            Germ.partialDerivative 0 QGerm ∈
        Germ.weightedOrderIdeal a (m + n - a) := by
    have htail :
        (Germ.partialDerivative (1 : Fin 2) f -
              Germ.partialDerivative 1 PGerm) *
            Germ.partialDerivative (0 : Fin 2) g ∈
          Germ.weightedOrderIdeal a (m + n - a) := by
      simpa only [show m + (n - a) = m + n - a by omega] using
        hsecondTail
    have hpolynomial :
        Germ.partialDerivative (1 : Fin 2) PGerm *
            (Germ.partialDerivative (0 : Fin 2) g -
              Germ.partialDerivative 0 QGerm) ∈
          Germ.weightedOrderIdeal a (m + n - a) := by
      simpa only [show m - 1 + (n - a + 1) = m + n - a by omega] using
        hsecondPolynomial
    have hsum := (Germ.weightedOrderIdeal a (m + n - a)).add_mem
      htail hpolynomial
    convert hsum using 1
    ring
  have hdifference := (Germ.weightedOrderIdeal a (m + n - a)).sub_mem
    hfirst hsecond
  rw [← Germ.jacobian_coordinatePolynomialAlgHom]
  simp only [Germ.jacobian_eq]
  convert hdifference using 1
  ring

/-- Analytic divisibility of a Jacobian by its full second coordinate power
passes to the weighted polynomial initial forms. -/
theorem exists_jacobian_eq_C_mul_second_pow_of_analytic_divisibility
    (a m n : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m + n - a - 1) ∣
      Germ.jacobian f g) :
    ∃ c : ℂ,
      OnLeConjecture.Polynomial.jacobian P Q =
        MvPolynomial.C c *
          MvPolynomial.X (1 : Fin 2) ^ (m + n - a - 1) := by
  have hmone : 1 ≤ m := by omega
  have hnone : 1 ≤ n := by omega
  have hJacobianHomogeneous :
      MvPolynomial.IsWeightedHomogeneous ![a, 1]
        (OnLeConjecture.Polynomial.jacobian P Q)
          (m + n - a - 1) := by
    have hhomogeneous :=
      OnLeConjecture.Polynomial.isWeightedHomogeneous_jacobian
        ![a, 1] P Q m n hP hQ ham hmone han hnone
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      show (m - a) + (n - 1) = m + n - a - 1 by omega] using
        hhomogeneous
  have htail :=
    Germ.jacobian_sub_coordinatePolynomial_mem_weightedOrderIdeal
      a m n ha ham han P Q hP hQ f g hf hg
  apply Germ.exists_eq_C_mul_second_pow_of_dvd_coordinatePolynomial_initialForm
    a (m + n - a - 1) ha (Germ.jacobian f g)
      (OnLeConjecture.Polynomial.jacobian P Q)
      hJacobianHomogeneous
  · simpa only [show m + n - a - 1 + 1 = m + n - a by omega] using
      htail
  · exact hdiv

/-- If the polynomial Jacobian is nonzero, the scalar obtained from analytic
divisibility is nonzero. -/
theorem exists_jacobian_eq_ne_zero_C_mul_second_pow_of_analytic_divisibility
    (a m n : ℕ) (ha : 0 < a) (ham : a ≤ m) (han : a ≤ n)
    (P Q : MvPolynomial (Fin 2) ℂ)
    (hP : P.IsWeightedHomogeneous ![a, 1] m)
    (hQ : Q.IsWeightedHomogeneous ![a, 1] n)
    (f g : Germ 2)
    (hf : f - Germ.coordinatePolynomialAlgHom 2 P ∈
      Germ.weightedOrderIdeal a (m + 1))
    (hg : g - Germ.coordinatePolynomialAlgHom 2 Q ∈
      Germ.weightedOrderIdeal a (n + 1))
    (hdiv : Germ.coordinate (1 : Fin 2) ^ (m + n - a - 1) ∣
      Germ.jacobian f g)
    (hJacobian : OnLeConjecture.Polynomial.jacobian P Q ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      OnLeConjecture.Polynomial.jacobian P Q =
        MvPolynomial.C c *
          MvPolynomial.X (1 : Fin 2) ^ (m + n - a - 1) := by
  obtain ⟨c, hc⟩ :=
    Germ.exists_jacobian_eq_C_mul_second_pow_of_analytic_divisibility
      a m n ha ham han P Q hP hQ f g hf hg hdiv
  refine ⟨c, ?_, hc⟩
  intro hcZero
  subst c
  have hzero : OnLeConjecture.Polynomial.jacobian P Q = 0 := by
    simpa only [map_zero, zero_mul] using hc
  exact hJacobian hzero

end Germ

end OnLeConjecture.Analytic
