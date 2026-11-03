/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.DTwo.CyclicComponentDomain
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Polynomial identities from the affine cyclic component

The variable order in the three-variable polynomial ring is `(X,x,y)`.
The component equation is `X²-x²-c*y^L`. Its primality is transported
from the proved iterated-polynomial calculation. Weighted homogeneity
extends an identity on the chart `y=1, X≠0` to `y*X≠0`. The polynomial
Nullstellensatz and primality then give divisibility by the component
equation, including at the points omitted from that chart.
-/

public section

namespace OnLeConjecture.DTwo

open scoped BigOperators

/-- The coordinate equation, with variables ordered as `(X,x,y)`. -/
@[expose] noncomputable def cyclicComponentRelation (L : ℕ) (c : ℂ) :
    MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 ^ 2 - MvPolynomial.X 1 ^ 2 - MvPolynomial.C c * MvPolynomial.X 2 ^ L

@[expose] noncomputable def cyclicBaseCoordinateEquiv :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] CyclicBaseRing :=
  (MvPolynomial.finSuccEquiv ℂ 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)))

private theorem cyclicBaseCoordinateEquiv_first :
    cyclicBaseCoordinateEquiv (MvPolynomial.X 0) = Polynomial.X := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

private theorem cyclicBaseCoordinateEquiv_second :
    cyclicBaseCoordinateEquiv (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv ℂ 1 (MvPolynomial.X 1)) = _
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

/-- The three-variable ring as `ℂ[y][x][X]`. -/
@[expose] noncomputable def cyclicComponentCoordinateEquiv :
    MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] Polynomial CyclicBaseRing :=
  (MvPolynomial.finSuccEquiv ℂ 2).trans (Polynomial.mapAlgEquiv cyclicBaseCoordinateEquiv)

@[simp] theorem cyclicComponentCoordinateEquiv_zero :
    cyclicComponentCoordinateEquiv (MvPolynomial.X 0) = Polynomial.X := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X 0)) = _
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] theorem cyclicComponentCoordinateEquiv_one :
    cyclicComponentCoordinateEquiv (MvPolynomial.X 1) = Polynomial.C Polynomial.X := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X 1)) = _
  rw [show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  exact congrArg Polynomial.C cyclicBaseCoordinateEquiv_first

@[simp] theorem cyclicComponentCoordinateEquiv_two :
    cyclicComponentCoordinateEquiv (MvPolynomial.X 2) =
      Polynomial.C (Polynomial.C Polynomial.X) := by
  change Polynomial.map _ (MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X 2)) = _
  rw [show (2 : Fin 3) = (1 : Fin 2).succ from rfl,
    MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  exact congrArg Polynomial.C cyclicBaseCoordinateEquiv_second

@[simp] theorem cyclicComponentCoordinateEquiv_C (c : ℂ) :
    cyclicComponentCoordinateEquiv (MvPolynomial.C c) =
      Polynomial.C (Polynomial.C (Polynomial.C c)) := by
  exact cyclicComponentCoordinateEquiv.commutes c

@[simp] theorem cyclicComponentCoordinateEquiv_relation (L : ℕ) (c : ℂ) :
    cyclicComponentCoordinateEquiv (cyclicComponentRelation L c) =
      cyclicComponentPolynomial L c := by
  simp only [cyclicComponentRelation, map_sub, map_pow, map_mul,
    cyclicComponentCoordinateEquiv_zero, cyclicComponentCoordinateEquiv_one,
    cyclicComponentCoordinateEquiv_two, cyclicComponentCoordinateEquiv_C,
    cyclicComponentPolynomial, cyclicSquare, map_add]
  ring

theorem cyclicComponentRelation_prime (L : ℕ) (c : ℂ) (hc : c ≠ 0) :
    Prime (cyclicComponentRelation L c) := by
  apply (MulEquiv.prime_iff cyclicComponentCoordinateEquiv).mp
  rw [cyclicComponentCoordinateEquiv_relation]
  exact cyclicComponentPolynomial_prime L hc

private theorem cyclicComponentRelation_not_dvd_zero (L : ℕ) (c : ℂ) :
    ¬ cyclicComponentRelation L c ∣ MvPolynomial.X 0 := by
  intro h
  have hd := map_dvd cyclicComponentCoordinateEquiv h
  rw [cyclicComponentCoordinateEquiv_relation, cyclicComponentCoordinateEquiv_zero] at hd
  have hn := Polynomial.natDegree_le_of_dvd hd Polynomial.X_ne_zero
  simp [cyclicComponentPolynomial] at hn

private theorem cyclicComponentRelation_not_dvd_two (L : ℕ) (c : ℂ) :
    ¬ cyclicComponentRelation L c ∣ MvPolynomial.X 2 := by
  intro h
  have hd := map_dvd cyclicComponentCoordinateEquiv h
  rw [cyclicComponentCoordinateEquiv_relation, cyclicComponentCoordinateEquiv_two] at hd
  have hn := Polynomial.natDegree_le_of_dvd hd
    (Polynomial.C_ne_zero.mpr (Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero))
  simp [cyclicComponentPolynomial] at hn

/-- Vanishing on the open subset where `X*y≠0` is sufficient for an
identity on the whole irreducible polynomial component. -/
theorem cyclicComponentRelation_dvd_of_vanishing_on_open
    (L : ℕ) (c : ℂ) (hc : c ≠ 0) (Q : MvPolynomial (Fin 3) ℂ)
    (hzero : ∀ z : Fin 3 → ℂ, z 0 ≠ 0 → z 2 ≠ 0 →
      z 0 ^ 2 = z 1 ^ 2 + c * z 2 ^ L → MvPolynomial.eval z Q = 0) :
    cyclicComponentRelation L c ∣ Q := by
  let I := Ideal.span ({cyclicComponentRelation L c} : Set (MvPolynomial (Fin 3) ℂ))
  have hprime := cyclicComponentRelation_prime L c hc
  let : I.IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hvan : MvPolynomial.X 0 * MvPolynomial.X 2 * Q ∈
      MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    intro z hz
    have hR := hz (cyclicComponentRelation L c) (Ideal.subset_span (Set.mem_singleton _))
    have hpoint : z 0 ^ 2 = z 1 ^ 2 + c * z 2 ^ L := by
      simp only [cyclicComponentRelation, map_sub, map_pow, map_mul,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C, Algebra.algebraMap_self,
        RingHom.id_apply] at hR
      linear_combination hR
    by_cases hz0 : z 0 = 0
    · simp [hz0]
    by_cases hz2 : z 2 = 0
    · simp [hz2]
    have hQ := hzero z hz0 hz2 hpoint
    simp only [map_mul, MvPolynomial.aeval_def,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id, hQ, mul_zero]
  rw [MvPolynomial.IsPrime.vanishingIdeal_zeroLocus] at hvan
  have hd : cyclicComponentRelation L c ∣ MvPolynomial.X 0 * MvPolynomial.X 2 * Q :=
    Ideal.mem_span_singleton.mp hvan
  rcases hprime.dvd_or_dvd hd with hleft | hright
  · rcases hprime.dvd_or_dvd hleft with hx | hy
    · exact (cyclicComponentRelation_not_dvd_zero L c hx).elim
    · exact (cyclicComponentRelation_not_dvd_two L c hy).elim
  · exact hright

private theorem eval_weighted_scale_three
    {Q : MvPolynomial (Fin 3) ℂ} {w : Fin 3 → ℕ} {D : ℕ}
    (hQ : Q.IsWeightedHomogeneous w D) (t : ℂ) (z : Fin 3 → ℂ) :
    MvPolynomial.eval (fun i => t ^ w i * z i) Q = t ^ D * MvPolynomial.eval z Q := by
  induction hQ using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [MvPolynomial.eval_add, ihp, ihq, mul_add]
  | monomial d c hd =>
    rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
      Finsupp.prod_pow, Finsupp.prod_pow]
    simp_rw [mul_pow, ← pow_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hsum : ∑ i, w i * d i = D := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, mul_comm] using hd
    rw [hsum]
    ring

/-- A weighted homogeneous identity on the affine chart `y=1, X≠0`
holds modulo the component equation. No parity condition on `L` or on
the weighted degree is required for this extension. -/
theorem cyclicComponentRelation_dvd_of_weighted_chart_vanishing
    (L d : ℕ) (c : ℂ) (hc : c ≠ 0) (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : Q.IsWeightedHomogeneous ![L, L, 2] d)
    (hchart : ∀ s S : ℂ, S ≠ 0 → S ^ 2 = s ^ 2 + c →
      MvPolynomial.eval (![S, s, 1]) Q = 0) :
    cyclicComponentRelation L c ∣ Q := by
  apply cyclicComponentRelation_dvd_of_vanishing_on_open L c hc Q
  intro z hz0 hz2 hpoint
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (z 2) (by omega : 0 < (2 : ℕ))
  have ht0 : t ≠ 0 := fun h => hz2 (by simpa [h] using ht.symm)
  have htL : t ^ L ≠ 0 := pow_ne_zero L ht0
  have hpower : (t ^ L) ^ 2 = z 2 ^ L := by
    rw [← pow_mul, Nat.mul_comm L 2, pow_mul, ht]
  have hscaled : (z 0 / t ^ L) ^ 2 = (z 1 / t ^ L) ^ 2 + c := by
    rw [div_pow, div_pow]
    apply (div_eq_iff (pow_ne_zero 2 htL)).mpr
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 htL), hpower]
    exact hpoint
  have heval := hchart (z 1 / t ^ L) (z 0 / t ^ L) (div_ne_zero hz0 htL) hscaled
  have hcoordinates : (fun i : Fin 3 => t ^ (![L, L, 2] i) *
      (![z 0 / t ^ L, z 1 / t ^ L, 1] i)) = z := by
    funext i
    fin_cases i <;> simp [htL, ht, mul_div_cancel₀]
  have h := eval_weighted_scale_three hQ t (![z 0 / t ^ L, z 1 / t ^ L, 1])
  rwa [hcoordinates, heval, mul_zero] at h

end OnLeConjecture.DTwo
