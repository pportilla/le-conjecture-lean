/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.CompletionClosure
public import OnLeConjecture.Analytic.PlaneNoetherian
public import OnLeConjecture.Analytic.WeightedOrderIdealAlgebra
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Closure of principal ideals for weighted approximation

Weighted order at least `a * n` implies ordinary order at least `n`.
Consequently, approximation to every weighted order by elements of an ideal
places the limit in that ideal. In the plane germ ring a principal ideal
cannot contain a power of the maximal ideal.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- A power of a germ multiplies its weighted order by the exponent. -/
theorem pow_mem_weightedOrderIdeal_mul
    (a D s : ℕ) (ha : 0 < a) {f : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a D) :
    f ^ s ∈ Germ.weightedOrderIdeal a (D * s) := by
  induction s with
  | zero =>
      let k : Fin (0 + 1) := 0
      have hk := Germ.weightedOrderGenerator_mem a 0 k
      simpa [Germ.weightedOrderGenerator, k] using hk
  | succ s ih =>
      rw [pow_succ, Nat.mul_succ]
      exact Germ.weightedOrderIdeal_mul_mem a (D * s) D ha ih hf

/-- If two germs of weighted order `D` agree through weighted degree `D`,
their positive powers agree through the corresponding next weighted degree. -/
theorem pow_sub_pow_mem_weightedOrderIdeal
    (a D s : ℕ) (ha : 0 < a) (hs : 0 < s) {f g : Germ 2}
    (hf : f ∈ Germ.weightedOrderIdeal a D)
    (hg : g ∈ Germ.weightedOrderIdeal a D)
    (hfg : f - g ∈ Germ.weightedOrderIdeal a (D + 1)) :
    f ^ s - g ^ s ∈ Germ.weightedOrderIdeal a (D * s + 1) := by
  cases s with
  | zero => omega
  | succ s =>
    induction s with
    | zero => simpa using hfg
    | succ s ih =>
      have hfirst := Germ.weightedOrderIdeal_mul_mem
        a (D * (s + 1) + 1) D ha (ih (by omega)) hf
      have hgPower := Germ.pow_mem_weightedOrderIdeal_mul
        a D (s + 1) ha hg
      have hsecond := Germ.weightedOrderIdeal_mul_mem
        a (D * (s + 1)) (D + 1) ha hgPower hfg
      have hequality :
          f ^ (s + 2) - g ^ (s + 2) =
            (f ^ (s + 1) - g ^ (s + 1)) * f +
              g ^ (s + 1) * (f - g) := by
        ring
      rw [hequality]
      have hdegreeFirst : D * (s + 1) + 1 + D = D * (s + 2) + 1 := by
        ring
      have hdegreeSecond : D * (s + 1) + (D + 1) = D * (s + 2) + 1 := by
        ring
      rw [hdegreeFirst] at hfirst
      rw [hdegreeSecond] at hsecond
      exact (Germ.weightedOrderIdeal a (D * (s + 2) + 1)).add_mem
        hfirst hsecond

/-- Weighted order at least `a * n` implies ordinary order at least `n`. -/
theorem weightedOrderIdeal_mul_le_maximalIdeal_pow
    (a n : ℕ) (ha : 0 < a) :
    Germ.weightedOrderIdeal a (a * n) ≤ Germ.maximalIdeal 2 ^ n := by
  rw [Germ.weightedOrderIdeal, Ideal.span_le]
  intro q hq
  obtain ⟨k, rfl⟩ := hq
  let u : ℕ := k
  let v : ℕ := a * n - a * u
  have hweighted : a * n ≤ a * u + v := by
    dsimp only [v]
    omega
  have hv : v ≤ a * v := by
    calc
      v = 1 * v := by simp
      _ ≤ a * v := Nat.mul_le_mul_right v ha
  have htotal : n ≤ u + v := by
    have hmul : a * n ≤ a * (u + v) := by
      calc
        a * n ≤ a * u + v := hweighted
        _ ≤ a * u + a * v := Nat.add_le_add_left hv (a * u)
        _ = a * (u + v) := by rw [Nat.mul_add]
    exact Nat.le_of_mul_le_mul_left hmul ha
  have hx : Germ.coordinate (0 : Fin 2) ^ u ∈
      Germ.maximalIdeal 2 ^ u :=
    Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal 0) u
  have hy : Germ.coordinate (1 : Fin 2) ^ v ∈
      Germ.maximalIdeal 2 ^ v :=
    Ideal.pow_mem_pow (Germ.coordinate_mem_maximalIdeal 1) v
  have hproduct : Germ.coordinate (0 : Fin 2) ^ u *
        Germ.coordinate (1 : Fin 2) ^ v ∈
      Germ.maximalIdeal 2 ^ (u + v) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right htotal hproduct

/-- An ideal of the plane germ ring contains every germ which it approximates
to every power of the maximal ideal. -/
theorem mem_ideal_of_sub_mem_maximalIdeal_pow_all
    (J : Ideal (Germ 2)) (u : Germ 2)
    (happrox : ∀ n : ℕ, ∃ v : Germ 2, v ∈ J ∧
      u - v ∈ Germ.maximalIdeal 2 ^ n) :
    u ∈ J := by
  let _ : Module.Finite (Germ 2) (Germ 2 ⧸ J) := inferInstance
  have hHausdorff :
      IsHausdorff (Germ.maximalIdeal 2) (Germ 2 ⧸ J) := by
    rw [Germ.maximalIdeal_eq_isLocalRing]
    infer_instance
  have hzero : Ideal.Quotient.mk J u = 0 := by
    apply hHausdorff.haus
    intro n
    rw [SModEq.zero]
    obtain ⟨v, hv, huv⟩ := happrox n
    rw [Ideal.smul_top_eq_map]
    have hmap := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) huv
    simpa [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hv] using hmap
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- Approximation to every weighted order by elements of an ideal implies
membership in that ideal. -/
theorem mem_ideal_of_sub_mem_weightedOrderIdeal_all
    (a : ℕ) (ha : 0 < a) (J : Ideal (Germ 2)) (u : Germ 2)
    (happrox : ∀ D : ℕ, ∃ v : Germ 2, v ∈ J ∧
      u - v ∈ Germ.weightedOrderIdeal a D) :
    u ∈ J := by
  apply Germ.mem_ideal_of_sub_mem_maximalIdeal_pow_all J u
  intro n
  obtain ⟨v, hv, huv⟩ := happrox (a * n)
  exact ⟨v, hv,
    Germ.weightedOrderIdeal_mul_le_maximalIdeal_pow a n ha huv⟩

/-- A principal ideal in the plane germ ring cannot contain a power of the
maximal ideal when its generator vanishes at the origin. -/
theorem not_maximalIdeal_pow_le_span_singleton
    (g : Germ 2) (hg : g ∈ Germ.maximalIdeal 2) :
    ¬ ∃ N : ℕ, Germ.maximalIdeal 2 ^ N ≤ Ideal.span {g} := by
  rintro ⟨N, hN⟩
  let J : Ideal (Germ 2) := Ideal.span {g}
  have hJmaximal : J ≤ Germ.maximalIdeal 2 := by
    change Ideal.span {g} ≤ Germ.maximalIdeal 2
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hg
  have hN' : Germ.maximalIdeal 2 ^ N ≤ J := by
    simpa only [J] using hN
  have hNzero : N ≠ 0 := by
    intro hzero
    subst N
    have htopLe : (⊤ : Ideal (Germ 2)) ≤ J := by
      simpa using hN'
    have htop : J = ⊤ := top_unique htopLe
    exact (Germ.maximalIdeal_isMaximal 2).ne_top
      (top_unique (htop ▸ hJmaximal))
  have hradical : J.radical = Germ.maximalIdeal 2 := by
    apply le_antisymm
    · exact (Germ.maximalIdeal_isMaximal 2).isPrime.radical_le_iff.mpr
        hJmaximal
    · have hradicalPower := Ideal.radical_mono hN'
      rw [Ideal.radical_pow (I := Germ.maximalIdeal 2) hNzero,
        (Germ.maximalIdeal_isMaximal 2).isPrime.radical] at hradicalPower
      exact hradicalPower
  have hheight : J.height = (Germ.maximalIdeal 2).height := by
    rw [Ideal.height_eq_inf_minimalPrimes,
      ← Ideal.radical_minimalPrimes, hradical,
      Ideal.height_eq_inf_minimalPrimes]
  have hgNotUnit : ¬ IsUnit g := by
    intro hunit
    have htop : Germ.maximalIdeal 2 = ⊤ :=
      (Germ.maximalIdeal 2).eq_top_of_isUnit_mem hg hunit
    exact (Germ.maximalIdeal_isMaximal 2).ne_top htop
  have hprincipal : J.height ≤ 1 := by
    simpa only [J] using Ideal.height_span_singleton_le_one hgNotUnit
  have hprincipalCast :
      (J.height : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hprincipal
  rw [hheight, Germ.maximalIdeal_eq_isLocalRing,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    Germ.ringKrullDim_two] at hprincipalCast
  norm_num at hprincipalCast

/-- If a pair generates an ideal containing a power of the maximal ideal,
the second member does not belong to the principal ideal generated by the
first. -/
theorem not_mem_span_singleton_of_pair_finite_colength
    (g u : Germ 2) (hg : g ∈ Germ.maximalIdeal 2)
    (hfinite : ∃ N : ℕ,
      Germ.maximalIdeal 2 ^ N ≤ Ideal.span {g, u}) :
    u ∉ Ideal.span {g} := by
  intro hu
  apply Germ.not_maximalIdeal_pow_le_span_singleton g hg
  obtain ⟨N, hN⟩ := hfinite
  refine ⟨N, ?_⟩
  have hequality : Ideal.span ({g, u} : Set (Germ 2)) = Ideal.span {g} := by
    exact Ideal.span_pair_eq_span_left_iff_dvd.mpr
      (Ideal.mem_span_singleton.mp hu)
  simpa only [hequality] using hN

end Germ

end OnLeConjecture.Analytic
