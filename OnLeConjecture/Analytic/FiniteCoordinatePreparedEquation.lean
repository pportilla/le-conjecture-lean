/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.ImageCoefficientRootConvergence
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Prepared equations for individual source coordinates

Finiteness gives a power of each coordinate in the coordinate ideal.
Expanding its monic image-ring relation gives a monic relation for the
coordinate itself. All lower target coefficients vanish at the origin.
The resulting equation holds on actual representatives near the origin.
-/

public section

namespace OnLeConjecture.Analytic.PointedMapGerm

open Filter OnLeConjecture.Analytic.Germ Polynomial
open scoped Topology BigOperators

/-- Each source coordinate of a finite germ satisfies a positive-degree
monic relation with all lower coefficients in the image maximal ideal. -/
theorem exists_coordinate_monic_relation_in_image_maximalIdeal
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin) (j : Fin n) :
    ∃ p : Polynomial g.ImageRing, p.Monic ∧ 0 < p.natDegree ∧
      Polynomial.aeval (coordinate j) p = 0 ∧
      ∀ i < p.natDegree, p.coeff i ∈ g.imageMaximalIdeal := by
  obtain ⟨N, hNmem⟩ :=
    g.exists_pow_mem_coordinateIdeal_of_isFiniteAtOrigin_of_mem_maximalIdeal hf
      (coordinate_mem_maximalIdeal j)
  have hN : 0 < N := by
    by_contra hz
    have hzero : N = 0 := by omega
    rw [hzero, pow_zero] at hNmem
    have hbad := g.coordinateIdeal_le_maximalIdeal hNmem
    exact (maximalIdeal_isMaximal n).ne_top (Ideal.eq_top_of_isUnit_mem _ hbad isUnit_one)
  obtain ⟨p, hp, heval, hcoeff⟩ :=
    g.exists_monic_relation_with_vanishing_coefficients_of_pow_mem_coordinateIdeal hf hNmem
  have hpd : 0 < p.natDegree := by
    rw [hp.natDegree_pos]
    intro hpone
    rw [hpone, map_one] at heval
    exact one_ne_zero heval
  refine ⟨Polynomial.expand g.ImageRing N p, hp.expand hN, ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_expand]
    exact Nat.mul_pos hpd hN
  · simpa only [Polynomial.expand_aeval] using heval
  · intro i hi
    rw [Polynomial.natDegree_expand] at hi
    rw [Polynomial.coeff_expand hN]
    split_ifs
    · apply hcoeff
      exact Nat.ne_of_lt ((Nat.div_lt_iff_lt_mul hN).mpr hi)
    · exact Ideal.zero_mem _

/-- The positive-degree prepared relation for a source coordinate holds
on representatives, with target coefficients analytic and zero at the origin. -/
theorem exists_coordinate_prepared_equation_of_finite
    {n m : ℕ} (g : PointedMapGerm n m) (hf : g.IsFiniteAtOrigin)
    (G : Source n → Source m) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 = 0)
    (hg : g = ofFunction G hG hG0) (j : Fin n) :
    ∃ (d : ℕ) (_hd : 0 < d) (C : Fin d → Source m → ℂ),
      (∀ i, AnalyticAt ℂ (C i) 0) ∧ (∀ i, C i 0 = 0) ∧
      ∀ᶠ x in 𝓝 (0 : Source n),
        x j ^ d + ∑ i : Fin d, C i (G x) * x j ^ (i : ℕ) = 0 := by
  obtain ⟨p, hp, hpd, heval, hcoeff⟩ :=
    g.exists_coordinate_monic_relation_in_image_maximalIdeal hf j
  obtain ⟨C, hC, hC0, hrep, _⟩ :=
    exists_target_representatives_with_monic_root_convergence.{0} g
      (fun i : Fin p.natDegree => p.coeff i) (fun i => hcoeff i i.isLt)
  have hsum : coordinate j ^ p.natDegree +
      ∑ i : Fin p.natDegree,
        g.pullbackRingHom (Germ.ofFunction (C i) (hC i)) * coordinate j ^ (i : ℕ) = 0 := by
    have hs := congrArg (Polynomial.aeval (coordinate j)) hp.as_sum
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at hs
    rw [heval] at hs
    rw [← Fin.sum_univ_eq_sum_range] at hs
    convert hs.symm using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hc := congrArg (fun a : g.ImageRing => (a : Germ n)) (hrep i)
    change (p.coeff i : Germ n) = g.pullbackRingHom (Germ.ofFunction (C i) (hC i)) at hc
    rw [← hc]
    rfl
  have hpull (i : Fin p.natDegree) :
      (analyticGermSubring n).subtype (g.pullbackRingHom (Germ.ofFunction (C i) (hC i))) =
        ((fun x : Source n => C i (G x)) : FunctionGerm n) := by
    rw [hg]
    rfl
  have h := congrArg (analyticGermSubring n).subtype hsum
  simp only [map_add, map_pow, map_sum, map_mul, hpull, map_zero] at h
  have hfun :
      ((fun x : Source n => x j ^ p.natDegree +
        ∑ i : Fin p.natDegree, C i (G x) * x j ^ (i : ℕ)) : FunctionGerm n) = 0 := by
    have heq : (fun x : Source n => x j ^ p.natDegree +
        ∑ i : Fin p.natDegree, C i (G x) * x j ^ (i : ℕ)) =
        (fun x => x j ^ p.natDegree) +
          ∑ i : Fin p.natDegree, fun x => C i (G x) * x j ^ (i : ℕ) := by
      ext x
      simp only [Pi.add_apply, Finset.sum_apply]
    rw [heq]
    change (Filter.Germ.coeRingHom (𝓝 (0 : Source n)))
      ((fun x => x j ^ p.natDegree) +
        ∑ i : Fin p.natDegree, fun x => C i (G x) * x j ^ (i : ℕ)) = 0
    rw [map_add, map_sum]
    exact h
  exact ⟨p.natDegree, hpd, C, hC, hC0, Filter.Germ.coe_eq.mp hfun⟩

end OnLeConjecture.Analytic.PointedMapGerm
