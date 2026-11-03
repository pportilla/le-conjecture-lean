/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneNoetherian
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# A reduction of integral closure to Weierstrass prime divisors

Mathlib does not derive integral closure from its regular local ring class.
This file uses linear coordinate changes, analytic Weierstrass preparation,
and Kaplansky's criterion to reduce integral closure of the plane analytic
germ ring to one statement about distinguished Weierstrass polynomials.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- If every prime ideal containing a distinguished Weierstrass polynomial
contains a prime element, then the plane analytic germ ring is integrally
closed. -/
theorem isIntegrallyClosed_two_of_distinguishedWeierstrass_primes
    (hprime :
      ∀ (d : ℕ) (P : Polynomial (Germ 1)),
        P.Monic →
        P.natDegree = d + 1 →
        (∀ k, k < d + 1 →
          P.coeff k ∈ Germ.maximalIdeal 1) →
        ∀ I : Ideal (Germ 2),
          I.IsPrime →
          I ≠ ⊥ →
          Germ.firstCoordinatePolynomialEvaluation P ∈ I →
          ∃ q ∈ I, Prime q) :
    IsIntegrallyClosed (Germ 2) := by
  let hfactorization : UniqueFactorizationMonoid (Germ 2) :=
    UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr (by
      intro I hIBot hIPrime
      obtain ⟨f, hfI, hfZero⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot hIBot
      have hfNotUnit : ¬ IsUnit f := by
        intro hfUnit
        exact hIPrime.ne_top (I.eq_top_of_isUnit_mem hfI hfUnit)
      obtain ⟨e, n, hregular⟩ :=
        Germ.exists_linear_equiv_regularInFirstCoordinate hfZero
      have hn : 0 < n := by
        by_contra hn
        have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        have hunitTransformed :
            IsUnit (e.forward.pullbackRingHom f) := by
          simpa using
            Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
        apply hfNotUnit
        exact
          (MulEquiv.isUnit_map e.pullbackRingEquiv.toMulEquiv).mp (by
            simpa using hunitTransformed)
      obtain ⟨d, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      let I' : Ideal (Germ 2) := Ideal.map e.pullbackRingEquiv I
      let g : Germ 2 := e.pullbackRingEquiv f
      have hgRegular :
          Germ.IsRegularInFirstCoordinateOfOrder g (d + 1) := by
        simpa [g, PointedEquivGerm.pullbackRingEquiv_apply] using hregular
      have hgI : g ∈ I' := by
        exact Ideal.mem_map_of_mem e.pullbackRingEquiv hfI
      let _ : I.IsPrime := hIPrime
      have hIPrime' : I'.IsPrime := by
        dsimp only [I']
        infer_instance
      have hI'Bot : I' ≠ ⊥ := by
        change Ideal.map e.pullbackRingEquiv I ≠ ⊥
        intro hmap
        apply hIBot
        exact (Ideal.map_eq_bot_iff_of_injective
          e.pullbackRingEquiv.injective).mp hmap
      obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hfactor⟩ :=
        Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hgRegular
      let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
      have hWI : W ∈ I' := by
        have hproduct : g * (↑(hu.unit⁻¹) : Germ 2) ∈ I' := by
          simpa [mul_comm] using
            I'.mul_mem_left (↑(hu.unit⁻¹) : Germ 2) hgI
        have hproductEq : g * (↑(hu.unit⁻¹) : Germ 2) = W := by
          calc
            g * (↑(hu.unit⁻¹) : Germ 2) =
                (W * u) * (↑(hu.unit⁻¹) : Germ 2) := by
              rw [hfactor]
            _ = W * ((↑hu.unit : Germ 2) *
                (↑(hu.unit⁻¹) : Germ 2)) := by
              rw [hu.unit_spec, mul_assoc]
            _ = W := by simp
        rw [hproductEq] at hproduct
        exact hproduct
      obtain ⟨q, hqI, hqPrime⟩ :=
        hprime d P hPMonic hPDegree hPCoeff I' hIPrime' hI'Bot (by
          simpa only [W] using hWI)
      refine ⟨e.pullbackRingEquiv.symm q, ?_, ?_⟩
      · exact Ideal.symm_apply_mem_of_equiv_iff.mpr hqI
      · exact
          (MulEquiv.prime_iff
            e.pullbackRingEquiv.symm.toMulEquiv).mpr hqPrime)
  let _ : UniqueFactorizationMonoid (Germ 2) := hfactorization
  let _ : GCDMonoid (Germ 2) :=
    UniqueFactorizationMonoid.toGCDMonoid (Germ 2)
  exact GCDMonoid.toIsIntegrallyClosed

end Germ

end OnLeConjecture.Analytic
