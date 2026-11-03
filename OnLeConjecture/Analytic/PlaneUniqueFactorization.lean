/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.PlaneWeierstrassPrimes
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# Unique factorization of plane analytic germs

Every nonzero prime ideal contains a germ that is regular in one coordinate
after a linear change. Analytic Weierstrass preparation and the established
prime-divisor theorem for distinguished polynomials give a prime element
in that ideal. Kaplansky's criterion then supplies unique factorization.

The final theorem factors a nonzero germ into coordinate powers and a unit
under the algebraic hypothesis that every prime divisor is associated to a
coordinate. It does not infer that hypothesis from a restriction on the
zero set of an analytic representative.
-/

public section

namespace OnLeConjecture.Analytic

namespace Germ

/-- Every nonzero prime ideal in the plane analytic germ ring contains a
prime element. -/
theorem exists_prime_mem_of_nonzero_prime
    (I : Ideal (Germ 2)) (hIBot : I ≠ ⊥) (hIPrime : I.IsPrime) :
    ∃ q ∈ I, Prime q := by
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
    have hunitTransformed : IsUnit (e.forward.pullbackRingHom f) := by
      simpa using Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
    apply hfNotUnit
    exact (MulEquiv.isUnit_map e.pullbackRingEquiv.toMulEquiv).mp
      (by simpa using hunitTransformed)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let I' : Ideal (Germ 2) := Ideal.map e.pullbackRingEquiv I
  let g : Germ 2 := e.pullbackRingEquiv f
  have hgRegular : Germ.IsRegularInFirstCoordinateOfOrder g (d + 1) := by
    simpa [g, PointedEquivGerm.pullbackRingEquiv_apply] using hregular
  have hgI : g ∈ I' := Ideal.mem_map_of_mem e.pullbackRingEquiv hfI
  let _ : I.IsPrime := hIPrime
  have hIPrime' : I'.IsPrime := by
    dsimp only [I']
    infer_instance
  obtain ⟨P, u, hPMonic, hPDegree, hPCoeff, hu, hfactor⟩ :=
    Germ.hasAnalyticWeierstrassFactorizationOfOrder_succ hgRegular
  let W : Germ 2 := Germ.firstCoordinatePolynomialEvaluation P
  have hWI : W ∈ I' := by
    have hproduct : g * (↑(hu.unit⁻¹) : Germ 2) ∈ I' := by
      simpa [mul_comm] using I'.mul_mem_left (↑(hu.unit⁻¹) : Germ 2) hgI
    have hproductEq : g * (↑(hu.unit⁻¹) : Germ 2) = W := by
      calc
        g * (↑(hu.unit⁻¹) : Germ 2) =
            (W * u) * (↑(hu.unit⁻¹) : Germ 2) := by rw [hfactor]
        _ = W * ((↑hu.unit : Germ 2) * (↑(hu.unit⁻¹) : Germ 2)) := by
          rw [hu.unit_spec, mul_assoc]
        _ = W := by simp
    rw [hproductEq] at hproduct
    exact hproduct
  obtain ⟨q, hqI, hqPrime⟩ :=
    Germ.exists_prime_mem_of_distinguishedWeierstrass_mem_prime
      d P hPMonic hPDegree hPCoeff I' hIPrime' hWI
  refine ⟨e.pullbackRingEquiv.symm q, ?_, ?_⟩
  · exact Ideal.symm_apply_mem_of_equiv_iff.mpr hqI
  · exact (MulEquiv.prime_iff e.pullbackRingEquiv.symm.toMulEquiv).mpr hqPrime

/-- The plane analytic germ ring is a unique factorization domain. -/
noncomputable instance instUniqueFactorizationMonoidTwo :
    UniqueFactorizationMonoid (Germ 2) :=
  UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr
    Germ.exists_prime_mem_of_nonzero_prime

end Germ

/-- If every prime divisor of a nonzero element is associated to one of
two specified elements, the element is a product of their powers and a
unit. This is an algebraic statement about prime divisors. -/
theorem exists_eq_pow_mul_pow_mul_unit_of_prime_divisors
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (x y f : R) (hf : f ≠ 0)
    (hsupport : ∀ p : R, Prime p → p ∣ f → Associated p x ∨ Associated p y) :
    ∃ a b : ℕ, ∃ u : Rˣ, f = x ^ a * y ^ b * ↑u := by
  revert hf hsupport
  refine UniqueFactorizationMonoid.induction_on_prime f ?_ ?_ ?_
  · intro hzero _hsupport
    exact (hzero rfl).elim
  · intro a ha _haZero _hsupport
    refine ⟨0, 0, ha.unit, ?_⟩
    simp
  · intro a p ha hp ih _hproductZero hsupport
    have hsupportA : ∀ q : R, Prime q → q ∣ a →
        Associated q x ∨ Associated q y := by
      intro q hq hqa
      exact hsupport q hq (dvd_mul_of_dvd_right hqa p)
    obtain ⟨i, j, u, hu⟩ := ih ha hsupportA
    rcases hsupport p hp (dvd_mul_right p a) with hx | hy
    · obtain ⟨v, hv⟩ := hx.symm
      refine ⟨i + 1, j, v * u, ?_⟩
      rw [← hv, hu]
      simp only [pow_succ, Units.val_mul]
      ring
    · obtain ⟨v, hv⟩ := hy.symm
      refine ⟨i, j + 1, v * u, ?_⟩
      rw [← hv, hu]
      simp only [pow_succ, Units.val_mul]
      ring

namespace Germ

/-- A germ whose prime divisors are associated to the two coordinate germs
is a product of coordinate powers and an analytic unit. A zero-set support
condition alone is not a hypothesis of this theorem. -/
theorem exists_coordinate_factorization_of_prime_divisors
    (f : Germ 2) (hf : f ≠ 0)
    (hsupport : ∀ p : Germ 2, Prime p → p ∣ f →
      Associated p (Germ.coordinate (0 : Fin 2)) ∨
        Associated p (Germ.coordinate (1 : Fin 2))) :
    ∃ a b : ℕ, ∃ u : (Germ 2)ˣ,
      f = Germ.coordinate (0 : Fin 2) ^ a *
        Germ.coordinate (1 : Fin 2) ^ b * ↑u :=
  exists_eq_pow_mul_pow_mul_unit_of_prime_divisors
    (Germ.coordinate (0 : Fin 2)) (Germ.coordinate (1 : Fin 2)) f hf hsupport

end Germ

end OnLeConjecture.Analytic
