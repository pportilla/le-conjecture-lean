/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.Order

/-!
# Weighted bivariate Jacobians

This file records the weighted homogeneity of the Jacobian determinant in two
variables. The result is used in the cases of order three and order two.
-/

public section

namespace OnLeConjecture.Polynomial

/-- The Jacobian determinant of two bivariate polynomials. -/
@[expose]
noncomputable def jacobian {R : Type*} [CommRing R]
    (f g : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.pderiv 0 f * MvPolynomial.pderiv 1 g -
    MvPolynomial.pderiv 1 f * MvPolynomial.pderiv 0 g

/-- The Jacobian of weighted homogeneous bivariate polynomials is weighted
homogeneous of the expected degree. -/
theorem isWeightedHomogeneous_jacobian
    {R : Type*} [CommRing R]
    (w : Fin 2 → ℕ) (f g : MvPolynomial (Fin 2) R) (m n : ℕ)
    (hf : f.IsWeightedHomogeneous w m)
    (hg : g.IsWeightedHomogeneous w n)
    (hfm0 : w 0 ≤ m) (hfm1 : w 1 ≤ m)
    (hgn0 : w 0 ≤ n) (hgn1 : w 1 ≤ n) :
    (jacobian f g).IsWeightedHomogeneous w
      ((m - w 0) + (n - w 1)) := by
  have hdf0 := hf.pderiv (Nat.sub_add_cancel hfm0)
  have hdf1 := hf.pderiv (Nat.sub_add_cancel hfm1)
  have hdg0 := hg.pderiv (Nat.sub_add_cancel hgn0)
  have hdg1 := hg.pderiv (Nat.sub_add_cancel hgn1)
  have hfirst := hdf0.mul hdg1
  have hsecond := hdf1.mul hdg0
  have hdegrees :
      (m - w 1) + (n - w 0) = (m - w 0) + (n - w 1) := by
    omega
  rw [hdegrees] at hsecond
  exact hfirst.sub hsecond

end OnLeConjecture.Polynomial
