/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Polynomial.NonzeroRoot
public import OnLeConjecture.Polynomial.RootsOfUnity

/-!
# The polynomial data for the residual collision

This file formalizes the root selection in the final polynomial part of the
case of order two. The analytic lifting of this initial collision is a later
dependency.
-/

public section

namespace OnLeConjecture.DTwo

/-- The prepared odd polynomial and a nontrivial residual root of unity supply
the two source coordinates used in the residual collision. -/
theorem exists_residual_collision_coordinates
    (a k L N : ℕ) (p : _root_.Polynomial ℂ)
    (ha : 2 ≤ a) (hak : a ∣ k) (haL : a ∣ L)
    (hp : p.Monic) (hdegree : p.natDegree = N) (hN : 2 ≤ N)
    (hcoeff : p.coeff (N - 2) ≠ 0)
    (hodd : ∀ z : ℂ, p.eval (-z) = -p.eval z) :
    ∃ η z : ℂ,
      η ≠ 1 ∧ η ^ k = 1 ∧ η ^ L = 1 ∧
        z ≠ 0 ∧ p.IsRoot z ∧ p.IsRoot (-z) := by
  obtain ⟨η, hη, hηk, hηL⟩ :=
    OnLeConjecture.Polynomial.exists_nontrivial_root_fixed_by_multiples
      a k L ha hak haL
  obtain ⟨z, hz, hpz, hpnz⟩ :=
    OnLeConjecture.Polynomial.exists_symmetric_nonzero_roots
      p N hp hdegree hN hcoeff hodd
  exact ⟨η, z, hη, hηk, hηL, hz, hpz, hpnz⟩

end OnLeConjecture.DTwo
