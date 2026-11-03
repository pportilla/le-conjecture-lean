/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A nonzero root criterion

This file records the polynomial root argument used in the final collision
construction for the case of order two in the article *On Lê's conjecture*.
-/

public section

namespace OnLeConjecture.Polynomial

/-- A monic complex polynomial of degree `N ≥ 2` whose coefficient in degree
`N - 2` is nonzero has a nonzero root. -/
theorem exists_nonzero_root_of_monic_coeff_ne_zero
    (p : _root_.Polynomial ℂ) (N : ℕ)
    (hp : p.Monic)
    (hdegree : p.natDegree = N)
    (hN : 2 ≤ N)
    (hcoeff : p.coeff (N - 2) ≠ 0) :
    ∃ z : ℂ, z ≠ 0 ∧ p.IsRoot z := by
  by_contra h
  have hroot_zero : ∀ z : ℂ, p.IsRoot z → z = 0 := by
    intro z hz
    by_contra hz0
    exact h ⟨z, hz0, hz⟩
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hroots : p.roots = Multiset.replicate N 0 := by
    rw [← hdegree, hsplits.natDegree_eq_card_roots]
    exact Multiset.eq_replicate_card.mpr fun z hz ↦
      hroot_zero z ((p.mem_roots hp.ne_zero).mp hz)
  have hpX : p = _root_.Polynomial.X ^ N := by
    rw [hsplits.eq_prod_roots_of_monic hp, hroots]
    simp
  have hNpos : 0 < N := lt_of_lt_of_le (by decide) hN
  have hindex : N - 2 ≠ N :=
    ne_of_lt (tsub_lt_self hNpos (by decide : 0 < (2 : ℕ)))
  apply hcoeff
  rw [hpX, _root_.Polynomial.coeff_X_pow]
  simp [hindex]

/-- Under the parity relation used in the prepared order two case, the
nonzero root occurs together with its negative. -/
theorem exists_symmetric_nonzero_roots
    (p : _root_.Polynomial ℂ) (N : ℕ)
    (hp : p.Monic)
    (hdegree : p.natDegree = N)
    (hN : 2 ≤ N)
    (hcoeff : p.coeff (N - 2) ≠ 0)
    (hodd : ∀ z : ℂ, p.eval (-z) = -p.eval z) :
    ∃ z : ℂ, z ≠ 0 ∧ p.IsRoot z ∧ p.IsRoot (-z) := by
  obtain ⟨z, hz, hpz⟩ :=
    exists_nonzero_root_of_monic_coeff_ne_zero p N hp hdegree hN hcoeff
  refine ⟨z, hz, hpz, ?_⟩
  rw [_root_.Polynomial.IsRoot.def, hodd z]
  simpa [_root_.Polynomial.IsRoot.def] using congrArg Neg.neg hpz

end OnLeConjecture.Polynomial
