/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSignedDomainDefs
import Mathlib.Tactic

/-!
# Boundary and positivity of the signed domain of a seam correction path

The signed domain of a correction path from `seamState p.1 p.2` to `seamState q.1 q.2` is a
domain between these two states (`SeamCorrectionPath.signedDomain_isFrom`). The proof telescopes
the rectangle boundaries: the matching rectangle at a source `s` is a domain from `s` to its
partner, and an internal rectangle from `s` is a domain from `s` to the partner of the next
source.

The sum of the actual rectangle domains is nonnegative
(`SeamCorrectionPath.positiveDomain_nonneg`). A matching rectangle occupies only cell columns
`n, …, N - 2` and cell rows `0, …, n - 1`, where `N = n + m + 1`
(`SeamCorrectionPath.matchingDomain_eq_zero`).
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-! ### Matching rectangles -/

/-- The matching rectangle at a source vanishes outside cell columns `n, …, N - 2` and cell rows
`0, …, n - 1`. -/
theorem seamComplementRectangle_domain_eq_zero (x : SeamComplement n m)
    (hx : SeamComplementSource x) (c r : Fin (n + m + 1))
    (h : c.val < n ∨ c.val = n + m ∨ n ≤ r.val) :
    (seamComplementRectangle x).domain c r = 0 := by
  rw [domain_apply, if_neg]
  rintro ⟨hc, hr⟩
  rw [seamComplementRectangle_left, seamComplementRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right (seamComplementFirst_lt_second x)] at hc
  rw [seamComplementRectangle_left, seamComplementRectangle_right,
    Grid.mem_cIco_iff_of_left_lt_right hx] at hr
  have hp := ((mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x)).1
  have hq := ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x)).2
  have hQ := (seamComplementSecond x).isLt
  omega

/-- The matching domain of an internal path vanishes outside cell columns `n, …, N - 2` and
cell rows `0, …, n - 1`. -/
theorem SeamInternalPath.matchingDomain_eq_zero {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) (c r : Fin (n + m + 1))
    (h : c.val < n ∨ c.val = n + m ∨ n ≤ r.val) : π.matchingDomain c r = 0 := by
  induction k generalizing x with
  | zero =>
    exact seamComplementRectangle_domain_eq_zero x.val x.property c r h
  | succ k ih =>
    obtain ⟨z, R, ρ⟩ := π
    change (seamComplementRectangle x.val).domain c r + ρ.matchingDomain c r = 0
    rw [seamComplementRectangle_domain_eq_zero x.val x.property c r h, ih ρ, add_zero]

/-! ### Boundaries -/

/-- The internal rectangle domains minus the matching domains of an internal path form a domain
from the partner of its first source to its last source. -/
theorem SeamInternalPath.signedDomain_isFrom {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) :
    (π.rectDomain - π.matchingDomain).IsFrom (seamComplementPartner x.val).val y.val.val := by
  induction k generalizing x with
  | zero =>
    obtain ⟨_, h⟩ := π
    subst h
    change ((0 : GridDomain (n + m + 1)) - (seamComplementRectangle x.val).domain).IsFrom _ _
    rw [zero_sub]
    exact (seamComplementRectangle x.val).domain_isFrom.neg
  | succ k ih =>
    obtain ⟨z, R, ρ⟩ := π
    have h := (((seamComplementRectangle x.val).domain_isFrom.neg).add
      R.val.domain_isFrom).add (ih ρ)
    change (R.val.domain + ρ.rectDomain -
      ((seamComplementRectangle x.val).domain + ρ.matchingDomain)).IsFrom _ _
    convert h using 1
    abel

/-- The signed domain of a correction path is a domain between its retained endpoint states. -/
theorem SeamCorrectionPath.signedDomain_isFrom {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) :
    π.signedDomain.IsFrom (seamState p.1 p.2) (seamState q.1 q.2) := by
  obtain ⟨x, y, E, ρ, X⟩ := π
  have h := (E.val.domain_isFrom.add ρ.signedDomain_isFrom).add X.val.domain_isFrom
  change (E.val.domain + ρ.rectDomain + X.val.domain - ρ.matchingDomain).IsFrom _ _
  convert h using 1
  abel

/-! ### Positivity -/

/-- The domain of a rectangle is nonnegative. -/
theorem _root_.TauCeti.GridRectangleBetween.domain_nonneg {k : ℕ} {u v : GridState k}
    (R : GridRectangleBetween u v) (c r : Fin k) : 0 ≤ R.domain c r := by
  rw [domain_apply]
  split_ifs <;> norm_num

/-- The internal rectangle domains of an internal path have nonnegative sum. -/
theorem SeamInternalPath.rectDomain_nonneg {k : ℕ} {x y : SeamMatchingSource n m}
    (π : SeamInternalPath k x y) (c r : Fin (n + m + 1)) : 0 ≤ π.rectDomain c r := by
  induction k generalizing x with
  | zero => exact le_refl 0
  | succ k ih =>
    obtain ⟨z, R, ρ⟩ := π
    change 0 ≤ R.val.domain c r + ρ.rectDomain c r
    exact add_nonneg (R.val.domain_nonneg c r) (ih ρ)

/-- The sum of the actual rectangle domains of a correction path is nonnegative. -/
theorem SeamCorrectionPath.positiveDomain_nonneg {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c r : Fin (n + m + 1)) : 0 ≤ π.positiveDomain c r := by
  obtain ⟨x, y, E, ρ, X⟩ := π
  change 0 ≤ E.val.domain c r + ρ.rectDomain c r + X.val.domain c r
  have h1 := E.val.domain_nonneg c r
  have h2 := ρ.rectDomain_nonneg c r
  have h3 := X.val.domain_nonneg c r
  omega

/-- Matching rectangles use only cell columns `n, …, N - 2` and cell rows `0, …, n - 1`. -/
theorem SeamCorrectionPath.matchingDomain_eq_zero {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c r : Fin (n + m + 1))
    (h : c.val < n ∨ c.val = n + m ∨ n ≤ r.val) : π.matchingDomain c r = 0 :=
  π.2.2.2.1.matchingDomain_eq_zero c r h

/-- The signed domain agrees with the nonnegative positive domain outside cell columns
`n, …, N - 2` or outside cell rows `0, …, n - 1`. -/
theorem SeamCorrectionPath.signedDomain_nonneg_of {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c r : Fin (n + m + 1))
    (h : c.val < n ∨ c.val = n + m ∨ n ≤ r.val) : 0 ≤ π.signedDomain c r := by
  change 0 ≤ π.positiveDomain c r - π.matchingDomain c r
  rw [π.matchingDomain_eq_zero c r h, sub_zero]
  exact π.positiveDomain_nonneg c r

/-- The signed domain is nonnegative on the cell rows `n, …, N - 1`. -/
theorem SeamCorrectionPath.signedDomain_nonneg_of_high {k : ℕ} {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c r : Fin (n + m + 1)) (hr : n ≤ r.val) :
    0 ≤ π.signedDomain c r :=
  π.signedDomain_nonneg_of c r (Or.inr (Or.inr hr))

end OnLeConjecture.KnotFloer.GridFull
