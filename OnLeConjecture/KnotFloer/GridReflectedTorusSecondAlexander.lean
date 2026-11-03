/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusAnchorAlexander

/-!
# Cyclic displacement and the second torus filtration bound

The Alexander grading of a state relative to the reflected torus anchor
can be computed from its column displacements. This supplies the grading
calculation needed to check a proposed second representative. It does
not construct a representative or prove the requisite cancellations.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

/-- The forward cyclic displacement from column `c` to column `b`. -/
def reflectedTorusCyclicDisplacement (n c b : ℕ) : ℕ :=
  if c ≤ b then b - c else consecutiveTorusGridSize n + b - c

/-- The integer contribution of a cyclic displacement to the scaled
Alexander drop. For `d < 2*n+3` this is the tent function with slopes
`n+1` and `-(n+2)`. -/
def reflectedTorusDisplacementWeight (n d : ℕ) : ℤ :=
  ((n : ℤ) + 1) * d - (consecutiveTorusGridSize n : ℤ) * ((d - (n + 2) : ℕ) : ℤ)

private theorem reflectedTorusColumnPotential_cyclic_difference
    (n c b : ℕ) (hc : c < consecutiveTorusGridSize n)
    (hb : b < consecutiveTorusGridSize n) :
    reflectedTorusColumnPotential n c b - reflectedTorusColumnPotential n c c =
      ((c - (n + 2) : ℕ) : ℤ) - ((b - (n + 2) : ℕ) : ℤ) +
        ((reflectedTorusCyclicDisplacement n c b - (n + 2) : ℕ) : ℤ) -
        (if c ≤ b then 0 else (n : ℤ) + 1) := by
  unfold reflectedTorusColumnPotential reflectedTorusCyclicDisplacement
    consecutiveTorusGridSize at *
  split_ifs <;> omega

/-- The column potential is a cyclic displacement weight up to a difference
of terms depending on the individual columns. Those terms cancel when
summed over a permutation. -/
theorem reflectedTorusColumnPotential_difference_eq_displacement
    (n : ℕ) (c b : Fin (consecutiveTorusGridSize n)) :
    (consecutiveTorusGridSize n : ℤ) *
        (reflectedTorusColumnPotential n c.val b.val -
          reflectedTorusColumnPotential n c.val c.val) =
      reflectedTorusDisplacementWeight n b.val -
        reflectedTorusDisplacementWeight n c.val -
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val b.val) := by
  rw [reflectedTorusColumnPotential_cyclic_difference n c.val b.val c.isLt b.isLt]
  unfold reflectedTorusDisplacementWeight
  by_cases h : c.val ≤ b.val
  · have hd : (reflectedTorusCyclicDisplacement n c.val b.val : ℤ) =
        (b.val : ℤ) - c.val := by
      simp only [reflectedTorusCyclicDisplacement, if_pos h]
      omega
    rw [if_pos h, hd]
    ring
  · have hd : (reflectedTorusCyclicDisplacement n c.val b.val : ℤ) =
        (consecutiveTorusGridSize n : ℤ) + b.val - c.val := by
      simp only [reflectedTorusCyclicDisplacement, if_neg h]
      have hc := c.isLt
      omega
    rw [if_neg h, hd]
    ring

/-- The column of the anchor whose occupied row is the row of `x` in the
given column. -/
def reflectedTorusRelativeColumns (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n)) :
    Equiv.Perm (Fin (consecutiveTorusGridSize n)) :=
  x.toPerm.trans (reflectedTorusAnchor n).toPerm.symm

@[simp]
theorem reflectedTorusAnchor_relativeColumns (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n))
    (c : Fin (consecutiveTorusGridSize n)) :
    reflectedTorusAnchor n (reflectedTorusRelativeColumns n x c) = x c := by
  exact (reflectedTorusAnchor n).toPerm.apply_symm_apply (x c)

/-- The full Alexander drop is the sum of the cyclic displacement weights.
The identity is scaled to avoid division by the grid size. -/
theorem alexanderTwo_reflectedTorus_eq_sum_displacement (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n)) :
    (consecutiveTorusGridSize n : ℤ) *
        ((reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) -
          (reflectedTorusGrid n).alexanderTwoℤ x) =
      2 * ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val) := by
  classical
  let σ := reflectedTorusRelativeColumns n x
  have hx (c : Fin (consecutiveTorusGridSize n)) :
      x c = reflectedTorusAnchor n (σ c) :=
    (reflectedTorusAnchor_relativeColumns n x c).symm
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun c _ => reflectedTorusColumnPotential_difference_eq_displacement n c (σ c))
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_sub_distrib] at hsum
  rw [Equiv.sum_comp σ (fun c => reflectedTorusDisplacementWeight n c.val)] at hsum
  have hA : (reflectedTorusGrid n).alexanderTwoℤ x -
      (reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) =
      2 * ((∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusColumnPotential n c.val (σ c).val) -
        ∑ c : Fin (consecutiveTorusGridSize n),
          reflectedTorusColumnPotential n c.val c.val) := by
    rw [GridDiagram.alexanderTwoℤ_eq_sum_southwestCount,
      GridDiagram.alexanderTwoℤ_eq_sum_southwestCount]
    simp only [hx, southwestCount_reflectedTorus_anchor_difference]
    ring
  change (consecutiveTorusGridSize n : ℤ) *
      ((reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) -
        (reflectedTorusGrid n).alexanderTwoℤ x) =
    2 * ∑ c : Fin (consecutiveTorusGridSize n),
      reflectedTorusDisplacementWeight n
        (reflectedTorusCyclicDisplacement n c.val (σ c).val)
  nlinarith [hsum]

/-- A lower bound on the displacement sum gives the corresponding absolute
Alexander bound, with the anchor normalization already discharged. -/
theorem alexander_reflectedTorus_le_of_displacement_weight (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n)) (k : ℤ)
    (hk : (consecutiveTorusGridSize n : ℤ) * k ≤
      ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val)) :
    (reflectedTorusGrid n).alexander x ≤ (n : ℚ) * ((n : ℚ) + 1) / 2 - k := by
  have h := alexanderTwo_reflectedTorus_eq_sum_displacement n x
  have hQ : (consecutiveTorusGridSize n : ℚ) *
      (((reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) : ℤ) -
        (reflectedTorusGrid n).alexanderTwoℤ x) ≥
      2 * (consecutiveTorusGridSize n : ℚ) * k := by
    exact_mod_cast (show (consecutiveTorusGridSize n : ℤ) *
      ((reflectedTorusGrid n).alexanderTwoℤ (reflectedTorusAnchor n) -
        (reflectedTorusGrid n).alexanderTwoℤ x) ≥
      2 * (consecutiveTorusGridSize n : ℤ) * k by nlinarith [hk])
  have ha := (reflectedTorusGrid n).two_mul_alexander_eq_intCast (reflectedTorusAnchor n)
  have hx := (reflectedTorusGrid n).two_mul_alexander_eq_intCast x
  have hN : (0 : ℚ) < consecutiveTorusGridSize n := by
    unfold consecutiveTorusGridSize
    positivity
  rw [alexander_reflectedTorusAnchor] at ha
  push_cast at hQ
  rw [← ha, ← hx] at hQ
  nlinarith

/-- In Laurent exponent `-3`, this displacement inequality is exactly the
Alexander-coordinate bound of the second staircase vertex. -/
theorem alexander_reflectedTorus_second_of_displacement_weight (n : ℕ)
    (x : GridState (consecutiveTorusGridSize n))
    (hk : (consecutiveTorusGridSize n : ℤ) * (2 * ((n : ℤ) + 1)) ≤
      ∑ c : Fin (consecutiveTorusGridSize n),
        reflectedTorusDisplacementWeight n
          (reflectedTorusCyclicDisplacement n c.val
            (reflectedTorusRelativeColumns n x c).val)) :
    (reflectedTorusGrid n).alexander x + 3 ≤
      ((n : ℚ) - 2) * ((n : ℚ) - 1) / 2 := by
  have h := alexander_reflectedTorus_le_of_displacement_weight n x
    (2 * ((n : ℤ) + 1)) hk
  push_cast at h
  nlinarith

end OnLeConjecture.KnotFloer.GridFull
