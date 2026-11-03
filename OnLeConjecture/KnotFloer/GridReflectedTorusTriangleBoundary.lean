/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridReflectedTorusTransposition

/-!
# Coefficients of the triangular torus boundary

For three ordered columns, the coefficient is governed by the parity of
the three selected edges of `firstTorusTrianglePairs`. Odd parity forces
each cyclic gap to be at most `n+2`, the condition used in the Alexander
estimate for the two oriented three-cycle states.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti GridRectangleBetween

variable (n : ℕ)

/-- The number of triangular edges among three ordered columns. -/
noncomputable def firstTorusTriangleEdgeCount
    (a b c : Fin (consecutiveTorusGridSize n)) : ℕ :=
  (if (a, b) ∈ firstTorusTrianglePairs n then 1 else 0) +
  (if (a, c) ∈ firstTorusTrianglePairs n then 1 else 0) +
  (if (b, c) ∈ firstTorusTrianglePairs n then 1 else 0)

/-- Odd edge parity forces all three cyclic gaps into the required range. -/
theorem cyclic_gaps_le_of_odd_firstTorusTriangleEdgeCount
    (a b c : Fin (consecutiveTorusGridSize n))
    (hab : (a : ℕ) < b) (hbc : (b : ℕ) < c)
    (hodd : Odd (firstTorusTriangleEdgeCount n a b c)) :
    (b : ℕ) - a ≤ n + 2 ∧ (c : ℕ) - b ≤ n + 2 ∧
      consecutiveTorusGridSize n - c + a ≤ n + 2 := by
  obtain ⟨k, hk⟩ := hodd
  simp only [firstTorusTriangleEdgeCount, mem_firstTorusTrianglePairs] at hk
  have hc := c.isLt
  dsimp [consecutiveTorusGridSize] at hc ⊢
  split_ifs at hk <;> omega

/-- The corner returns after two swaps if the final state fixes the first swapped column. -/
theorem two_swaps_eq_corner_of_fixed_first
    {a b c d : Fin (consecutiveTorusGridSize n)} (hab : a ≠ b)
    (h : (((reflectedTorusAnchor n).swapColumns a b).swapColumns c d) a =
      reflectedTorusAnchor n a) :
    ((reflectedTorusAnchor n).swapColumns a b).swapColumns c d =
      reflectedTorusAnchor n := by
  have hi : Equiv.swap a b (Equiv.swap c d a) = a :=
    (reflectedTorusAnchor n).toPerm.injective (by
      simpa only [GridState.swapColumns_apply] using h)
  have hs : Equiv.swap c d a = b := by
    have hh := congrArg (Equiv.swap a b) hi
    simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using hh
  by_cases hac : a = c
  · subst c
    rw [Equiv.swap_apply_left] at hs
    subst d
    exact GridState.swapColumns_swapColumns _ _ _
  · by_cases had : a = d
    · subst d
      rw [Equiv.swap_apply_right] at hs
      subst c
      rw [GridState.swapColumns_comm b a, GridState.swapColumns_swapColumns]
    · rw [Equiv.swap_apply_of_ne_of_ne hac had] at hs
      exact (hab hs).elim

/-- One orientation of the corner three-cycle. -/
def cornerThreeCycle (a b c : Fin (consecutiveTorusGridSize n)) :
    GridState (consecutiveTorusGridSize n) :=
  ((reflectedTorusAnchor n).swapColumns a b).swapColumns a c

theorem cornerThreeCycle_apply_of_ne
    {a b c d : Fin (consecutiveTorusGridSize n)}
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) :
    cornerThreeCycle n a b c d = reflectedTorusAnchor n d := by
  simp only [cornerThreeCycle, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hda hdc, Equiv.swap_apply_of_ne_of_ne hda hdb]

theorem cornerThreeCycle_ne_anchor
    {a b c : Fin (consecutiveTorusGridSize n)} (hca : c ≠ a) (hcb : c ≠ b) :
    cornerThreeCycle n a b c ≠ reflectedTorusAnchor n := by
  intro h
  have hv := congrArg (fun x : GridState (consecutiveTorusGridSize n) => x a) h
  simp only [cornerThreeCycle, GridState.swapColumns_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hca hcb] at hv
  exact hca ((reflectedTorusAnchor n).toPerm.injective hv)

/-- An intermediate transposition cannot use a column fixed by a nontrivial final three-cycle. -/
theorem laurentCoefficient_triangle_intermediate_eq_zero_of_first_outside
    (R : Type*) [CommSemiring R]
    {a b c p q : Fin (consecutiveTorusGridSize n)}
    (hca : c ≠ a) (hcb : c ≠ b) (hpq : p ≠ q)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns p q) (cornerThreeCycle n a b c) = 0 := by
  classical
  rw [laurentCoefficient_eq]
  apply Finset.sum_eq_zero
  intro r _
  exfalso
  apply cornerThreeCycle_ne_anchor n hca hcb
  rw [r.target_eq_swapColumns]
  apply two_swaps_eq_corner_of_fixed_first n hpq
  rw [← r.target_eq_swapColumns]
  exact cornerThreeCycle_apply_of_ne n hpa hpb hpc

/-- The same exclusion applies to the second column of the intermediate swap. -/
theorem laurentCoefficient_triangle_intermediate_eq_zero_of_second_outside
    (R : Type*) [CommSemiring R]
    {a b c p q : Fin (consecutiveTorusGridSize n)}
    (hca : c ≠ a) (hcb : c ≠ b) (hpq : p ≠ q)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns p q) (cornerThreeCycle n a b c) = 0 := by
  rw [GridState.swapColumns_comm p q]
  exact laurentCoefficient_triangle_intermediate_eq_zero_of_first_outside
    n R hca hcb hpq.symm hqa hqb hqc

/-- All three factorizations of the oriented three-cycle contribute coefficient one. -/
theorem laurentCoefficient_cornerThreeCycle_edges (R : Type*) [CommSemiring R]
    {a b c : Fin (consecutiveTorusGridSize n)}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a b) (cornerThreeCycle n a b c) = 1 ∧
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns a c) (cornerThreeCycle n a b c) = 1 ∧
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns b c) (cornerThreeCycle n a b c) = 1 := by
  have h₁ := laurentCoefficient_corner_swap_three n R hab hca hcb
  have heq₁ : cornerThreeCycle n a b c =
      ((reflectedTorusAnchor n).swapColumns c a).swapColumns c b := by
    rw [cornerThreeCycle, GridState.swapColumns_swapColumns_conj]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab.symm hcb.symm]
    rw [GridState.swapColumns_comm a c]
  have heq₂ : cornerThreeCycle n a b c =
      ((reflectedTorusAnchor n).swapColumns b c).swapColumns b a := by
    rw [heq₁, GridState.swapColumns_swapColumns_conj]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca.symm hab]
    rw [GridState.swapColumns_comm c b]
  refine ⟨h₁, ?_, ?_⟩
  · rw [GridState.swapColumns_comm a c, heq₁]
    exact laurentCoefficient_corner_swap_three n R hca hcb.symm hab.symm
  · rw [heq₂]
    exact laurentCoefficient_corner_swap_three n R hcb.symm hab hca.symm

/-- The coefficient of each oriented three-cycle is the number of its selected triangle edges. -/
theorem laurentDifferential_firstTorusTriangle_threeCycle (R : Type*) [CommSemiring R]
    (a b c : Fin (consecutiveTorusGridSize n))
    (hab : (a : ℕ) < b) (hbc : (b : ℕ) < c) :
    laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R)
      (cornerThreeCycle n a b c) =
      (firstTorusTriangleEdgeCount n a b c : LaurentPolynomial R) := by
  classical
  have hab' : a ≠ b := by intro h; subst b; omega
  have hca : c ≠ a := by intro h; subst c; omega
  have hcb : c ≠ b := by intro h; subst c; omega
  let E : Finset (Fin (consecutiveTorusGridSize n) × Fin (consecutiveTorusGridSize n)) :=
    {(a, b), (a, c), (b, c)}
  let f (p : Fin (consecutiveTorusGridSize n) × Fin (consecutiveTorusGridSize n)) :=
    laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns p.1 p.2) (cornerThreeCycle n a b c)
  have hz (p) (hp : p ∈ firstTorusTrianglePairs n) (hpE : p ∉ E) : f p = 0 := by
    have hpq := firstTorusTrianglePairs_ne n hp
    by_cases h₁ : p.1 ∈ ({a, b, c} : Finset _)
    · by_cases h₂ : p.2 ∈ ({a, b, c} : Finset _)
      · have hporder : (p.1 : ℕ) < p.2 := by
          obtain ⟨hleft, hright, -⟩ := (mem_firstTorusTrianglePairs n p).mp hp
          omega
        simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
        rcases h₁ with h₁ | h₁ | h₁ <;> rcases h₂ with h₂ | h₂ | h₂
        all_goals simp only [h₁, h₂] at hporder
        all_goals first
          | omega
          | exact (hpE (by simp [E, Prod.ext_iff, h₁, h₂])).elim
      · have hn : p.2 ≠ a ∧ p.2 ≠ b ∧ p.2 ≠ c := by simpa using h₂
        exact laurentCoefficient_triangle_intermediate_eq_zero_of_second_outside
          n R hca hcb hpq hn.1 hn.2.1 hn.2.2
    · have hn : p.1 ≠ a ∧ p.1 ≠ b ∧ p.1 ≠ c := by simpa using h₁
      exact laurentCoefficient_triangle_intermediate_eq_zero_of_first_outside
        n R hca hcb hpq hn.1 hn.2.1 hn.2.2
  have hcoeff := laurentCoefficient_cornerThreeCycle_edges n R hab' hca hcb
  rw [firstTorusTriangle, map_sum, Finsupp.finsetSum_apply]
  simp only [laurentDifferential_single, laurentOnGenerator_apply]
  change ∑ p ∈ firstTorusTrianglePairs n, f p = _
  calc
    _ = ∑ p ∈ firstTorusTrianglePairs n ∩ E, f p := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro p hp hnot
      exact hz p hp (fun he => hnot (Finset.mem_inter.mpr ⟨hp, he⟩))
    _ = ∑ p ∈ E, if p ∈ firstTorusTrianglePairs n then f p else 0 := by
      have he : firstTorusTrianglePairs n ∩ E =
          E.filter (fun p => p ∈ firstTorusTrianglePairs n) := by
        ext p
        simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
      rw [he, Finset.sum_filter]
    _ = _ := by
      have habac : (a, b) ≠ (a, c) := by simp [hcb.symm]
      have habbc : (a, b) ≠ (b, c) := by simp [hab']
      have hacbc : (a, c) ≠ (b, c) := by simp [hab']
      have hnot : (a, b) ∉ ({(a, c), (b, c)} : Finset _) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨habac, habbc⟩
      dsimp only [E]
      rw [Finset.sum_insert hnot, Finset.sum_pair hacbc]
      simp only [f, hcoeff.1, hcoeff.2.1, hcoeff.2.2]
      by_cases h₁ : (a, b) ∈ firstTorusTrianglePairs n <;>
        by_cases h₂ : (a, c) ∈ firstTorusTrianglePairs n <;>
        by_cases h₃ : (b, c) ∈ firstTorusTrianglePairs n <;>
        norm_num [firstTorusTriangleEdgeCount, h₁, h₂, h₃]

/-- Reversing the three-cycle orientation leaves the triangular boundary coefficient unchanged. -/
theorem laurentDifferential_firstTorusTriangle_threeCycle_reverse
    (R : Type*) [CommSemiring R] (a b c : Fin (consecutiveTorusGridSize n))
    (hab : (a : ℕ) < b) (hbc : (b : ℕ) < c) :
    laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R)
      (cornerThreeCycle n a c b) =
      (firstTorusTriangleEdgeCount n a b c : LaurentPolynomial R) := by
  classical
  have hab' : a ≠ b := by intro h; subst b; omega
  have hca : c ≠ a := by intro h; subst c; omega
  have hcb : c ≠ b := by intro h; subst c; omega
  have hf := laurentCoefficient_cornerThreeCycle_edges n R hab' hca hcb
  have hr := laurentCoefficient_cornerThreeCycle_edges n R hca.symm hab'.symm hcb.symm
  have hrbc : laurentCoefficient (reflectedTorusGrid n) R
      ((reflectedTorusAnchor n).swapColumns b c) (cornerThreeCycle n a c b) = 1 := by
    rw [GridState.swapColumns_comm b c]
    exact hr.2.2
  rw [← laurentDifferential_firstTorusTriangle_threeCycle n R a b c hab hbc]
  simp only [firstTorusTriangle, map_sum, Finsupp.finsetSum_apply,
    laurentDifferential_single, laurentOnGenerator_apply]
  apply Finset.sum_congr rfl
  intro p hp
  have hpq := firstTorusTrianglePairs_ne n hp
  by_cases h₁ : p.1 ∈ ({a, b, c} : Finset _)
  · by_cases h₂ : p.2 ∈ ({a, b, c} : Finset _)
    · have hporder : (p.1 : ℕ) < p.2 := by
        obtain ⟨hleft, hright, -⟩ := (mem_firstTorusTrianglePairs n p).mp hp
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
      rcases h₁ with h₁ | h₁ | h₁ <;> rcases h₂ with h₂ | h₂ | h₂
      all_goals simp only [h₁, h₂] at hporder ⊢
      all_goals first | omega | rw [hf.1, hr.2.1] | rw [hf.2.1, hr.1] | rw [hf.2.2, hrbc]
    · have hn : p.2 ≠ a ∧ p.2 ≠ b ∧ p.2 ≠ c := by simpa using h₂
      rw [laurentCoefficient_triangle_intermediate_eq_zero_of_second_outside
        n R hab'.symm hcb.symm hpq hn.1 hn.2.2 hn.2.1,
        laurentCoefficient_triangle_intermediate_eq_zero_of_second_outside
          n R hca hcb hpq hn.1 hn.2.1 hn.2.2]
  · have hn : p.1 ≠ a ∧ p.1 ≠ b ∧ p.1 ≠ c := by simpa using h₁
    rw [laurentCoefficient_triangle_intermediate_eq_zero_of_first_outside
      n R hab'.symm hcb.symm hpq hn.1 hn.2.2 hn.2.1,
      laurentCoefficient_triangle_intermediate_eq_zero_of_first_outside
        n R hca hcb hpq hn.1 hn.2.1 hn.2.2]

/-- Exactly one selected edge is adjacent, so the corner coefficient of the boundary is U. -/
theorem laurentDifferential_firstTorusTriangle_anchor (R : Type*) [CommSemiring R]
    (hn : 0 < n) :
    laurentDifferential (reflectedTorusGrid n) R (firstTorusTriangle n R)
      (reflectedTorusAnchor n) = LaurentPolynomial.T 1 := by
  classical
  let p₀ : Fin (consecutiveTorusGridSize n) × Fin (consecutiveTorusGridSize n) :=
    (⟨n - 1, by dsimp [consecutiveTorusGridSize]; omega⟩,
      ⟨n, by dsimp [consecutiveTorusGridSize]; omega⟩)
  have hp₀ : p₀ ∈ firstTorusTrianglePairs n := by
    rw [mem_firstTorusTrianglePairs]
    dsimp [p₀]
    omega
  have hp₀adj : (p₀.2 : ℕ) = (p₀.1 : ℕ) + 1 := by dsimp [p₀]; omega
  have hc (p) (hp : p ∈ firstTorusTrianglePairs n) :
      laurentCoefficient (reflectedTorusGrid n) R
        ((reflectedTorusAnchor n).swapColumns p.1 p.2) (reflectedTorusAnchor n) =
        if (p.2 : ℕ) = (p.1 : ℕ) + 1 then LaurentPolynomial.T 1 else 0 := by
    obtain ⟨hl, hr, hb⟩ := (mem_firstTorusTrianglePairs n p).mp hp
    apply laurentCoefficient_corner_swap_anchor_of_lt n R (by omega)
    dsimp [consecutiveTorusGridSize]
    omega
  rw [firstTorusTriangle, map_sum, Finsupp.finsetSum_apply]
  simp only [laurentDifferential_single, laurentOnGenerator_apply]
  rw [Finset.sum_eq_single p₀]
  · rw [hc p₀ hp₀, if_pos hp₀adj]
  · intro p hp hne
    rw [hc p hp]
    apply if_neg
    intro hadj
    apply hne
    obtain ⟨hl, hr, -⟩ := (mem_firstTorusTrianglePairs n p).mp hp
    apply Prod.ext <;> apply Fin.ext <;> dsimp [p₀] <;> omega
  · exact fun h => (h hp₀).elim

/-- The explicit boundary correction cancels the anchor coefficient. -/
theorem firstTorusCycle_anchor_eq_zero (R : Type*) [CommSemiring R] [CharP R 2]
    (hn : 0 < n) : firstTorusCycle n R (reflectedTorusAnchor n) = 0 := by
  rw [firstTorusCycle, Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.smul_apply,
    laurentDifferential_firstTorusTriangle_anchor n R hn, smul_eq_mul,
    ← LaurentPolynomial.T_add]
  rw [show (-1 : ℤ) + 1 = 0 by omega, LaurentPolynomial.T_zero]
  ext k
  simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero,
    Finsupp.add_apply, Finsupp.zero_apply, CharTwo.add_self_eq_zero]

end OnLeConjecture.KnotFloer.GridFull
