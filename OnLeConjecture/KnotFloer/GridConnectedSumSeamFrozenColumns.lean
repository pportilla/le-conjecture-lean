/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSignedDomainDefs
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamCompression

/-!
# Frozen columns of a seam correction path

Let `π` be a correction path from `seamState p.1 p.2` to `seamState q.1 q.2`, and let `c` be a
column that is west or carries a high row of the initial state. If the positive domain of `π`
vanishes on the four cells adjacent to the initial state point in column `c`, then every visited
matching source and the final state agree with the initial state at `c`
(`SeamCorrectionPath.fixesColumn_of_positiveDomain_eq_zero`).

The proof has three ingredients. Every rectangle domain is nonnegative, so each actual rectangle
of `π` misses the four cells. A rectangle that misses the cell to the northeast of a source point
does not have that point's column as its initial side, and a rectangle that misses the cell to the
southwest does not have it as its terminal side. A matching partner only exchanges two southwest
columns, and the column `c` is not southwest while it carries its initial value.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-! ### Rectangle domains near a state point -/

/-- A rectangle domain is nonnegative. -/
private theorem gridRectangleDomain_nonneg {k : ℕ} [NeZero k]
    {x y : GridState k} (R : GridRectangleBetween x y) (c r : Fin k) : 0 ≤ R.domain c r := by
  unfold GridRectangleBetween.domain
  split_ifs <;> norm_num

/-- The predecessor of the terminal endpoint lies in a nondegenerate half-open cyclic
interval. -/
private theorem sub_one_right_mem_cIco {k : ℕ} [NeZero k] {a b : Fin k} (hab : a ≠ b) :
    b - 1 ∈ Grid.cIco a b := by
  have key := ite_mem_cIco_sub_one a b b
  rw [if_neg (Grid.right_notMem_cIco a b), if_neg (Ne.symm hab), if_pos rfl] at key
  by_contra h
  rw [if_neg h] at key
  norm_num at key

/-- A rectangle whose domain vanishes on the cell northeast and on the cell southwest of the
source point in column `c` does not change column `c`. -/
private theorem gridRectangle_apply_eq_of_domain_eq_zero {k : ℕ} [NeZero k]
    {x y : GridState k} (R : GridRectangleBetween x y) (c : Fin k)
    (hne : R.domain c (x c) = 0) (hsw : R.domain (c - 1) (x c - 1) = 0) : y c = x c := by
  have hrow : x R.left ≠ x R.right := fun h => R.left_ne_right (x.toPerm.injective h)
  by_cases hl : c = R.left
  · subst hl
    unfold GridRectangleBetween.domain at hne
    rw [if_pos ⟨Grid.left_mem_cIco R.left_ne_right, Grid.left_mem_cIco hrow⟩] at hne
    exact absurd hne one_ne_zero
  by_cases hr : c = R.right
  · subst hr
    unfold GridRectangleBetween.domain at hsw
    rw [if_pos ⟨sub_one_right_mem_cIco R.left_ne_right,
      sub_one_right_mem_cIco hrow⟩] at hsw
    exact absurd hsw one_ne_zero
  exact R.map_of_ne c hl hr

/-! ### Matching partners -/

/-- The matching partner does not change a column that is west or carries a high row. -/
private theorem seamComplementPartner_apply_of_west_or_high (y : SeamComplement n m)
    (c : Fin (n + m + 1)) (hc : c.val < n ∨ n < (y.val c).val) :
    (seamComplementPartner y).val c = y.val c := by
  change y.val.swapColumns _ _ c = y.val c
  rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne]
  · intro he
    have h := seamComplementFirst_mem y
    rw [← he, mem_seamSouthwestColumns] at h
    omega
  · intro he
    have h := seamComplementSecond_mem y
    rw [← he, mem_seamSouthwestColumns] at h
    omega

/-- If the matching partner of `y` agrees with `w` at a column that is west or carries a high
row of `w`, then `y` agrees with `w` there. -/
private theorem apply_eq_of_seamComplementPartner_apply_eq {w : GridState (n + m + 1)}
    {c : Fin (n + m + 1)} (hc : c.val < n ∨ n < (w c).val) (y : SeamComplement n m)
    (hy : (seamComplementPartner y).val c = w c) : y.val c = w c := by
  have h := seamComplementPartner_apply_of_west_or_high (seamComplementPartner y) c
    (by rw [hy]; exact hc)
  rw [seamComplementPartner_involutive y] at h
  rw [h, hy]

/-! ### Internal paths -/

/-- The sum of the internal rectangle domains is nonnegative. -/
private theorem SeamInternalPath.rectDomain_nonneg_aux :
    {k : ℕ} → {x y : SeamMatchingSource n m} → (ι : SeamInternalPath k x y) →
      ∀ c r, 0 ≤ ι.rectDomain c r
  | 0, _, _, _, _, _ => le_refl _
  | _ + 1, _, _, ι, c, r => by
    change 0 ≤ ι.2.1.val.domain c r + ι.2.2.rectDomain c r
    exact add_nonneg (gridRectangleDomain_nonneg ι.2.1.val c r)
      (SeamInternalPath.rectDomain_nonneg_aux ι.2.2 c r)

/-- An internal path whose rectangle domains miss the cells northeast and southwest of the point
`(c, w c)` keeps column `c` at the value `w c`, provided its initial source does. -/
private theorem SeamInternalPath.apply_eq_of_rectDomain_eq_zero {w : GridState (n + m + 1)}
    {c : Fin (n + m + 1)} (hc : c.val < n ∨ n < (w c).val) :
    {k : ℕ} → {x y : SeamMatchingSource n m} → (ι : SeamInternalPath k x y) →
    x.val.val c = w c → ι.rectDomain c (w c) = 0 → ι.rectDomain (c - 1) (w c - 1) = 0 →
    (∀ s ∈ ι.sources, s.val.val c = w c) ∧ y.val.val c = w c
  | 0, x, y, ι, hx, _, _ => by
    have h : x = y := ι.property
    subst h
    refine ⟨fun s hs => ?_, hx⟩
    rw [show s = x from List.mem_singleton.mp hs]
    exact hx
  | _ + 1, x, y, ι, hx, hne, hsw => by
    change ι.2.1.val.domain c (w c) + ι.2.2.rectDomain c (w c) = 0 at hne
    change ι.2.1.val.domain (c - 1) (w c - 1) + ι.2.2.rectDomain (c - 1) (w c - 1) = 0 at hsw
    have h1 := gridRectangleDomain_nonneg ι.2.1.val c (w c)
    have h2 := ι.2.2.rectDomain_nonneg_aux c (w c)
    have h3 := gridRectangleDomain_nonneg ι.2.1.val (c - 1) (w c - 1)
    have h4 := ι.2.2.rectDomain_nonneg_aux (c - 1) (w c - 1)
    have hstep := gridRectangle_apply_eq_of_domain_eq_zero ι.2.1.val c (by rw [hx]; omega)
      (by rw [hx]; omega)
    rw [hx] at hstep
    have hz := apply_eq_of_seamComplementPartner_apply_eq hc ι.1.val hstep
    have ih := SeamInternalPath.apply_eq_of_rectDomain_eq_zero hc ι.2.2 hz (by omega) (by omega)
    refine ⟨fun s hs => ?_, ih.2⟩
    rcases List.mem_cons.mp hs with hs | hs
    · rw [hs]
      exact hx
    · exact ih.1 s hs

/-! ### Correction paths -/

variable {k : ℕ}

/-- A state point whose four adjacent cells are missed by every actual rectangle of a correction
path never moves, provided its column is west or its row is high. -/
theorem SeamCorrectionPath.fixesColumn_of_positiveDomain_eq_zero {p q : SeamRetainedIndex n m}
    (π : SeamCorrectionPath k p q) (c : Fin (n + m + 1))
    (htype : c.val < n ∨ n < (seamState p.1 p.2 c).val)
    (hzero : ∀ a ∈ ({c, c - 1} : Finset (Fin (n + m + 1))),
      ∀ b ∈ ({seamState p.1 p.2 c, seamState p.1 p.2 c - 1} : Finset (Fin (n + m + 1))),
        π.positiveDomain a b = 0) :
    π.FixesColumn c := by
  obtain ⟨x, y, ent, ι, ex⟩ := π
  have hne := hzero c (Finset.mem_insert_self _ _) _ (Finset.mem_insert_self _ _)
  have hsw := hzero (c - 1) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  change ent.val.domain c (seamState p.1 p.2 c) + ι.rectDomain c (seamState p.1 p.2 c) +
    ex.val.domain c (seamState p.1 p.2 c) = 0 at hne
  change ent.val.domain (c - 1) (seamState p.1 p.2 c - 1) +
    ι.rectDomain (c - 1) (seamState p.1 p.2 c - 1) +
    ex.val.domain (c - 1) (seamState p.1 p.2 c - 1) = 0 at hsw
  have he1 := gridRectangleDomain_nonneg ent.val c (seamState p.1 p.2 c)
  have he2 := gridRectangleDomain_nonneg ent.val (c - 1) (seamState p.1 p.2 c - 1)
  have hi1 := ι.rectDomain_nonneg_aux c (seamState p.1 p.2 c)
  have hi2 := ι.rectDomain_nonneg_aux (c - 1) (seamState p.1 p.2 c - 1)
  have hf1 := gridRectangleDomain_nonneg ex.val c (seamState p.1 p.2 c)
  have hf2 := gridRectangleDomain_nonneg ex.val (c - 1) (seamState p.1 p.2 c - 1)
  have hentry := gridRectangle_apply_eq_of_domain_eq_zero ent.val c (by omega) (by omega)
  have hx := apply_eq_of_seamComplementPartner_apply_eq htype x.val hentry
  have hint := ι.apply_eq_of_rectDomain_eq_zero htype hx (by omega) (by omega)
  have hexit := gridRectangle_apply_eq_of_domain_eq_zero ex.val c (by rw [hint.2]; omega)
    (by rw [hint.2]; omega)
  exact ⟨hint.1, hexit.trans hint.2⟩

end OnLeConjecture.KnotFloer.GridFull
