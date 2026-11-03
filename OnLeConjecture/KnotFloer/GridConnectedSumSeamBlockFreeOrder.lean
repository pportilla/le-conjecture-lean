/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamMatchingPaths

/-!
# Order of complementary matching steps avoiding both diagonal blocks

Such a nonmatching empty rectangle never decreases the first southwest row.
When the row stays fixed, the first southwest column decreases. Endpoint
cases at the shared column and at row zero are included.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

private theorem blockFree_ranges {x y : GridState (n + m + 1)}
    (r : GridRectangleBetween x y) (hb : SeamDiagonalBlockFree r.toGridRectangle) :
    (r.left.val < n ∧ r.left.val < r.right.val ∧ r.right.val ≤ n ∧
      n ≤ r.bottom.val ∧ (r.bottom.val < r.top.val ∨ r.top.val = 0)) ∨
    (n ≤ r.left.val ∧ (r.left.val < r.right.val ∨ r.right.val = 0) ∧
      r.bottom.val < r.top.val ∧ r.top.val ≤ n) := by
  have hf (c d : Fin (n + m + 1))
      (hc : c ∈ Grid.cIco r.left r.right) (hd : d ∈ Grid.cIco r.bottom r.top) :=
    hb c d ((GridRectangle.mem_coveredSquares _ _).mpr ⟨hc, hd⟩)
  have hl := Grid.left_mem_cIco r.left_ne_right
  have hbottom := Grid.left_mem_cIco r.bottom_ne_top
  have hbase := hf r.left r.bottom hl hbottom
  let z : Fin (n + m + 1) := 0
  let e : Fin (n + m + 1) := Fin.last (n + m)
  let s : Fin (n + m + 1) := ⟨n, by omega⟩
  have hlast : e.val = n + m := rfl
  have hzero : z.val = 0 := rfl
  have hs : s.val = n := rfl
  have hne : r.left.val ≠ r.right.val := fun h => r.left_ne_right (Fin.ext h)
  have hbt : r.bottom.val ≠ r.top.val := fun h => r.bottom_ne_top (Fin.ext h)
  rcases hbase with ⟨hlow, bhigh⟩ | ⟨hhigh, blow⟩
  · left
    have hcols : r.left.val < r.right.val := by
      by_contra h
      have hc : e ∈ Grid.cIco r.left r.right := by
        rw [Grid.mem_cIco]
        split_ifs
        omega
      have hh := hf e r.bottom hc hbottom
      omega
    have hright : r.right.val ≤ n := by
      by_contra h
      have hc : s ∈ Grid.cIco r.left r.right := by
        rw [Grid.mem_cIco]
        split_ifs
        omega
      have hh := hf s r.bottom hc hbottom
      omega
    refine ⟨hlow, hcols, hright, bhigh, ?_⟩
    by_contra h
    have hd : z ∈ Grid.cIco r.bottom r.top := by
      rw [Grid.mem_cIco]
      split_ifs <;> omega
    have hh := hf r.left z hl hd
    omega
  · right
    have hrows : r.bottom.val < r.top.val := by
      by_contra h
      have hd : e ∈ Grid.cIco r.bottom r.top := by
        rw [Grid.mem_cIco]
        split_ifs
        omega
      have hh := hf r.left e hl hd
      omega
    have htop : r.top.val ≤ n := by
      by_contra h
      have hd : s ∈ Grid.cIco r.bottom r.top := by
        rw [Grid.mem_cIco]
        split_ifs
        omega
      have hh := hf r.left s hl hd
      omega
    refine ⟨hhigh, ?_, hrows, htop⟩
    by_contra h
    have hc : z ∈ Grid.cIco r.left r.right := by
      rw [Grid.mem_cIco]
      split_ifs <;> omega
    have hh := hf z r.bottom hc hbottom
    omega

private theorem southwest_swap_rows_le (w : GridState (n + m + 1))
    (a b : Fin (n + m + 1)) (ha : (w a).val ≤ n) (hb : (w b).val ≤ n) :
    seamSouthwestColumns (n := n) (m := m) (w.swapColumns a b) =
      seamSouthwestColumns w := by
  ext c
  simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply]
  by_cases hca : c = a
  · subst c
    simp only [Equiv.swap_apply_left]
    omega
  · by_cases hcb : c = b
    · subst c
      simp only [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

private theorem first_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementFirst x = seamComplementFirst y := by
  unfold seamComplementFirst
  congr 1

private theorem second_congr (x y : SeamComplement n m)
    (h : seamSouthwestColumns x.val = seamSouthwestColumns y.val) :
    seamComplementSecond x = seamComplementSecond y := by
  unfold seamComplementSecond
  congr 1
  rw [h, first_congr x y h]

private theorem first_le (x : SeamComplement n m) (c : Fin (n + m + 1))
    (hc : n ≤ c.val) (hr : (x.val c).val ≤ n) :
    (seamComplementFirst x).val ≤ c.val :=
  Finset.min'_le _ _ ((mem_seamSouthwestColumns _ _).mpr ⟨hc, hr⟩)

private theorem second_le (x : SeamComplement n m) (c : Fin (n + m + 1))
    (hc : n ≤ c.val) (hr : (x.val c).val ≤ n)
    (hne : c.val ≠ (seamComplementFirst x).val) :
    (seamComplementSecond x).val ≤ c.val :=
  Finset.min'_le _ _ (Finset.mem_erase.mpr
    ⟨fun h => hne (congrArg Fin.val h), (mem_seamSouthwestColumns _ _).mpr ⟨hc, hr⟩⟩)

private theorem partner_first (y : SeamComplement n m) :
    (seamComplementPartner y).val (seamComplementFirst y) =
      y.val (seamComplementSecond y) := by
  simp only [seamComplementPartner, GridState.swapColumns_apply, Equiv.swap_apply_left]

private theorem partner_second (y : SeamComplement n m) :
    (seamComplementPartner y).val (seamComplementSecond y) =
      y.val (seamComplementFirst y) := by
  simp only [seamComplementPartner, GridState.swapColumns_apply, Equiv.swap_apply_right]

private theorem matching_sides_excluded {x y : SeamMatchingSource n m} (hne : x ≠ y)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) :
    ¬ ((r.left.val = (seamComplementFirst x.val).val ∧
        r.right.val = (seamComplementSecond x.val).val) ∨
      (r.right.val = (seamComplementFirst x.val).val ∧
        r.left.val = (seamComplementSecond x.val).val)) := by
  intro h
  have hs : (seamComplementPartner y.val).val = (seamComplementPartner x.val).val := by
    rw [r.target_eq_swapColumns]
    change x.val.val.swapColumns r.left r.right =
      x.val.val.swapColumns (seamComplementFirst x.val) (seamComplementSecond x.val)
    rcases h with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [Fin.ext hl, Fin.ext hr]
    · rw [Fin.ext hl, Fin.ext hr, GridState.swapColumns_comm]
  have hp : seamComplementPartner y.val = seamComplementPartner x.val := Subtype.ext hs
  exact hne (Subtype.ext (seamComplementPartner_involutive.injective hp).symm)

private theorem rectangle_maps {x y : GridState (n + m + 1)}
    (r : GridRectangleBetween x y) (c : Fin (n + m + 1)) :
    (c.val = r.left.val → (y c).val = r.top.val) ∧
    (c.val = r.right.val → (y c).val = r.bottom.val) ∧
    (c.val ≠ r.left.val → c.val ≠ r.right.val → (y c).val = (x c).val) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simpa only [Fin.ext h, GridRectangleBetween.top] using congrArg Fin.val r.map_left
  · intro h
    simpa only [Fin.ext h, GridRectangleBetween.bottom] using congrArg Fin.val r.map_right
  · intro hl hr
    exact congrArg Fin.val (r.map_of_ne c
      (fun h => hl (congrArg Fin.val h)) (fun h => hr (congrArg Fin.val h)))

private theorem rectangle_source_maps {x y : GridState (n + m + 1)}
    (r : GridRectangleBetween x y) (c : Fin (n + m + 1)) :
    (c.val = r.left.val → (x c).val = r.bottom.val) ∧
    (c.val = r.right.val → (x c).val = r.top.val) := by
  constructor
  · intro h
    rw [Fin.ext h]
    rfl
  · intro h
    rw [Fin.ext h]
    rfl

private theorem southwest_order {x y : SeamMatchingSource n m} (hne : x ≠ y)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val) (hr : r.IsEmpty)
    (hl : n ≤ r.left.val) (hcol : r.left.val < r.right.val ∨ r.right.val = 0)
    (hrow : r.bottom.val < r.top.val) (ht : r.top.val ≤ n) :
    (x.val.val (seamComplementFirst x.val)).val <
      (y.val.val (seamComplementFirst y.val)).val := by
  have hsets : seamSouthwestColumns y.val.val = seamSouthwestColumns x.val.val := by
    rw [← seamComplementPartner_southwestColumns y.val, r.target_eq_swapColumns]
    exact southwest_swap_rows_le _ _ _ (by change r.bottom.val ≤ n; omega) ht
  have hfirst := first_congr y.val x.val hsets
  have hsecond := second_congr y.val x.val hsets
  have hp := rectangle_maps r (seamComplementFirst x.val)
  have hq := rectangle_maps r (seamComplementSecond x.val)
  rw [← hfirst, partner_first] at hp
  rw [← hsecond, partner_second] at hq
  have hps := rectangle_source_maps r (seamComplementFirst x.val)
  have hqs := rectangle_source_maps r (seamComplementSecond x.val)
  have hsource : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have htarget : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rw [hfirst]
  have hpl := first_le x.val r.left hl (by change r.bottom.val ≤ n; omega)
  have hql := second_le x.val r.left hl (by change r.bottom.val ≤ n; omega)
  have hpr (hc : n ≤ r.right.val) := first_le x.val r.right hc ht
  have hqr (hc : n ≤ r.right.val) := second_le x.val r.right hc ht
  have hpg := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqg := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hpq := seamComplementFirst_lt_second x.val
  have hnot := matching_sides_excluded hne r
  have hempty := (r.isEmpty_iff_forall_notMem_cIoo.mp hr) (seamComplementSecond x.val)
  simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff] at hempty
  simp only [hfirst, hsecond] at hp hq htarget
  change (seamComplementFirst x.val).val < (seamComplementSecond x.val).val at hpq
  split_ifs at hempty <;> omega

private theorem southwest_swap_away (w : GridState (n + m + 1))
    (a b : Fin (n + m + 1)) (ha : a.val < n)
    (hb : b.val < n ∨ (n < (w a).val ∧ n < (w b).val)) :
    seamSouthwestColumns (n := n) (m := m) (w.swapColumns a b) =
      seamSouthwestColumns w := by
  ext c
  simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply]
  by_cases hca : c = a
  · subst c
    simp only [Equiv.swap_apply_left]
    omega
  · by_cases hcb : c = b
    · subst c
      simp only [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]

private theorem northeast_away_impossible {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hl : r.left.val < n)
    (haway : r.right.val < n ∨ (n < r.bottom.val ∧ n < r.top.val)) : False := by
  have hsets : seamSouthwestColumns y.val.val = seamSouthwestColumns x.val.val := by
    rw [← seamComplementPartner_southwestColumns y.val, r.target_eq_swapColumns]
    exact southwest_swap_away _ _ _ hl haway
  have hfirst := first_congr y.val x.val hsets
  have hsecond := second_congr y.val x.val hsets
  have hp := rectangle_maps r (seamComplementFirst x.val)
  have hq := rectangle_maps r (seamComplementSecond x.val)
  have hps := rectangle_source_maps r (seamComplementFirst x.val)
  have hqs := rectangle_source_maps r (seamComplementSecond x.val)
  rw [← hfirst, partner_first] at hp
  rw [← hsecond, partner_second] at hq
  simp only [hfirst, hsecond] at hp hq
  have hpg := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hqg := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hx : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementSecond x.val)).val := x.property
  have hy : (y.val.val (seamComplementFirst y.val)).val <
      (y.val.val (seamComplementSecond y.val)).val := y.property
  rw [hfirst, hsecond] at hy
  omega

private theorem northeast_order {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hl : r.left.val < n) (_hc : r.left.val < r.right.val) (hr : r.right.val ≤ n)
    (hb : n ≤ r.bottom.val) (ht : r.bottom.val < r.top.val ∨ r.top.val = 0) :
    (x.val.val (seamComplementFirst x.val)).val <
      (y.val.val (seamComplementFirst y.val)).val ∨
    ((x.val.val (seamComplementFirst x.val)).val =
        (y.val.val (seamComplementFirst y.val)).val ∧
      seamComplementFirst y.val < seamComplementFirst x.val) := by
  by_cases hright : r.right.val < n
  · exact (northeast_away_impossible r hl (Or.inl hright)).elim
  have heq : r.right.val = n := by omega
  have hpx := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hpy := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem y.val)
  have hqy := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem y.val)
  have hpqy : (seamComplementFirst y.val).val < (seamComplementSecond y.val).val :=
    seamComplementFirst_lt_second y.val
  rcases ht with htop | hzero
  · by_cases hbottom : n < r.bottom.val
    · exact (northeast_away_impossible r hl (Or.inr ⟨hbottom, by omega⟩)).elim
    have hbn : r.bottom.val = n := by omega
    have hPx := first_le (seamComplementPartner y.val) r.right (by omega)
      (by rw [r.map_right]; change r.bottom.val ≤ n; omega)
    rw [seamComplementFirst_partner] at hPx
    have hPy : (seamComplementFirst y.val).val = n := by omega
    have hxp : n < (seamComplementFirst x.val).val := by
      by_contra h
      have he : seamComplementFirst x.val = r.right := Fin.ext (by omega)
      rw [he] at hpx
      change n ≤ r.right.val ∧ r.top.val ≤ n at hpx
      omega
    have hpmap : (seamComplementPartner y.val).val (seamComplementFirst x.val) =
        x.val.val (seamComplementFirst x.val) :=
      r.map_of_ne _ (fun he => by have := congrArg Fin.val he; omega)
        (fun he => by have := congrArg Fin.val he; omega)
    have hQp := second_le (seamComplementPartner y.val) (seamComplementFirst x.val)
      (by omega) (by rw [hpmap]; exact hpx.2)
      (by rw [seamComplementFirst_partner]; omega)
    rw [seamComplementSecond_partner] at hQp
    have hqmap : (seamComplementPartner y.val).val (seamComplementSecond y.val) =
        x.val.val (seamComplementSecond y.val) :=
      r.map_of_ne _ (fun he => by have := congrArg Fin.val he; omega)
        (fun he => by have := congrArg Fin.val he; omega)
    have hpQ := first_le x.val (seamComplementSecond y.val) (by omega)
      (by rw [← hqmap, partner_second]; exact hpy.2)
    have heQ : seamComplementSecond y.val = seamComplementFirst x.val := Fin.ext (by omega)
    right
    refine ⟨?_, ?_⟩
    · rw [← hpmap, ← heQ, partner_second y.val]
    · change (seamComplementFirst y.val).val < (seamComplementFirst x.val).val
      omega
  · have hpR := first_le x.val r.right (by omega)
      (by change r.top.val ≤ n; omega)
    have hfirst : seamComplementFirst x.val = r.right := Fin.ext (by omega)
    have hxzero : (x.val.val (seamComplementFirst x.val)).val = 0 := by
      rw [hfirst]
      exact hzero
    have hynz : (y.val.val (seamComplementFirst y.val)).val ≠ 0 := by
      intro h
      have hz : (seamComplementPartner y.val).val (seamComplementSecond y.val) =
          (seamComplementPartner y.val).val r.left := by
        apply Fin.ext
        rw [partner_second, r.map_left]
        change (y.val.val (seamComplementFirst y.val)).val = r.top.val
        omega
      have he := congrArg Fin.val ((seamComplementPartner y.val).val.toPerm.injective hz)
      omega
    left
    omega

/-- Every nonmatching empty rectangle avoiding both diagonal blocks strictly orders its sources. -/
theorem seamMatchingRectangle_blockFree_order {x y : SeamMatchingSource n m} (hne : x ≠ y)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (hr : r.IsEmpty) (hb : SeamDiagonalBlockFree r.toGridRectangle) :
    (x.val.val (seamComplementFirst x.val)).val <
      (y.val.val (seamComplementFirst y.val)).val ∨
    ((x.val.val (seamComplementFirst x.val)).val =
        (y.val.val (seamComplementFirst y.val)).val ∧
      seamComplementFirst y.val < seamComplementFirst x.val) := by
  rcases blockFree_ranges r hb with ⟨hl, hc, hr, hb, ht⟩ | ⟨hl, hc, ht, hb⟩
  · exact northeast_order r hl hc hr hb ht
  · exact Or.inl (southwest_order hne r hr hl hc ht hb)

end OnLeConjecture.KnotFloer.GridFull
