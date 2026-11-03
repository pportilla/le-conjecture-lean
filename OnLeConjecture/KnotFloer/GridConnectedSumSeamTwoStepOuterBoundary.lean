/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamTwoStepRecovery

/-!
# The last-column boundary of the two-step first-factor correction

The high point in a column beyond the old second southwest column is
preserved by both inner transitions. Its row must lie in one of the two
outer rectangles, contradicting emptiness. This proves the last-column
boundary from the same retained second state and actual path data.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

theorem seamTwoStep_complete_outer_last (p q : SeamRetainedIndex n m)
    (x y z : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner x.val).val)
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (t : GridRectangleBetween y.val.val (seamComplementPartner z.val).val)
    (f : GridRectangleBetween z.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns y.val.val).card = 2) (hpq : p.2 = q.2) :
    (seamComplementSecond x.val).val = n + m := by
  have ho := seamTwoStep_complete_outer_right p q x y z e r t f he hr ht hf hmid hpq
  have hA := seamTwoStep_complete_outer_right_eq p q x y z e r t f he hr ht hf hmid hpq
  have hsame := seamTwoStep_complete_inner_left_eq p q x y z e r t f he hr ht hf hmid hpq
  have hcut := seamTwoStep_complete_inner_cut p q x y z e r t f he hr ht hf hmid hpq
  have hx := seamMatchingEntry_southwest_card p x e
  have hb : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns x.val.val).card + 1 := by
    rw [hmid, seamMatchingEntry_northeast_card p x e]
  have hd : (seamNortheastColumns y.val.val).card =
      (seamNortheastColumns z.val.val).card + 1 := by
    rw [hmid, seamMatchingExit_northeast_card q z f]
  have hor := seamTwoStep_birth_death_nonwrap x y z r t hr ht hb hd hx
  obtain ⟨_, _, _, hPz, hQz, _, _⟩ :=
    seamTwoStep_birth_death_columns x y z r t hr ht hb hd hx
  have hrows := seamTwoStep_birth_death_final_rows x y z r t hr ht hb hd hx
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hPQ := seamComplementFirst_lt_second x.val
  have hE := seamMatchingEntry_left_eq_second_of_right_lt p x e he ho.1
  have hF := seamMatchingExit_left_eq_second_of_right_lt q z f hf ho.2
  rw [hQz] at hF
  have hhigh : n < (x.val.val e.right).val := by
    have hh : e.right ∈ seamNortheastColumns x.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p x e, if_neg (by rw [hE]; omega)]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  have hrlow : (x.val.val r.left).val ≤ n := by
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.1
    · omega
  have heA : e.right ≠ r.left := by
    intro hh
    rw [hh] at hhigh
    omega
  have heC : e.right ≠ r.right := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have heP : e.right ≠ seamComplementFirst x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have heQ : e.right ≠ seamComplementSecond x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hNErow := seamTwoStep_values_away x y z r t hr ht hb hd hx hsame
    e.right heA heC heP heQ
  have hB : e.bottom = x.val.val e.right := by
    have hh := e.map_right
    rw [hE, seamComplementPartner_firstBlock_apply x.val e.right ho.1] at hh
    rw [bottom_def, hE]
    exact hh.symm
  have hT : f.top = e.bottom := by
    rw [top_def, ← hA, hNErow, hB]
  have hEtop : e.top.val ≤ n := by
    have hh := e.map_left
    rw [hE, seamComplementPartner_apply_second] at hh
    change (seamState p.1 p.2 e.right).val ≤ n
    rw [← hh]
    exact hP.2
  have hFbottom : f.bottom.val ≤ n := by
    change (z.val.val f.left).val ≤ n
    rw [hF, ← hQz]
    exact ((mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem z.val)).2
  by_contra hn
  have hQlast : (seamComplementSecond x.val).val < n + m := by
    have hh := (seamComplementSecond x.val).isLt
    omega
  let c := Fin.last (n + m)
  have hcv : c.val = n + m := rfl
  have hcA : c ≠ r.left := by intro hh; have := congrArg Fin.val hh; omega
  have hcC : c ≠ r.right := by intro hh; have := congrArg Fin.val hh; omega
  have hcP : c ≠ seamComplementFirst x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hcQ : c ≠ seamComplementSecond x.val := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hce : c ≠ e.right := by intro hh; have := congrArg Fin.val hh; omega
  have hxc : n < (x.val.val c).val := by
    by_contra h
    have hcSW : c ∈ seamSouthwestColumns x.val.val :=
      (mem_seamSouthwestColumns _ _).mpr ⟨by omega, by omega⟩
    rw [seamComplement_southwest_eq_pair_of_card_two x.val hx] at hcSW
    rcases Finset.mem_insert.mp hcSW with hh | hh
    · exact hcP hh
    · exact hcQ (Finset.mem_singleton.mp hh)
  have hpc : seamState p.1 p.2 c = x.val.val c := by
    have hh := e.map_of_ne c (by rw [hE]; exact hcQ) hce
    change x.val.val.swapColumns (seamComplementFirst x.val)
      (seamComplementSecond x.val) c = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcP hcQ] at hh
    exact hh.symm
  have hzc := seamTwoStep_values_away x y z r t hr ht hb hd hx hsame c hcA hcC hcP hcQ
  have hcolE : c ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_neg (by rw [hE]; omega)]
    exact ⟨e.left_ne_right, Or.inl (by rw [hE]; omega)⟩
  have hcolF : c ∈ Grid.cIoo f.left f.right := by
    rw [Grid.mem_cIoo, if_neg (by rw [hF]; omega)]
    exact ⟨f.left_ne_right, Or.inl (by rw [hF]; omega)⟩
  have hvne : x.val.val c ≠ e.bottom := by
    rw [hB]
    exact fun hh => hce (x.val.val.toPerm.injective hh)
  by_cases hv : (x.val.val c).val < e.bottom.val
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf c hcolF
    rw [hzc, hT, Grid.mem_cIoo, if_pos (by rw [hB]; omega)]
    exact ⟨by simpa only [hT] using f.bottom_ne_top, by omega, hv⟩
  · have hvgt : e.bottom.val < (x.val.val c).val := by
      have hval : (x.val.val c).val ≠ e.bottom.val := fun hh => hvne (Fin.ext hh)
      omega
    apply (isEmpty_iff_forall_notMem_cIoo e).mp he c hcolE
    rw [hpc, Grid.mem_cIoo, if_neg (by rw [hB]; omega)]
    exact ⟨e.bottom_ne_top, Or.inl hvgt⟩

end OnLeConjecture.KnotFloer.GridFull
