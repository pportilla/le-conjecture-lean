/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamBirthDeath
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamSecondFactorLift
public import OnLeConjecture.KnotFloer.GridConnectedSumSeamUnweightedPaths

/-!
# The entry orientation of a two-step first-factor correction

The retained second state is fixed throughout this statement. Equality of
its high right-block values forces the outer rectangles to have opposite
row interiors. Their emptiness excludes the inserted southwest column.
No assertion about arbitrary path lengths is used.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- A high row in the right block depends only on the retained second state. -/
theorem seamRetained_same_second_high (p q : SeamRetainedIndex n m)
    (hpq : p.2 = q.2) (c : Fin (n + m + 1)) (hc : n ≤ c.val)
    (hr : n < (seamState p.1 p.2 c).val) :
    seamState p.1 p.2 c = seamState q.1 q.2 c := by
  rcases p with ⟨x, z⟩
  rcases q with ⟨y, w⟩
  change z = w at hpq
  subst w
  rcases seamColumn_cases_strict c with ⟨a, rfl⟩ | ⟨d, rfl⟩
  · have ha := a.isLt
    change n ≤ a.val at hc
    omega
  · have hz : z d ≠ 0 := by
      intro hz
      rw [seamState_right_of_zero x z d hz, seamLeft_val] at hr
      have hh := (x (Fin.last n)).isLt
      omega
    rw [seamState_right_of_ne_zero x z d hz, seamState_right_of_ne_zero y z d hz]

/-- A complete two-step correction with the same second state cannot enter
through the nonwrapping first-block column interval. -/
theorem seamTwoStep_entry_not_left (p q : SeamRetainedIndex n m) (hpq : p.2 = q.2)
    (a b c : SeamMatchingSource n m)
    (e : GridRectangleBetween (seamState p.1 p.2) (seamComplementPartner a.val).val)
    (r : GridRectangleBetween a.val.val (seamComplementPartner b.val).val)
    (t : GridRectangleBetween b.val.val (seamComplementPartner c.val).val)
    (f : GridRectangleBetween c.val.val (seamState q.1 q.2))
    (he : e.IsEmpty) (hr : r.IsEmpty) (ht : t.IsEmpty) (hf : f.IsEmpty)
    (hmid : (seamNortheastColumns b.val.val).card = 2) : ¬ e.left.val < n := by
  intro hE
  have hNEa := seamMatchingEntry_northeast_card p a e
  have hNEc := seamMatchingExit_northeast_card q c f
  have hSWa := seamMatchingEntry_southwest_card p a e
  have hb : (seamNortheastColumns b.val.val).card =
      (seamNortheastColumns a.val.val).card + 1 := by omega
  have hd : (seamNortheastColumns b.val.val).card =
      (seamNortheastColumns c.val.val).card + 1 := by omega
  have hor := seamTwoStep_birth_death_nonwrap a b c r t hr ht hb hd hSWa
  obtain ⟨_, _, _, hPc, hQc, _, _⟩ :=
    seamTwoStep_birth_death_columns a b c r t hr ht hb hd hSWa
  have hrows := seamTwoStep_birth_death_final_rows a b c r t hr ht hb hd hSWa
  have hB := seamMatchingBirth_nonwrap a b r hr hb hor.1
  have hCcut := hB.1
  have hCP := hB.2.1
  have hP := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem a.val)
  have hQ := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem a.val)
  have hPQ := seamComplementFirst_lt_second a.val
  have hPe := seamMatchingEntry_right_eq_first_of_left_lt p a e he hE
  have hAhigh : n < (a.val.val e.left).val := by
    have hh : e.left ∈ seamNortheastColumns a.val.val := by
      rw [seamMatchingEntry_northeast_eq_singleton p a e, if_pos hE]
      exact Finset.mem_singleton_self _
    exact ((mem_seamNortheastColumns _ _).mp hh).2
  have hpP : seamState p.1 p.2 (seamComplementFirst a.val) = a.val.val e.left := by
    have hh := e.map_left
    rw [hPe, seamComplementPartner_firstBlock_apply a.val e.left hE] at hh
    exact hh.symm
  have hpPhigh : n < (seamState p.1 p.2 (seamComplementFirst a.val)).val := by
    rwa [hpP]
  have hpqP := seamRetained_same_second_high p q hpq
    (seamComplementFirst a.val) hP.1 hpPhigh
  have hcP : c.val.val (seamComplementFirst a.val) =
      a.val.val (seamComplementSecond a.val) := by
    simpa only [hPc] using hrows.1
  have hF : f.left.val < n ∧ f.right = seamComplementFirst a.val := by
    rcases seamMatchingExit_endpoints q c f hf with hF | hF
    · exact ⟨hF.1, hF.2.1.trans hPc⟩
    · have hmap := f.map_of_ne (seamComplementFirst a.val)
        (by rw [hF.2.1, hQc]; exact seamComplementFirst_ne_second a.val)
        (fun hh => by have := congrArg Fin.val hh; omega)
      rw [hcP] at hmap
      have hh := congrArg Fin.val (hpqP.trans hmap)
      omega
  have hCneP : r.right ≠ seamComplementFirst a.val := hCP.ne
  have hCneQ : r.right ≠ seamComplementSecond a.val := (hCP.trans hPQ).ne
  have hCneA : r.right ≠ e.left := by
    intro hh
    have := congrArg Fin.val hh
    omega
  have hpC : seamState p.1 p.2 r.right = a.val.val r.right := by
    have hh := e.map_of_ne r.right hCneA (by simpa only [hPe] using hCneP)
    change a.val.val.swapColumns (seamComplementFirst a.val)
      (seamComplementSecond a.val) r.right = _ at hh
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hCneP hCneQ] at hh
    exact hh.symm
  have hChigh : n < (seamState p.1 p.2 r.right).val := by
    rw [hpC]
    rcases seamMatchingBirth_ranges r hb with h | h
    · exact h.2.2.2
    · omega
  have hpqC := seamRetained_same_second_high p q hpq r.right hCcut hChigh
  have hCf := f.map_of_ne r.right
    (fun hh => by have := congrArg Fin.val hh; omega)
    (by rw [hF.2]; exact hCneP)
  have hCeq : seamState p.1 p.2 r.right = c.val.val r.right := hpqC.trans hCf
  have hbottom : e.bottom = a.val.val (seamComplementSecond a.val) := by
    have hh := e.map_right
    rw [hPe, seamComplementPartner_apply_first] at hh
    exact hh.symm
  have htop : f.top = e.bottom := by rw [top_def, hF.2, hcP, hbottom]
  have hcut : f.bottom = e.top := by
    calc
      f.bottom = seamState q.1 q.2 f.right := f.map_right.symm
      _ = seamState q.1 q.2 (seamComplementFirst a.val) := by rw [hF.2]
      _ = seamState p.1 p.2 (seamComplementFirst a.val) := hpqP.symm
      _ = e.top := by rw [top_def, hPe]
  have hCe : r.right ∈ Grid.cIoo e.left e.right := by
    rw [Grid.mem_cIoo, if_pos (by rw [hPe]; omega)]
    exact ⟨e.left_ne_right, by omega, by rwa [hPe]⟩
  have hCfcol : r.right ∈ Grid.cIoo f.left f.right := by
    rw [Grid.mem_cIoo, if_pos (by rw [hF.2]; omega)]
    exact ⟨f.left_ne_right, by omega, by rwa [hF.2]⟩
  have hneB : seamState p.1 p.2 r.right ≠ e.bottom := by
    intro hh
    rw [hbottom] at hh
    have := congrArg Fin.val hh
    omega
  have hneT : seamState p.1 p.2 r.right ≠ e.top := by
    intro hh
    apply hCneP
    exact (seamState p.1 p.2).toPerm.injective (by simpa only [top_def, hPe] using hh)
  rcases (Grid.mem_cIoo_or_mem_cIoo_swap_iff e.bottom_ne_top).mpr ⟨hneB, hneT⟩ with h | h
  · exact (isEmpty_iff_forall_notMem_cIoo e).mp he r.right hCe h
  · apply (isEmpty_iff_forall_notMem_cIoo f).mp hf r.right hCfcol
    simpa only [hcut, htop, ← hCeq] using h

end OnLeConjecture.KnotFloer.GridFull
