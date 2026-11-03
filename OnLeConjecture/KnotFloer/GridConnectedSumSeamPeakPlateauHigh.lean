/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridConnectedSumSeamPeakPlateauBarrier

/-! # High-row exchanges at a three-point southwest set

These lemmas identify the order of the southwest columns after the middle
rectangle of a birth, neutral step, and death.
-/

@[expose] public noncomputable section
namespace OnLeConjecture.KnotFloer.GridFull
open TauCeti GridRectangleBetween
variable {n m : ℕ}

/-- The ordered triple determines all three selected southwest columns. -/
theorem seamPlateau_columns_of_triple (x : SeamComplement n m)
    (P Q R : Fin (n + m + 1)) (hset : seamSouthwestColumns x.val = {P, Q, R})
    (hPQ : P < Q) (hQR : Q < R) (hthree : 3 ≤ (seamSouthwestColumns x.val).card) :
    seamComplementFirst x = P ∧ seamComplementSecond x = Q ∧
      seamComplementThird x hthree = R := by
  classical
  have hPR := hPQ.trans hQR
  have hP : seamComplementFirst x = P := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hset]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨by simp, ?_⟩
    intro c hc
    rcases hc with rfl | rfl | rfl
    · exact le_rfl
    · exact hPQ.le
    · exact hPR.le
  have hQ : seamComplementSecond x = Q := by
    apply (Finset.min'_eq_iff _ _ _).mpr
    rw [hset, hP]
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨by simp [hPQ.ne.symm], ?_⟩
    rintro c ⟨hcP, hc⟩
    rcases hc with rfl | rfl | rfl
    · exact False.elim (hcP rfl)
    · exact le_rfl
    · exact hQR.le
  refine ⟨hP, hQ, ?_⟩
  apply (Finset.min'_eq_iff _ _ _).mpr
  rw [hset, hP, hQ]
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨by simp [hQR.ne.symm, hPR.ne.symm], ?_⟩
  rintro c ⟨hcQ, hcP, hc⟩
  rcases hc with rfl | rfl | rfl
  · exact False.elim (hcP rfl)
  · exact False.elim (hcQ rfl)
  · exact le_rfl

/-- A high second-block exchange replaces precisely its southwest endpoint. -/
theorem seamPlateau_high_southwest_eq {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (S D : Fin (n + m + 1)) (hS : S ∈ seamSouthwestColumns x.val.val)
    (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = S ∧ r.right = D) ∨ (r.right = S ∧ r.left = D)) :
    seamSouthwestColumns y.val.val = insert D ((seamSouthwestColumns x.val.val).erase S) := by
  classical
  obtain ⟨hSn, hSv⟩ := (mem_seamSouthwestColumns _ _).mp hS
  have hSD : S ≠ D := by intro h; rw [← h] at hDv; omega
  have hstate : (seamComplementPartner y.val).val = x.val.val.swapColumns S D := by
    rw [r.target_eq_swapColumns]
    rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
    · rw [hl, hr, GridState.swapColumns_comm]
  rw [← seamComplementPartner_southwestColumns, hstate]
  ext c
  by_cases hcS : c = S
  · subst c
    simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply, Equiv.swap_apply_left,
      Finset.mem_insert, Finset.mem_erase, hSD, ne_eq, not_true_eq_false, false_and,
      or_self, iff_false, not_and_or]
    omega
  by_cases hcD : c = D
  · subst c
    simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply, Equiv.swap_apply_right,
      Finset.mem_insert, true_or, iff_true]
    exact ⟨hDn, hSv⟩
  simp only [mem_seamSouthwestColumns, GridState.swapColumns_apply,
    Equiv.swap_apply_of_ne_of_ne hcS hcD, Finset.mem_insert, Finset.mem_erase,
    hcD, hcS, ne_eq, not_false_eq_true, true_and, false_or]

private theorem plateau_high_map {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (S D : Fin (n + m + 1))
    (hsides : (r.left = S ∧ r.right = D) ∨ (r.right = S ∧ r.left = D)) :
    (seamComplementPartner y.val).val D = x.val.val S ∧
      ∀ c, c ≠ S → c ≠ D → (seamComplementPartner y.val).val c = x.val.val c := by
  constructor
  · rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [← hr, r.map_right, hl]
    · rw [← hl, r.map_left, hr]
  · intro c hcS hcD
    apply r.map_of_ne <;> rcases hsides with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rwa [hl]
    · rwa [hl]
    · rwa [hr]
    · rwa [hr]

private theorem plateau_high_triple {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (S U V D : Fin (n + m + 1)) (hset : seamSouthwestColumns x.val.val = {S, U, V})
    (hSU : S ≠ U) (hSV : S ≠ V)
    (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = S ∧ r.right = D) ∨ (r.right = S ∧ r.left = D)) :
    seamSouthwestColumns y.val.val = {D, U, V} := by
  have hS : S ∈ seamSouthwestColumns x.val.val := by rw [hset]; simp
  rw [seamPlateau_high_southwest_eq r S D hS hDn hDv hsides, hset]
  simp [hSU, hSV]

/-- An exchange of the first southwest point with a high point moves the new
column beyond the old second point. Its position relative to the third point
specifies the new ordered triple. -/
theorem seamPlateau_high_first {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 3)
    (hy : (seamSouthwestColumns y.val.val).card = 3)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = seamComplementFirst x.val ∧ r.right = D) ∨
      (r.right = seamComplementFirst x.val ∧ r.left = D)) :
    r.left = D ∧ r.right = seamComplementFirst x.val ∧ seamComplementSecond x.val < D ∧
      ((D < seamComplementThird x.val (by omega) ∧
        seamComplementFirst y.val = seamComplementSecond x.val ∧
        seamComplementSecond y.val = D ∧
        seamComplementThird y.val (by omega) = seamComplementThird x.val (by omega)) ∨
      (seamComplementThird x.val (by omega) < D ∧
        seamComplementFirst y.val = seamComplementSecond x.val ∧
        seamComplementSecond y.val = seamComplementThird x.val (by omega) ∧
        seamComplementThird y.val (by omega) = D ∧
        (x.val.val (seamComplementThird x.val (by omega))).val <
          (x.val.val (seamComplementSecond x.val)).val)) := by
  classical
  let P := seamComplementFirst x.val
  let Q := seamComplementSecond x.val
  let R := seamComplementThird x.val (by omega)
  have hPQ : P < Q := seamComplementFirst_lt_second x.val
  have hQR : Q < R := seamComplementSecond_lt_third x.val (by omega)
  have hPR := hPQ.trans hQR
  have hp := (mem_seamSouthwestColumns _ _).mp (seamComplementFirst_mem x.val)
  have hq := (mem_seamSouthwestColumns _ _).mp (seamComplementSecond_mem x.val)
  have hr := (mem_seamSouthwestColumns _ _).mp (seamComplementThird_mem x.val (by omega))
  change n ≤ P.val ∧ (x.val.val P).val ≤ n at hp
  change n ≤ Q.val ∧ (x.val.val Q).val ≤ n at hq
  change n ≤ R.val ∧ (x.val.val R).val ≤ n at hr
  change ((r.left = P ∧ r.right = D) ∨ (r.right = P ∧ r.left = D)) at hsides
  have hDP : D ≠ P := by intro h; rw [h] at hDv; omega
  have hDQ : D ≠ Q := by intro h; rw [h] at hDv; omega
  have hDR : D ≠ R := by intro h; rw [h] at hDv; omega
  have hset := plateau_high_triple r P Q R D
    (seamComplement_southwest_eq_triple_of_card_three x.val hx) hPQ.ne hPR.ne hDn hDv hsides
  obtain ⟨hmapD, hmap⟩ := plateau_high_map r P D hsides
  have hmapQ := hmap Q hPQ.ne.symm hDQ.symm
  have hmapR := hmap R hPR.ne.symm hDR.symm
  have hsource : (x.val.val P).val < (x.val.val Q).val := x.property
  have hQD : Q < D := by
    by_contra hn
    have hDQ' : D < Q := lt_of_le_of_ne (le_of_not_gt hn) hDQ
    obtain ⟨hP, hQ, _⟩ := seamPlateau_columns_of_triple y.val D Q R hset hDQ' hQR (by omega)
    have hh := seamMatchingTarget_first_gt_second y
    rw [hP, hQ, hmapD, hmapQ] at hh
    omega
  have hor : r.left = D ∧ r.right = P := by
    rcases hsides with ⟨hL, hR⟩ | ⟨hR, hL⟩
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he Q
      · rw [Grid.mem_cIoo, hL, hR, if_pos (show P.val < D.val from hPQ.trans hQD)]
        exact ⟨hDP.symm, hPQ, hQD⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hL, hR, if_pos (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, hsource, by omega⟩
    · exact ⟨hL, hR⟩
  refine ⟨hor.1, hor.2, hQD, ?_⟩
  rcases lt_or_gt_of_ne hDR with hDR | hRD
  · have hset' : seamSouthwestColumns y.val.val = {Q, D, R} := by
      rw [hset, Finset.insert_comm]
    obtain ⟨hP, hQ, hR⟩ := seamPlateau_columns_of_triple y.val Q D R hset' hQD hDR (by omega)
    exact Or.inl ⟨hDR, hP, hQ, hR⟩
  · have hset' : seamSouthwestColumns y.val.val = {Q, R, D} := by
      rw [hset]
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨hP, hQ, hR⟩ := seamPlateau_columns_of_triple y.val Q R D hset' hQR hRD (by omega)
    have hh := seamMatchingTarget_first_gt_second y
    rw [hP, hQ, hmapQ, hmapR] at hh
    exact Or.inr ⟨hRD, hP, hQ, hR, hh⟩

/-- Removing a later southwest column places the inserted high point before
both retained columns when the first row is below both other rows. -/
theorem seamPlateau_high_later {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hy : (seamSouthwestColumns y.val.val).card = 3)
    (P S T D : Fin (n + m + 1)) (hset : seamSouthwestColumns x.val.val = {S, P, T})
    (hPS : P < S) (hPT : P < T) (hST : S ≠ T)
    (hrowS : (x.val.val P).val < (x.val.val S).val)
    (hrowT : (x.val.val P).val < (x.val.val T).val)
    (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = S ∧ r.right = D) ∨ (r.right = S ∧ r.left = D)) :
    r.left = S ∧ r.right = D ∧ D < P ∧
      seamComplementFirst y.val = D ∧ seamComplementSecond y.val = P ∧
      seamComplementThird y.val (by omega) = T := by
  classical
  have hp : n ≤ P.val ∧ (x.val.val P).val ≤ n :=
    (mem_seamSouthwestColumns _ _).mp (by rw [hset]; simp)
  have hs : n ≤ S.val ∧ (x.val.val S).val ≤ n :=
    (mem_seamSouthwestColumns _ _).mp (by rw [hset]; simp)
  have ht : n ≤ T.val ∧ (x.val.val T).val ≤ n :=
    (mem_seamSouthwestColumns _ _).mp (by rw [hset]; simp)
  have hDP : D ≠ P := by intro h; rw [h] at hDv; omega
  have hDS : D ≠ S := by intro h; rw [h] at hDv; omega
  have hDT : D ≠ T := by intro h; rw [h] at hDv; omega
  have hsetY := plateau_high_triple r S P T D hset hPS.ne.symm hST hDn hDv hsides
  obtain ⟨hmapD, hmap⟩ := plateau_high_map r S D hsides
  have hmapP := hmap P hPS.ne hDP.symm
  have hmapT := hmap T hST.symm hDT.symm
  have hDP' : D < P := by
    by_contra hn
    have hPD : P < D := lt_of_le_of_ne (le_of_not_gt hn) hDP.symm
    rcases lt_or_gt_of_ne hDT with hDT' | hTD
    · have hset' : seamSouthwestColumns y.val.val = {P, D, T} := by
        rw [hsetY, Finset.insert_comm]
      obtain ⟨hP, hQ, _⟩ := seamPlateau_columns_of_triple y.val P D T hset' hPD hDT' (by omega)
      have hh := seamMatchingTarget_first_gt_second y
      rw [hP, hQ, hmapP, hmapD] at hh
      omega
    · have hset' : seamSouthwestColumns y.val.val = {P, T, D} := by
        rw [hsetY]
        ext c
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      obtain ⟨hP, hQ, _⟩ := seamPlateau_columns_of_triple y.val P T D hset' hPT hTD (by omega)
      have hh := seamMatchingTarget_first_gt_second y
      rw [hP, hQ, hmapP, hmapT] at hh
      omega
  obtain ⟨hP, hQ, hR⟩ := seamPlateau_columns_of_triple y.val D P T hsetY hDP' hPT (by omega)
  have hor : r.left = S ∧ r.right = D := by
    rcases hsides with hh | ⟨hR, hL⟩
    · exact hh
    · exfalso
      apply (isEmpty_iff_forall_notMem_cIoo r).mp he P
      · rw [Grid.mem_cIoo, hL, hR, if_pos (show D.val < S.val from hDP'.trans hPS)]
        exact ⟨hDS, hDP', hPS⟩
      · rw [Grid.mem_cIoo, bottom_def, top_def, hL, hR, if_neg (by omega)]
        exact ⟨by intro h; have := congrArg Fin.val h; omega, Or.inr hrowS⟩
  exact ⟨hor.1, hor.2, hDP', hP, hQ, hR⟩

/-- A high exchange at the second of three southwest columns moves it before
the first column, provided the first row is below the third row. -/
theorem seamPlateau_high_second {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 3)
    (hy : (seamSouthwestColumns y.val.val).card = 3)
    (hrow : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementThird x.val (by omega))).val)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = seamComplementSecond x.val ∧ r.right = D) ∨
      (r.right = seamComplementSecond x.val ∧ r.left = D)) :
    r.left = seamComplementSecond x.val ∧ r.right = D ∧ D < seamComplementFirst x.val ∧
      seamComplementFirst y.val = D ∧ seamComplementSecond y.val = seamComplementFirst x.val ∧
      seamComplementThird y.val (by omega) = seamComplementThird x.val (by omega) := by
  have hthree : 3 ≤ (seamSouthwestColumns x.val.val).card := by omega
  exact seamPlateau_high_later r he hy _ _ _ D
      (by rw [seamComplement_southwest_eq_triple_of_card_three x.val hx, Finset.insert_comm])
      (seamComplementFirst_lt_second x.val) (seamComplementFirst_lt_third x.val hthree)
      (seamComplementSecond_lt_third x.val hthree).ne x.property hrow hDn hDv hsides

/-- A high exchange at the third southwest column has the corresponding
insertion before the first column. -/
theorem seamPlateau_high_third {x y : SeamMatchingSource n m}
    (r : GridRectangleBetween x.val.val (seamComplementPartner y.val).val)
    (he : r.IsEmpty) (hx : (seamSouthwestColumns x.val.val).card = 3)
    (hy : (seamSouthwestColumns y.val.val).card = 3)
    (hrow : (x.val.val (seamComplementFirst x.val)).val <
      (x.val.val (seamComplementThird x.val (by omega))).val)
    (D : Fin (n + m + 1)) (hDn : n ≤ D.val) (hDv : n < (x.val.val D).val)
    (hsides : (r.left = seamComplementThird x.val (by omega) ∧ r.right = D) ∨
      (r.right = seamComplementThird x.val (by omega) ∧ r.left = D)) :
    r.left = seamComplementThird x.val (by omega) ∧ r.right = D ∧ D < seamComplementFirst x.val ∧
      seamComplementFirst y.val = D ∧ seamComplementSecond y.val = seamComplementFirst x.val ∧
      seamComplementThird y.val (by omega) = seamComplementSecond x.val := by
  have hthree : 3 ≤ (seamSouthwestColumns x.val.val).card := by omega
  exact seamPlateau_high_later r he hy _ _ _ D
      (by
        rw [seamComplement_southwest_eq_triple_of_card_three x.val hx]
        ext c
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto)
      (seamComplementFirst_lt_third x.val hthree) (seamComplementFirst_lt_second x.val)
      (seamComplementSecond_lt_third x.val hthree).ne.symm hrow x.property hDn hDv hsides

end OnLeConjecture.KnotFloer.GridFull
