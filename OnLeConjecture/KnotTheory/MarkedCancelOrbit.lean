/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesMatching

/-!
# Following a strand through a signed word

The arcs of a signed word grid that belong to one strand of the closed braid are the iterates of
the matching `SignedGrid.sM`. A strand at the position `s` that leaves a letter on an integer arc
of height `2 s` reaches the next letter touching `s`, and leaves it at the position
`swapAt` of that letter (`follow_step`, one or two applications of the matching). Iterating over
a segment of letters, the orbit of the matching follows the positions given by `follow`
(`follow_segment`). This is used to slide the protected block of the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 8) from the closing arc of a conjugate `A η A⁻¹` into
the core `η`.
-/

@[expose] public section

namespace OnLeConjecture.KnotTheory.MarkedCancel

open SignedGrid

variable {m : ℕ}

/-- The position of a strand after crossing a letter. -/
def swapAt (a : Fin (m - 1) × ℤˣ) (s : ℕ) : ℕ :=
  if s = a.1.val then a.1.val + 1 else if s = a.1.val + 1 then a.1.val else s

/-- The position of a strand after crossing a list of letters, from left to right. -/
def follow (s : ℕ) (u : SignedAdjacentWord m) : ℕ := u.foldl (fun s a => swapAt a s) s

theorem follow_nil (s : ℕ) : follow s ([] : SignedAdjacentWord m) = s := rfl

theorem follow_append (s : ℕ) (u u' : SignedAdjacentWord m) :
    follow s (u ++ u') = follow (follow s u) u' := by
  simp [follow, List.foldl_append]

theorem follow_concat (s : ℕ) (u : SignedAdjacentWord m) (a : Fin (m - 1) × ℤˣ) :
    follow s (u ++ [a]) = swapAt a (follow s u) := by
  rw [follow_append]; rfl

theorem swapAt_of_not_occ {a : Fin (m - 1) × ℤˣ} {s : ℕ} (h1 : a.1.val ≠ s)
    (h2 : a.1.val + 1 ≠ s) : swapAt a s = s := by
  unfold swapAt; rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2)]

/-- **One letter.** A strand leaving the corner `p` on an integer arc at height `2 s` reaches the
next letter `h` touching `s` and leaves it, after one or two applications of the matching, on an
integer arc at the position `swapAt v[h] s`. -/
theorem follow_step (v : SignedAdjacentWord m) {p : Fin v.length × Fin 3} (hp : p.2 ≠ 0)
    {s : ℕ} (hs : v.oHeight2 p = 2 * s) {h : Fin v.length} (hph : p.1 < h)
    (hnone : ∀ k : Fin v.length, p.1 < k → k < h → ¬ Occ v s k) (hocc : Occ v s h) :
    ∃ (j : ℕ) (c : Fin 3), c ≠ 0 ∧ ((sM v) ^ j) p = (h, c) ∧
      v.oHeight2 (h, c) = 2 * swapAt v[h.val] s := by
  have hs2 : v.oHeight2 p / 2 = s := by omega
  -- the corner of `h` where the strand arrives
  have harr : ∀ c : Fin 3, v.xHeight2 (h, c) = 2 * s → sM v p = (h, c) := by
    intro c hc
    refine sM_eq_of_spec v p (h, c) hp (by rw [hc, hs]) (Or.inl ⟨hph, fun k hk hpk => ?_⟩)
    rw [hs2] at hk
    by_contra hlt
    exact hnone k hpk (lt_of_not_ge hlt) hk
  have hX : ∀ c : Fin 3, v.xHeight2 (h, c) = signedXHeight2 v[h.val] c := fun c => rfl
  have hO : ∀ c : Fin 3, v.oHeight2 (h, c) = signedOHeight2 v[h.val] c := fun c => rfl
  have hpow2 : ∀ q, ((sM v) ^ 2) q = sM v (sM v q) := fun q => by
    rw [pow_two, Equiv.Perm.mul_apply]
  have hpow1 : ∀ q, ((sM v) ^ 1) q = sM v q := fun q => by rw [pow_one]
  set r := (v[h.val].1).val with hr
  unfold Occ at hocc
  rw [← hr] at hocc
  rcases Int.units_eq_one_or v[h.val].2 with he | he
  · rcases hocc with hocc | hocc
    · -- arrival at the corner `0`, departure at the corner `2`
      have h1 := harr 0 (by rw [hX]; simp [signedXHeight2, he, ← hr, hocc])
      refine ⟨2, 2, by decide, by rw [hpow2, h1, sM_middle], ?_⟩
      rw [hO]
      simp only [signedOHeight2, he, if_true, swapAt, ← hr, hocc]
      simp; ring
    · -- arrival and departure at the corner `1`
      have h1 := harr 1 (by rw [hX]; simp [signedXHeight2, he, ← hr, ← hocc]; ring)
      refine ⟨1, 1, by decide, by rw [hpow1, h1], ?_⟩
      rw [hO]
      simp only [signedOHeight2, he, if_true, swapAt, ← hr, ← hocc]
      simp
  · have hne : v[h.val].2 ≠ 1 := by rw [he]; decide
    rcases hocc with hocc | hocc
    · -- arrival and departure at the corner `1`
      have h1 := harr 1 (by rw [hX]; simp [signedXHeight2, hne, ← hr, hocc])
      refine ⟨1, 1, by decide, by rw [hpow1, h1], ?_⟩
      rw [hO]
      simp only [signedOHeight2, hne, if_false, swapAt, ← hr, hocc]
      simp; ring
    · -- arrival at the corner `0`, departure at the corner `2`
      have h1 := harr 0 (by rw [hX]; simp [signedXHeight2, hne, ← hr, ← hocc]; ring)
      refine ⟨2, 2, by decide, by rw [hpow2, h1, sM_middle], ?_⟩
      rw [hO]
      simp only [signedOHeight2, hne, if_false, swapAt, ← hr, ← hocc]
      simp

/-- **A segment of letters.** The orbit of the matching follows a strand across the letters
`h₀, …, h₀ + d - 1`. -/
theorem follow_segment (v : SignedAdjacentWord m) {p : Fin v.length × Fin 3} (hp : p.2 ≠ 0)
    {s : ℕ} (hs : v.oHeight2 p = 2 * s) {h₀ : ℕ} (hph : p.1.val < h₀)
    (hnone : ∀ k : Fin v.length, p.1 < k → k.val < h₀ → ¬ Occ v s k) :
    ∀ d, h₀ + d ≤ v.length → ∃ (j : ℕ) (p' : Fin v.length × Fin 3), p'.2 ≠ 0 ∧
      ((sM v) ^ j) p = p' ∧ v.oHeight2 p' = 2 * follow s ((v.drop h₀).take d) ∧
      p'.1.val < h₀ + d ∧
      ∀ k : Fin v.length, p'.1 < k → k.val < h₀ + d →
        ¬ Occ v (follow s ((v.drop h₀).take d)) k := by
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨0, p, hp, by rw [pow_zero]; rfl, by simpa [follow] using hs, by simpa using hph,
      fun k hk1 hk2 => by simpa [follow] using hnone k hk1 (by simpa using hk2)⟩
  | succ d ih =>
    intro hd
    obtain ⟨j, p', hp', hj, hs', hp'1, hnone'⟩ := ih (by omega)
    have hlt : h₀ + d < v.length := by omega
    set h : Fin v.length := ⟨h₀ + d, hlt⟩ with hh
    have htake : (v.drop h₀).take (d + 1) = (v.drop h₀).take d ++ [v[h₀ + d]] := by
      rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem hlt]
      rfl
    rw [htake, follow_concat]
    set s' := follow s ((v.drop h₀).take d) with hs'def
    by_cases hocc : Occ v s' h
    · obtain ⟨j', c, hc, hj', hO⟩ := follow_step v hp' hs' (h := h) (by
        rw [Fin.lt_def]; exact hp'1) (fun k hk1 hk2 => hnone' k hk1 hk2) hocc
      refine ⟨j' + j, (h, c), hc, ?_, hO, by simp [hh], fun k hk1 hk2 => ?_⟩
      · rw [pow_add, Equiv.Perm.mul_apply, hj, hj']
      · exfalso; rw [Fin.lt_def] at hk1; simp only [hh] at hk1; omega
    · have hsw : swapAt v[h₀ + d] s' = s' := by
        unfold Occ at hocc
        exact swapAt_of_not_occ (fun e => hocc (Or.inl e)) (fun e => hocc (Or.inr e))
      rw [hsw]
      refine ⟨j, p', hp', hj, hs', by omega, fun k hk1 hk2 => ?_⟩
      by_cases hk : k.val < h₀ + d
      · exact hnone' k hk1 hk
      · have : k = h := Fin.ext (by simp only [hh]; omega)
        rw [this]; exact hocc

/-- **The strand reaches the core.** Let `v = A ++ η ++ u`, and let a strand leave the corner
`p` of `A`, before the letter `h₀`, at the position `s`. If the position `k'` of the strand after
`A` is touched by `η`, the orbit of `p` reaches the corner of the first letter of `η` touching
`k'` where the strand arrives at height `2 k'`. -/
theorem reach_core (A η u : SignedAdjacentWord m) {p : Fin (A ++ η ++ u).length × Fin 3}
    (hp : p.2 ≠ 0) {s : ℕ} (hs : (A ++ η ++ u).oHeight2 p = 2 * s) {h₀ : ℕ}
    (hph : p.1.val < h₀) (hh₀ : h₀ ≤ A.length)
    (hnone : ∀ k : Fin (A ++ η ++ u).length, p.1 < k → k.val < h₀ →
      ¬ Occ (A ++ η ++ u) s k)
    {i : ℕ} (hi : i < η.length)
    (hfirst : Occ η (follow s (A.drop h₀)) ⟨i, hi⟩ ∧
      ∀ i' (hi' : i' < i), ¬ Occ η (follow s (A.drop h₀)) ⟨i', by omega⟩) :
    ∃ (j : ℕ) (q : Fin (A ++ η ++ u).length × Fin 3), ((sM (A ++ η ++ u)) ^ j) p = q ∧
      q.1.val = A.length + i ∧ (A ++ η ++ u).xHeight2 q = 2 * follow s (A.drop h₀) := by
  have hlenv : (A ++ η ++ u).length = A.length + η.length + u.length := by simp; omega
  have hseg := follow_segment (A ++ η ++ u) hp hs hph hnone (A.length - h₀) (by omega)
  have hdrop : ((A ++ η ++ u).drop h₀).take (A.length - h₀) = A.drop h₀ := by
    rw [List.append_assoc, List.drop_append_of_le_length hh₀]
    rw [List.take_append_of_le_length (by simp)]
    rw [List.take_of_length_le (by simp)]
  rw [hdrop, show h₀ + (A.length - h₀) = A.length by omega] at hseg
  obtain ⟨j, p', hp', hj, hs', hp'1, hnone'⟩ := hseg
  set k' := follow s (A.drop h₀) with hk'
  have hgetη : ∀ (i' : ℕ) (hi' : i' < η.length),
      (A ++ η ++ u)[A.length + i']'(by omega) = η[i'] := fun i' hi' => by
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hi']
  have hoccv : ∀ (i' : ℕ) (hi' : i' < η.length),
      Occ (A ++ η ++ u) k' ⟨A.length + i', by omega⟩ ↔ Occ η k' ⟨i', hi'⟩ := fun i' hi' => by
    unfold Occ; simp only; rw [hgetη i' hi']
  set hη : Fin (A ++ η ++ u).length := ⟨A.length + i, by omega⟩ with hhη
  have hspec := sM_spec (A ++ η ++ u) p' hp'
  have hk2 : (A ++ η ++ u).oHeight2 p' / 2 = k' := by omega
  rw [hk2] at hspec
  rcases hspec with ⟨hlt, hmin⟩ | ⟨hle, hall⟩
  · have hle1 := hmin hη ((hoccv i hi).mpr hfirst.1) (by rw [Fin.lt_def]; simp [hhη]; omega)
    have hq2 : (sM (A ++ η ++ u) p').2 ≠ 2 := fun e => by
      have := (xHeight2_odd_iff (A ++ η ++ u) (sM (A ++ η ++ u) p')).mpr e
      rw [sM_height] at this; omega
    have hocc_q := occ_of_xHeight2 (A ++ η ++ u) hq2
    rw [sM_height, hk2] at hocc_q
    have hge : A.length ≤ (sM (A ++ η ++ u) p').1.val := by
      by_contra hlt'
      exact hnone' _ hlt (by omega) hocc_q
    have hidx : (sM (A ++ η ++ u) p').1.val = A.length + i := by
      rw [Fin.le_def] at hle1; simp only [hhη] at hle1
      by_contra hne
      have hlt2 : (sM (A ++ η ++ u) p').1.val - A.length < i := by omega
      have := hfirst.2 _ hlt2
      apply this
      have h' := (hoccv ((sM (A ++ η ++ u) p').1.val - A.length) (by omega)).mp
      apply h'
      have e : (⟨A.length + ((sM (A ++ η ++ u) p').1.val - A.length), by omega⟩ :
          Fin (A ++ η ++ u).length) =
          (sM (A ++ η ++ u) p').1 := Fin.ext (by simp; omega)
      rw [e]; exact hocc_q
    refine ⟨j + 1, sM (A ++ η ++ u) p', ?_, hidx, by rw [sM_height]; omega⟩
    rw [pow_succ', Equiv.Perm.mul_apply, hj]
  · exfalso
    have := (hall hη ((hoccv i hi).mpr hfirst.1)).2
    rw [Fin.le_def] at this; simp only [hhη] at this
    omega

end OnLeConjecture.KnotTheory.MarkedCancel
