/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotTheory.SignedWordGridMovesMatching

/-! # Rotation and far commutation of signed word grids

`SignedGrid.Fwd x y` says that every signed word grid of `x` is related by grid moves to some
signed word grid of `y`. This file proves it for the cyclic rotation `x ++ y ↦ y ++ x`
(`SignedGrid.fwd_rotate`), by a cyclic permutation of the columns, and for the far commutation
`u (i, e) (j, f) w ↦ u (j, f) (i, e) w` with `|i - j| ≥ 2` and arbitrary signs
(`SignedGrid.fwd_far`), by nine column commutations. This is the written proof of Statement E
(`statement_E_complete_proof.tex`, Section 7, *Far commutation and cyclic rotation*). All results
are unconditional.
-/

@[expose] public noncomputable section

namespace OnLeConjecture.KnotTheory.SignedGrid

open TauCeti

variable {m : ℕ}

/-- Every signed word grid of `x` is related by grid moves to a signed word grid of `y`. -/
def Fwd (x y : SignedAdjacentWord m) : Prop :=
  ∀ G : GridDiagram (x.length * 3), IsSignedWordGrid x G →
    ∃ H : GridDiagram (y.length * 3), IsSignedWordGrid y H ∧ G.MovesTo H

theorem Fwd.refl (x : SignedAdjacentWord m) : Fwd x x :=
  fun G hG => ⟨G, hG, GridDiagram.MovesTo.refl G⟩

theorem Fwd.trans {x y z : SignedAdjacentWord m} (h₁ : Fwd x y) (h₂ : Fwd y z) : Fwd x z := by
  intro G hG
  obtain ⟨H, hH, hm⟩ := h₁ G hG
  obtain ⟨K, hK, hm'⟩ := h₂ H hH
  exact ⟨K, hK, hm.trans hm'⟩

/-- Specific signed word grids of `x` and `y` related by grid moves give `Fwd` in both
directions. -/
theorem fwd_of_grids {x y : SignedAdjacentWord m} {G : GridDiagram (x.length * 3)}
    {H : GridDiagram (y.length * 3)} (hG : IsSignedWordGrid x G) (hH : IsSignedWordGrid y H)
    (hm : G.MovesTo H) : Fwd x y ∧ Fwd y x := by
  constructor
  · intro G' hG'
    exact ⟨H, hH, (signed_movesTo hG' hG).trans hm⟩
  · intro H' hH'
    exact ⟨G, hG, (signed_movesTo hH' hH).trans hm.symm⟩

/-! ### Transport along a bijection of letters -/

section Transport

variable {v v' : SignedAdjacentWord m}

/-- Transport a grid of `v` to a grid of `v'` along a bijection of letter positions. -/
def sTransport (hL : v.length = v'.length) (τ : Fin v.length ≃ Fin v'.length)
    (G : GridDiagram (v.length * 3)) : GridDiagram (v'.length * 3) :=
  let σ : Fin v.length × Fin 3 ≃ Fin v'.length × Fin 3 := τ.prodCongr (Equiv.refl _)
  let κ : Fin (v'.length * 3) ≃ Fin (v.length * 3) :=
    finProdFinEquiv.symm.trans (σ.symm.trans finProdFinEquiv)
  have hL3 : v.length * 3 = v'.length * 3 := by rw [hL]
  { O := ⟨κ.trans (G.O.toPerm.trans (finCongr hL3))⟩
    X := ⟨κ.trans (G.X.toPerm.trans (finCongr hL3))⟩
    disjoint := fun c h => G.disjoint (κ c) ((finCongr hL3).injective h) }

theorem sTransport_O (hL : v.length = v'.length) (τ : Fin v.length ≃ Fin v'.length)
    (G : GridDiagram (v.length * 3)) (p : Fin v.length × Fin 3) :
    ((sTransport hL τ G).O (finProdFinEquiv (τ p.1, p.2))).val =
      (G.O (finProdFinEquiv p)).val := by
  simp [sTransport]

theorem sTransport_X (hL : v.length = v'.length) (τ : Fin v.length ≃ Fin v'.length)
    (G : GridDiagram (v.length * 3)) (p : Fin v.length × Fin 3) :
    ((sTransport hL τ G).X (finProdFinEquiv (τ p.1, p.2))).val =
      (G.X (finProdFinEquiv p)).val := by
  simp [sTransport]

theorem oHeight2_transport (τ : Fin v.length ≃ Fin v'.length)
    (hlet : ∀ h, v'[(τ h).val] = v[h.val]) (p : Fin v.length × Fin 3) :
    v'.oHeight2 (τ p.1, p.2) = v.oHeight2 p := by
  simp only [SignedAdjacentWord.oHeight2, hlet]

theorem xHeight2_transport (τ : Fin v.length ≃ Fin v'.length)
    (hlet : ∀ h, v'[(τ h).val] = v[h.val]) (p : Fin v.length × Fin 3) :
    v'.xHeight2 (τ p.1, p.2) = v.xHeight2 p := by
  simp only [SignedAdjacentWord.xHeight2, hlet]

theorem transport_surj (τ : Fin v.length ≃ Fin v'.length) (a : Fin v'.length × Fin 3) :
    ∃ p : Fin v.length × Fin 3, (τ p.1, p.2) = a := ⟨(τ.symm a.1, a.2), by simp⟩

/-- Transport of signed word grids along a bijection of letters preserving the cyclic gaps. -/
theorem isSignedWordGrid_transport_gap (hL : v.length = v'.length)
    (τ : Fin v.length ≃ Fin v'.length) (hlet : ∀ h, v'[(τ h).val] = v[h.val])
    (hgap : ∀ p q : Fin v.length × Fin 3,
      v'.cornerGap (τ p.1, p.2) (τ q.1, q.2) = v.cornerGap p q)
    {G : GridDiagram (v.length * 3)} (hG : IsSignedWordGrid v G) :
    IsSignedWordGrid v' (sTransport hL τ G) := by
  constructor
  · intro a b hab
    obtain ⟨p, rfl⟩ := transport_surj τ a
    obtain ⟨q, rfl⟩ := transport_surj τ b
    rw [oHeight2_transport τ hlet, oHeight2_transport τ hlet] at hab
    rw [Fin.lt_def, sTransport_O, sTransport_O]
    exact hG.O_lt p q hab
  · intro b
    obtain ⟨q, rfl⟩ := transport_surj τ b
    obtain ⟨p, hp1, hp2, hp3⟩ := hG.X_eq q
    refine ⟨(τ p.1, p.2), ?_, fun a ha => ?_, ?_⟩
    · rw [oHeight2_transport τ hlet, xHeight2_transport τ hlet, hp1]
    · obtain ⟨p', rfl⟩ := transport_surj τ a
      rw [oHeight2_transport τ hlet, xHeight2_transport τ hlet] at ha
      rw [hgap, hgap]
      exact hp2 p' ha
    · apply Fin.ext
      rw [sTransport_X, sTransport_O, hp3]

/-- Transport of signed word grids along a bijection of letters commuting with the matchings. -/
theorem isSignedWordGrid_transport_sM (hL : v.length = v'.length)
    (τ : Fin v.length ≃ Fin v'.length) (hlet : ∀ h, v'[(τ h).val] = v[h.val])
    (hM : ∀ p : Fin v.length × Fin 3, sM v' (τ p.1, p.2) = (τ (sM v p).1, (sM v p).2))
    {G : GridDiagram (v.length * 3)} (hG : IsSignedWordGrid v G) :
    IsSignedWordGrid v' (sTransport hL τ G) := by
  rw [isSignedWordGrid_iff]
  constructor
  · intro a b hab
    obtain ⟨p, rfl⟩ := transport_surj τ a
    obtain ⟨q, rfl⟩ := transport_surj τ b
    rw [oHeight2_transport τ hlet, oHeight2_transport τ hlet] at hab
    rw [Fin.lt_def, sTransport_O, sTransport_O]
    exact hG.O_lt p q hab
  · intro b
    obtain ⟨q, rfl⟩ := transport_surj τ b
    have hs : (sM v').symm (τ q.1, q.2) =
        (τ ((sM v).symm q).1, ((sM v).symm q).2) := by
      rw [Equiv.symm_apply_eq, hM, Equiv.apply_symm_apply]
    apply Fin.ext
    rw [hs, sTransport_X, sTransport_O, X_eq_sM hG]

theorem sTransport_eq_relabel (hL : v.length = v'.length) (τ : Fin v.length ≃ Fin v'.length)
    (G : GridDiagram (v.length * 3)) (σ : Equiv.Perm (Fin (v.length * 3)))
    (hσ : ∀ p : Fin v.length × Fin 3, σ (finProdFinEquiv p) =
      Fin.cast (by rw [hL]) (finProdFinEquiv (τ p.1, p.2))) :
    sTransport hL τ G = GridDiagram.castSize (by rw [hL]) (G.relabelColumns σ) := by
  ext c
  · obtain ⟨p, rfl⟩ : ∃ p : Fin v.length × Fin 3, finProdFinEquiv (τ p.1, p.2) = c := by
      obtain ⟨a, rfl⟩ := finProdFinEquiv.surjective c
      obtain ⟨p, rfl⟩ := transport_surj τ a
      exact ⟨p, rfl⟩
    rw [sTransport_O, GridDiagram.castSize_O_apply, Fin.val_cast,
      GridDiagram.relabelColumns_O_apply]
    congr 2
    rw [eq_comm, Equiv.symm_apply_eq, hσ]
  · obtain ⟨p, rfl⟩ : ∃ p : Fin v.length × Fin 3, finProdFinEquiv (τ p.1, p.2) = c := by
      obtain ⟨a, rfl⟩ := finProdFinEquiv.surjective c
      obtain ⟨p, rfl⟩ := transport_surj τ a
      exact ⟨p, rfl⟩
    rw [sTransport_X, GridDiagram.castSize_X_apply, Fin.val_cast,
      GridDiagram.relabelColumns_X_apply]
    congr 2
    rw [eq_comm, Equiv.symm_apply_eq, hσ]

end Transport

/-! ### Cyclic rotation -/

theorem finRotate_pow_val {N : ℕ} (x : Fin N) (k : ℕ) :
    ((finRotate N ^ k) x).val = (x.val + k) % N := by
  have hx := x.isLt
  induction k with
  | zero => simp [Nat.mod_eq_of_lt hx]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_val_eq, ih]
    have hN : 0 < N := by omega
    have hlt := Nat.mod_lt (x.val + k) hN
    have key : ((x.val + k) % N + 1) % N = (x.val + (k + 1)) % N := by
      rw [← Nat.add_assoc, Nat.mod_add_mod]
    split_ifs with h
    · rw [← key, Nat.mod_eq_of_lt h]
    · rw [← key, show (x.val + k) % N + 1 = N by omega, Nat.mod_self]

section Rotation

variable (x y : SignedAdjacentWord m)

theorem rot_length : (x ++ y).length = (y ++ x).length := by simp [Nat.add_comm]

/-- The letter bijection of the rotation `x ++ y ↦ y ++ x`. -/
def rotL : Fin (x ++ y).length ≃ Fin (y ++ x).length where
  toFun h := ⟨if h.val < x.length then h.val + y.length else h.val - x.length, by
    have := h.isLt; simp only [List.length_append] at this ⊢; split_ifs <;> omega⟩
  invFun h := ⟨if h.val < y.length then h.val + x.length else h.val - y.length, by
    have := h.isLt; simp only [List.length_append] at this ⊢; split_ifs <;> omega⟩
  left_inv h := by
    apply Fin.ext; have := h.isLt; simp only [List.length_append] at this
    simp only; split_ifs <;> omega
  right_inv h := by
    apply Fin.ext; have := h.isLt; simp only [List.length_append] at this
    simp only; split_ifs <;> omega

theorem rotL_val (h : Fin (x ++ y).length) :
    (rotL x y h).val = if h.val < x.length then h.val + y.length else h.val - x.length := rfl

theorem rotL_getElem (h : Fin (x ++ y).length) : (y ++ x)[(rotL x y h).val] = (x ++ y)[h.val] := by
  have := h.isLt
  simp only [List.length_append] at this
  by_cases h1 : h.val < x.length
  · have e : (rotL x y h).val = h.val + y.length := by rw [rotL_val, if_pos h1]
    simp only [e]
    rw [List.getElem_append_right (by omega), List.getElem_append_left h1]
    simp
  · have e : (rotL x y h).val = h.val - x.length := by rw [rotL_val, if_neg h1]
    simp only [e]
    rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]

theorem rotL_gap (p q : Fin (x ++ y).length × Fin 3) :
    (y ++ x).cornerGap (rotL x y p.1, p.2) (rotL x y q.1, q.2) = (x ++ y).cornerGap p q := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  have hp2 := p.2.isLt
  have hq2 := q.2.isLt
  simp only [List.length_append] at hp hq
  have c1 := (finProdFinEquiv p).isLt
  have c2 := (finProdFinEquiv q).isLt
  have c3 := (finProdFinEquiv ((rotL x y p.1, p.2) : Fin (y ++ x).length × Fin 3)).isLt
  have c4 := (finProdFinEquiv ((rotL x y q.1, q.2) : Fin (y ++ x).length × Fin 3)).isLt
  unfold SignedAdjacentWord.cornerGap
  rw [modsub c2 c1, modsub c4 c3]
  simp only [finProdFinEquiv_val3, rotL_val, List.length_append] at c1 c2 c3 c4 ⊢
  split_ifs <;> omega

/-- **Cyclic rotation.** -/
theorem fwd_rotate : Fwd (x ++ y) (y ++ x) := by
  intro G hG
  have hL := rot_length x y
  refine ⟨sTransport hL (rotL x y) G,
    isSignedWordGrid_transport_gap hL (rotL x y) (rotL_getElem x y) (rotL_gap x y) hG, ?_⟩
  rw [sTransport_eq_relabel hL (rotL x y) G (finRotate _ ^ (3 * y.length))]
  · exact (GridDiagram.movesTo_relabelColumns_finRotate_pow G _).trans
      (GridDiagram.movesTo_castSize _ _)
  · intro p
    apply Fin.ext
    rw [finRotate_pow_val, Fin.val_cast]
    have hp := p.1.isLt
    have hp2 := p.2.isLt
    simp only [List.length_append] at hp
    simp only [finProdFinEquiv_val3, rotL_val, List.length_append]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt (by omega)]; ring
    · rw [show p.2.val + 3 * p.1.val + 3 * y.length =
          (p.2.val + 3 * (p.1.val - x.length)) + (x.length + y.length) * 3 by
            rw [Nat.add_mul]; omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

end Rotation

/-! ### Far commutation -/

section Far

variable (u w : SignedAdjacentWord m) (a b : Fin (m - 1) × ℤˣ)

theorem far_length' : (u ++ a :: b :: w).length = (u ++ b :: a :: w).length := by simp

/-- The letter bijection of a far commutation. -/
def farL : Fin (u ++ a :: b :: w).length ≃ Fin (u ++ b :: a :: w).length where
  toFun h := ⟨if h.val = u.length then u.length + 1 else if h.val = u.length + 1 then u.length
      else h.val, by have := h.isLt; simp only [List.length_append, List.length_cons] at this ⊢
                     split_ifs <;> omega⟩
  invFun h := ⟨if h.val = u.length then u.length + 1 else if h.val = u.length + 1 then u.length
      else h.val, by have := h.isLt; simp only [List.length_append, List.length_cons] at this ⊢
                     split_ifs <;> omega⟩
  left_inv h := by apply Fin.ext; simp only; split_ifs <;> omega
  right_inv h := by apply Fin.ext; simp only; split_ifs <;> omega

theorem farL_val (h : Fin (u ++ a :: b :: w).length) :
    (farL u w a b h).val = if h.val = u.length then u.length + 1
      else if h.val = u.length + 1 then u.length else h.val := rfl

theorem farL_getElem (h : Fin (u ++ a :: b :: w).length) :
    (u ++ b :: a :: w)[(farL u w a b h).val] = (u ++ a :: b :: w)[h.val] := by
  have := h.isLt
  simp only [List.length_append, List.length_cons] at this
  by_cases h1 : h.val = u.length
  · have e : (farL u w a b h).val = u.length + 1 := by rw [farL_val, if_pos h1]
    simp only [e, h1]
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    simp
  · by_cases h2 : h.val = u.length + 1
    · have e : (farL u w a b h).val = u.length := by rw [farL_val, if_neg h1, if_pos h2]
      simp only [e, h2]
      rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
      simp
    · have e : (farL u w a b h).val = h.val := by rw [farL_val, if_neg h1, if_neg h2]
      simp only [e]
      by_cases h3 : h.val < u.length
      · rw [List.getElem_append_left h3, List.getElem_append_left h3]
      · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        obtain ⟨k, hk⟩ : ∃ k, h.val - u.length = k + 2 := ⟨h.val - u.length - 2, by omega⟩
        simp only [hk, List.getElem_cons_succ]

theorem farL_occ_order (hab : a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val) (s : ℕ)
    {k k' : Fin (u ++ a :: b :: w).length} (hk : Occ (u ++ a :: b :: w) s k)
    (hk' : Occ (u ++ a :: b :: w) s k') : k < k' ↔ farL u w a b k < farL u w a b k' := by
  have ha : (u ++ a :: b :: w)[u.length]'(by simp) = a := by
    rw [List.getElem_append_right (by omega)]; simp
  have hb : (u ++ a :: b :: w)[u.length + 1]'(by simp) = b := by
    rw [List.getElem_append_right (by omega)]; simp
  have hno : ¬ (Occ (u ++ a :: b :: w) s ⟨u.length, by simp⟩ ∧
      Occ (u ++ a :: b :: w) s ⟨u.length + 1, by simp⟩) := by
    rintro ⟨h1, h2⟩
    simp only [Occ, ha, hb] at h1 h2
    omega
  have hv := farL_val u w a b k
  have hv' := farL_val u w a b k'
  rw [Fin.lt_def, Fin.lt_def, hv, hv']
  have e1 : k.val = u.length → k' ≠ ⟨u.length + 1, by simp⟩ := fun h e =>
    hno ⟨by rwa [show k = ⟨u.length, by simp⟩ from Fin.ext h] at hk, by rwa [e] at hk'⟩
  have e2 : k.val = u.length + 1 → k' ≠ ⟨u.length, by simp⟩ := fun h e =>
    hno ⟨by rwa [e] at hk', by rwa [show k = ⟨u.length + 1, by simp⟩ from Fin.ext h] at hk⟩
  have e1' : k'.val = u.length → k.val ≠ u.length + 1 := fun h e =>
    hno ⟨by rwa [show k' = ⟨u.length, by simp⟩ from Fin.ext h] at hk',
      by rwa [show k = ⟨u.length + 1, by simp⟩ from Fin.ext e] at hk⟩
  have f1 : k.val = u.length → k'.val ≠ u.length + 1 := fun h e => e1 h (Fin.ext e)
  have f2 : k.val = u.length + 1 → k'.val ≠ u.length := fun h e => e2 h (Fin.ext e)
  split_ifs <;> omega

theorem farL_sM (hab : a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val)
    (p : Fin (u ++ a :: b :: w).length × Fin 3) :
    sM (u ++ b :: a :: w) (farL u w a b p.1, p.2) =
      (farL u w a b (sM (u ++ a :: b :: w) p).1, (sM (u ++ a :: b :: w) p).2) := by
  have hlet := farL_getElem u w a b
  by_cases hp : p.2 = 0
  · rw [show p = (p.1, 0) from Prod.ext rfl hp]
    simp only [sM_middle]
  have hev : (u ++ a :: b :: w).oHeight2 p % 2 = 0 := by
    have := (oHeight2_odd_iff _ p).not.mpr hp; omega
  have hq2 : (sM (u ++ a :: b :: w) p).2 ≠ 2 := fun h => by
    have := (xHeight2_odd_iff _ _).mpr h; rw [sM_height] at this; omega
  have hs : (u ++ b :: a :: w).oHeight2 (farL u w a b p.1, p.2) =
      (u ++ a :: b :: w).oHeight2 p := oHeight2_transport _ hlet p
  have hocc : ∀ k, Occ (u ++ b :: a :: w) ((u ++ a :: b :: w).oHeight2 p / 2) (farL u w a b k) ↔
      Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2) k := by
    intro k; unfold Occ; rw [hlet k]
  have op := occ_of_oHeight2 (u ++ a :: b :: w) hp
  have oq : Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2)
      (sM (u ++ a :: b :: w) p).1 := by
    have := occ_of_xHeight2 (u ++ a :: b :: w) hq2; rwa [sM_height] at this
  have hord : ∀ {k k' : Fin (u ++ a :: b :: w).length},
      Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2) k →
      Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2) k' →
        (k < k' ↔ farL u w a b k < farL u w a b k') :=
    fun hk hk' => farL_occ_order u w a b hab _ hk hk'
  have hle : ∀ {k k'}, Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2) k →
      Occ (u ++ a :: b :: w) ((u ++ a :: b :: w).oHeight2 p / 2) k' →
        (k ≤ k' ↔ farL u w a b k ≤ farL u w a b k') := by
    intro k k' hk hk'
    rw [← not_lt, ← not_lt, hord hk' hk]
  apply sM_eq_of_spec (u ++ b :: a :: w) (farL u w a b p.1, p.2) _ hp
  · rw [xHeight2_transport _ hlet, hs, sM_height]
  · rw [hs]
    rcases sM_spec (u ++ a :: b :: w) p hp with ⟨hlt, hmin⟩ | ⟨hle', hall⟩
    · left
      refine ⟨(hord op oq).mp hlt, fun k' hk' hpk => ?_⟩
      obtain ⟨k, rfl⟩ := (farL u w a b).surjective k'
      have hk := (hocc k).mp hk'
      exact (hle oq hk).mp (hmin k hk ((hord op hk).mpr hpk))
    · right
      refine ⟨(hle oq op).mp hle', fun k' hk' => ?_⟩
      obtain ⟨k, rfl⟩ := (farL u w a b).surjective k'
      have hk := (hocc k).mp hk'
      exact ⟨(hle oq hk).mp (hall k hk).1, (hle hk op).mp (hall k hk).2⟩

theorem height_bounds (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3) :
    2 * (v[p.1.val].1).val ≤ v.oHeight2 p ∧ v.oHeight2 p ≤ 2 * (v[p.1.val].1).val + 2 ∧
      2 * (v[p.1.val].1).val ≤ v.xHeight2 p ∧ v.xHeight2 p ≤ 2 * (v[p.1.val].1).val + 2 := by
  rcases p with ⟨h, c⟩
  simp only [SignedAdjacentWord.oHeight2, SignedAdjacentWord.xHeight2, signedOHeight2,
    signedXHeight2]
  split_ifs <;> fin_cases c <;> simp

theorem height_bounds' (v : SignedAdjacentWord m) (p : Fin v.length × Fin 3)
    {c : Fin (m - 1) × ℤˣ} (h : v[p.1.val] = c) :
    2 * c.1.val ≤ v.oHeight2 p ∧ v.oHeight2 p ≤ 2 * c.1.val + 2 ∧
      2 * c.1.val ≤ v.xHeight2 p ∧ v.xHeight2 p ≤ 2 * c.1.val + 2 := by
  rw [← h]; exact height_bounds v p

theorem nonint_of_far_letters (v : SignedAdjacentWord m) {G : GridDiagram (v.length * 3)}
    (hG : IsSignedWordGrid v G) (pA pB : Fin v.length × Fin 3) {A B : Fin (m - 1) × ℤˣ}
    (hA : v[pA.1.val] = A) (hB : v[pB.1.val] = B)
    (hab : A.1.val + 2 ≤ B.1.val ∨ B.1.val + 2 ≤ A.1.val) :
    NonintN (G.O (finProdFinEquiv pA)).val (G.X (finProdFinEquiv pA)).val
      (G.O (finProdFinEquiv pB)).val (G.X (finProdFinEquiv pB)).val := by
  have bA := height_bounds' v pA hA
  have bB := height_bounds' v pB hB
  have hA' := (sM_symm_min v pA).1
  have hB' := (sM_symm_min v pB).1
  rw [X_eq_sM hG pA, X_eq_sM hG pB]
  apply nonintN_of_lt
  rcases hab with hab | hab
  · left
    have l1 := hG.O_lt pA pB (by omega)
    have l2 := hG.O_lt pA ((sM v).symm pB) (by omega)
    have l3 := hG.O_lt ((sM v).symm pA) pB (by omega)
    have l4 := hG.O_lt ((sM v).symm pA) ((sM v).symm pB) (by omega)
    simp only [Fin.lt_def] at l1 l2 l3 l4
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨l1, l3⟩, l2, l4⟩
  · right
    have l1 := hG.O_lt pB pA (by omega)
    have l2 := hG.O_lt pB ((sM v).symm pA) (by omega)
    have l3 := hG.O_lt ((sM v).symm pB) pA (by omega)
    have l4 := hG.O_lt ((sM v).symm pB) ((sM v).symm pA) (by omega)
    simp only [Fin.lt_def] at l1 l2 l3 l4
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨l1, l3⟩, l2, l4⟩

theorem far_colsNonint' (hab : a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val)
    {G : GridDiagram ((u ++ a :: b :: w).length * 3)}
    (hG : IsSignedWordGrid (u ++ a :: b :: w) G) (c c' : Fin 3) :
    NonintN (G.O (finProdFinEquiv ((⟨u.length, by simp⟩ : Fin (u ++ a :: b :: w).length), c))).val
      (G.X (finProdFinEquiv ((⟨u.length, by simp⟩ : Fin (u ++ a :: b :: w).length), c))).val
      (G.O (finProdFinEquiv
        ((⟨u.length + 1, by simp⟩ : Fin (u ++ a :: b :: w).length), c'))).val
      (G.X (finProdFinEquiv
        ((⟨u.length + 1, by simp⟩ : Fin (u ++ a :: b :: w).length), c'))).val := by
  apply nonint_of_far_letters _ hG _ _ (A := a) (B := b) _ _ hab
  · simp only; rw [List.getElem_append_right (by omega)]; simp
  · simp only; rw [List.getElem_append_right (by omega)]; simp

/-- **Far commutation with arbitrary signs.** -/
theorem fwd_far (hab : a.1.val + 2 ≤ b.1.val ∨ b.1.val + 2 ≤ a.1.val) :
    Fwd (u ++ a :: b :: w) (u ++ b :: a :: w) := by
  intro G hG
  have hL := far_length' u w a b
  have hn : 3 * u.length + 6 ≤ (u ++ a :: b :: w).length * 3 := by simp; omega
  have hL3 : (u ++ a :: b :: w).length * 3 = (u ++ b :: a :: w).length * 3 := by rw [hL]
  have hlenu : u.length < (u ++ a :: b :: w).length := by simp
  have hlenu1 : u.length + 1 < (u ++ a :: b :: w).length := by simp
  obtain ⟨G', hm, hG'⟩ := exists_movesTo_blockSwap G (3 * u.length) hn (by
      intro c c'
      have h := far_colsNonint' u w a b hab hG c c'
      have e1 : (⟨3 * u.length + c.val, by omega⟩ : Fin ((u ++ a :: b :: w).length * 3)) =
          finProdFinEquiv ((⟨u.length, hlenu⟩ : Fin (u ++ a :: b :: w).length), c) := by
        apply Fin.ext; simp [finProdFinEquiv_apply_val]; ring
      have e2 : (⟨3 * u.length + 3 + c'.val, by omega⟩ :
          Fin ((u ++ a :: b :: w).length * 3)) =
          finProdFinEquiv ((⟨u.length + 1, hlenu1⟩ : Fin (u ++ a :: b :: w).length), c') := by
        apply Fin.ext; simp [finProdFinEquiv_apply_val]; ring
      rw [e1, e2]
      exact h)
  refine ⟨sTransport hL (farL u w a b) G,
    isSignedWordGrid_transport_sM hL (farL u w a b) (farL_getElem u w a b)
      (farL_sM u w a b hab) hG, ?_⟩
  have heq : sTransport hL (farL u w a b) G = GridDiagram.castSize hL3 G' := by
    have hsurj : ∀ c : Fin ((u ++ b :: a :: w).length * 3),
        ∃ q : Fin (u ++ a :: b :: w).length × Fin 3,
        finProdFinEquiv (farL u w a b q.1, q.2) = c := by
      intro c
      obtain ⟨a', rfl⟩ := finProdFinEquiv.surjective c
      obtain ⟨p, rfl⟩ := transport_surj (farL u w a b) a'
      exact ⟨p, rfl⟩
    have key : ∀ q : Fin (u ++ a :: b :: w).length × Fin 3,
        blockSwapVal (3 * u.length) (finProdFinEquiv (farL u w a b q.1, q.2)).val =
          (finProdFinEquiv q).val := by
      intro q
      have hv := farL_val u w a b q.1
      have h2 := q.2.isLt
      simp only [finProdFinEquiv_apply_val, blockSwapVal]
      split_ifs at hv ⊢ <;> omega
    ext c
    · obtain ⟨q, rfl⟩ := hsurj c
      rw [sTransport_O, GridDiagram.castSize_O_apply, Fin.val_cast, (hG' _).1]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (key q).symm
    · obtain ⟨q, rfl⟩ := hsurj c
      rw [sTransport_X, GridDiagram.castSize_X_apply, Fin.val_cast, (hG' _).2]
      congr 2
      apply Fin.ext
      simp only [Fin.val_cast]
      exact (key q).symm
  rw [heq]
  exact hm.trans (GridDiagram.movesTo_castSize hL3 G')

end Far

end OnLeConjecture.KnotTheory.SignedGrid
