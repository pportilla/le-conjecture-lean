/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridXSwitch

/-!
# Maps along finite sequences of adjacent X switches

A sequence contains the intermediate grid diagrams and the exact marking
equalities for each switch. Its length gives the Alexander-filtration cost.
In particular, a sequence of `2*g` switches induces a native chain map with
shifts `(0,g)`. No existence of a sequence from a smooth cobordism is assumed
as a theorem or asserted here.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti CategoryTheory

variable {n : ℕ}

/-- A finite sequence of switches of X markings in cyclically adjacent columns. -/
inductive XSwitchSequence : GridDiagram n → GridDiagram n → ℕ → Type
  | nil (G : GridDiagram n) : XSwitchSequence G G 0
  | cons {G H K : GridDiagram n} {l : ℕ}
      (a : Fin n) (ha : a ≠ finRotate n a)
      (hO : G.O = H.O) (hX : H.X = G.X.swapColumns a (finRotate n a))
      (tail : XSwitchSequence H K l) : XSwitchSequence G K (l + 1)

namespace XSwitchSequence

variable {G H : GridDiagram n} {l : ℕ}

/-- Every sequence retains the O markings. -/
theorem O_eq (s : XSwitchSequence G H l) : G.O = H.O := by
  induction s with
  | nil => rfl
  | cons a ha hO hX tail ih => exact hO.trans ih

/-- The Alexander change is bounded by half the number of switches. -/
theorem alexander_bounds (s : XSwitchSequence G H l) (x : GridState n) :
    G.alexander x - (l : ℚ) / 2 ≤ H.alexander x ∧
      H.alexander x ≤ G.alexander x + (l : ℚ) / 2 := by
  induction s with
  | nil => simp
  | cons a ha hO hX tail ih =>
      obtain ⟨hlo, hhi⟩ := alexander_adjacent_X_switch_bounds ha hO hX x
      push_cast
      constructor <;> linarith [ih.1, ih.2]

/-- The marking isomorphism induced by the sequence. Its underlying map is the identity. -/
noncomputable def chainIso (s : XSwitchSequence G H l)
    (R : Type*) [CommRing R] [CharP R 2] :
    laurentMaslovComplex G R ≅ laurentMaslovComplex H R :=
  laurentMaslovMarkingIso R s.O_eq

/-- The filtration cost of the map is at most half the sequence length. -/
theorem chainIso_shifts (s : XSwitchSequence G H l)
    (R : Type*) [CommRing R] [CharP R 2] :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (s.chainIso R).hom 0 ((l : ℝ) / 2) := by
  intro p q m c hc x k hk
  change k ∈ ((laurentMaslovChainEquiv G R m c : LaurentChain R n) x).coeff.support at hk
  obtain ⟨hp, hq⟩ := hc x k hk
  have hA : (H.alexander x : ℝ) ≤ (G.alexander x : ℝ) + (l : ℝ) / 2 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (s.alexander_bounds x).2
  exact ⟨by simpa using hp, by linarith⟩

/-- Exactly `2*g` switches give the shift required by the cobordism comparison. -/
theorem chainIso_shifts_of_twice (g : ℕ) (s : XSwitchSequence G H (2 * g))
    (R : Type*) [CommRing R] [CharP R 2] :
    (laurentMaslovBifiltration G R).Shifts (laurentMaslovBifiltration H R)
      (s.chainIso R).hom 0 (g : ℝ) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    using s.chainIso_shifts R

end XSwitchSequence

end OnLeConjecture.KnotFloer.GridFull
