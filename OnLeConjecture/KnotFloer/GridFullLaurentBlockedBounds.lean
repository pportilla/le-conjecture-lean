/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridFullLaurentXBlocking

/-!
# Grading and filtration of partially X-blocked Laurent differentials
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] (S : Finset (Fin n))

/-- The blocked differential is the full differential minus the selected crossing terms. -/
theorem laurentXBlockedDifferential_eq_sub :
    laurentXBlockedDifferential G R S =
      laurentDifferential G R - laurentXCrossingDifferential G R S := by
  rw [← laurentXBlocked_add_crossing G R S, add_sub_cancel_right]

/-- Every partially blocked differential lowers Maslov degree by one. -/
theorem laurentXBlockedDifferential_mem_maslovPiece {m : ℤ} {c : LaurentChain R n}
    (hc : c ∈ laurentMaslovPiece G R m) :
    laurentXBlockedDifferential G R S c ∈ laurentMaslovPiece G R (m - 1) := by
  rw [laurentXBlockedDifferential_eq_sub, LinearMap.sub_apply]
  exact Submodule.sub_mem _ (laurentDifferential_mem_maslovPiece G hc)
    (laurentXCrossingDifferential_mem_maslovPiece G R S hc)

/-- Every partially blocked differential preserves both Laurent filtration bounds. -/
theorem laurentXBlockedDifferential_mem_bifiltrationLevel {u v : ℝ} {c : LaurentChain R n}
    (hc : c ∈ laurentBifiltrationLevel G R u v) :
    laurentXBlockedDifferential G R S c ∈ laurentBifiltrationLevel G R u v := by
  rw [laurentXBlockedDifferential_eq_sub, LinearMap.sub_apply]
  apply Submodule.sub_mem _ (laurentDifferential_mem_bifiltrationLevel G R u v c hc)
  exact laurentBifiltrationLevel_mono G R le_rfl (by linarith : v - 1 ≤ v)
    (laurentXCrossingDifferential_mem_bifiltrationLevel G R S hc)

end OnLeConjecture.KnotFloer.GridFull
