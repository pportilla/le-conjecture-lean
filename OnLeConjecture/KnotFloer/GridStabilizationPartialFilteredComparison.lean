/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationComparisonBounds
public import OnLeConjecture.KnotFloer.GridFullLaurentBlockedBounds

/-!
# The shifted two-copy filtration of the stabilization retract

The second copy has Maslov and Alexander gradings lowered by one. With these shifts,
the specified inclusion and projection preserve degree and both filtration coordinates.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R]

/-- The two-copy Maslov piece, with the second copy shifted down by one. -/
noncomputable def stabilizationTargetMaslovPiece (m : ℤ) :
    Submodule R (LaurentChain R n × LaurentChain R n) :=
  (laurentMaslovPiece G R m).prod (laurentMaslovPiece G R (m + 1))

/-- The two-copy filtration, with the second Alexander coordinate shifted down by one. -/
noncomputable def stabilizationTargetBifiltrationLevel (u v : ℝ) :
    Submodule R (LaurentChain R n × LaurentChain R n) :=
  (laurentBifiltrationLevel G R u v).prod (laurentBifiltrationLevel G R u (v + 1))

variable [CharP R 2]

/-- The corrected inclusion expressed in the actual stabilized chain module. -/
theorem localStabilizationRetraction_incl_eq_corrected
    (c : LaurentChain R n × LaurentChain R n) :
    (localStabilizationRetraction G s R).incl c =
      localStabilizationFirstInclusion G s R c.1 + laurentStabilizationCenterInclusion G s R c.2 -
        (localStabilizationRetraction G s R).homotopy
          (laurentXBlockedDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
            R {s.castSucc, s.succ} (laurentStabilizationCenterInclusion G s R c.2)) := by
  rw [localStabilizationRetraction_incl, localStabilizationRetraction_homotopy]
  change laurentOffCenterInclusion G s R (_ + _) + _ =
    laurentOffCenterInclusion G s R _ + _ - (-laurentOffCenterInclusion G s R _)
  rw [map_add, sub_neg_eq_add]
  dsimp only [localStabilizationConnecting, LinearMap.comp_apply]
  abel

/-- The partially blocked projection preserves the shifted Maslov grading. -/
theorem localStabilizationRetraction_proj_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    (localStabilizationRetraction G s R).proj c ∈ stabilizationTargetMaslovPiece G R m := by
  rw [localStabilizationRetraction_proj]
  exact ⟨localStabilizationFirstProjection_mem_maslovPiece G s R hc,
    laurentStabilizationCenterProjection_mem_maslovPiece G s R hc⟩

/-- The partially blocked projection preserves the shifted bifiltration. -/
theorem localStabilizationRetraction_proj_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    (localStabilizationRetraction G s R).proj c ∈ stabilizationTargetBifiltrationLevel G R u v := by
  rw [localStabilizationRetraction_proj]
  exact ⟨localStabilizationFirstProjection_mem_bifiltrationLevel G s R hc,
    laurentStabilizationCenterProjection_mem_bifiltrationLevel G s R hc⟩

/-- The corrected inclusion preserves the shifted Maslov grading. -/
theorem localStabilizationRetraction_incl_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R n × LaurentChain R n} (hc : c ∈ stabilizationTargetMaslovPiece G R m) :
    (localStabilizationRetraction G s R).incl c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m := by
  have hcenter : laurentStabilizationCenterInclusion G s R c.2 ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m := by
    simpa only [add_sub_cancel_right] using
      laurentStabilizationCenterInclusion_mem_maslovPiece G s R hc.2
  rw [localStabilizationRetraction_incl_eq_corrected]
  apply Submodule.sub_mem _
    (Submodule.add_mem _ (localStabilizationFirstInclusion_mem_maslovPiece G s R hc.1) hcenter)
  simpa only [sub_add_cancel] using localStabilizationRetraction_homotopy_mem_maslovPiece G s R
    (laurentXBlockedDifferential_mem_maslovPiece
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ} hcenter)

/-- The corrected inclusion preserves both shifted filtration coordinates. -/
theorem localStabilizationRetraction_incl_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R n × LaurentChain R n}
    (hc : c ∈ stabilizationTargetBifiltrationLevel G R u v) :
    (localStabilizationRetraction G s R).incl c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
  have hcenter : laurentStabilizationCenterInclusion G s R c.2 ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
    simpa only [add_sub_cancel_right] using
      laurentStabilizationCenterInclusion_mem_bifiltrationLevel G s R hc.2
  rw [localStabilizationRetraction_incl_eq_corrected]
  apply Submodule.sub_mem _
    (Submodule.add_mem _
      (localStabilizationFirstInclusion_mem_bifiltrationLevel G s R hc.1) hcenter)
  exact localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R
    (laurentXBlockedDifferential_mem_bifiltrationLevel
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ} hcenter)

end OnLeConjecture.KnotFloer.GridFull
