/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.KnotFloer.GridStabilizationTransferredComplex

/-!
# Degree and filtration of the full stabilization comparison homotopy

The finite inverse preserves each homogeneous piece and each filtration level.
Consequently the constructed full comparison homotopy has the required degree and bounds.
-/

@[expose] public section

namespace OnLeConjecture.KnotFloer.GridFull

open TauCeti Finsupp

variable {n : ℕ} (G : GridDiagram n) (s : Fin n) (R : Type*) [CommRing R] [CharP R 2]

/-- The full comparison homotopy is the previous homotopy followed by the finite inverse. -/
theorem fullStabilizationTransferredRetraction_homotopy_eq_inverse :
    (fullStabilizationTransferredRetraction G s R).homotopy =
      (localStabilizationRetraction G s R).homotopy * Ring.inverse
        (1 + laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
          R {s.castSucc, s.succ} * (localStabilizationRetraction G s R).homotopy) := by
  rw [fullStabilizationTransferredRetraction_homotopy]
  let H := (localStabilizationRetraction G s R).homotopy
  let δ := laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
    R {s.castSucc, s.succ}
  let I := Ring.inverse (1 + δ * H)
  have hI : I * (1 + δ * H) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_one_add_stabilizationXCrossing_homotopy G s R)
  have hI' : 1 - I * (δ * H) = I := by
    rw [mul_add, mul_one] at hI
    apply LinearMap.ext
    intro z
    apply Finsupp.ext
    intro i
    have hi := congrArg (fun f => f z i) hI
    change I z i + (I * (δ * H)) z i = z i at hi
    change z i - (I * (δ * H)) z i = I z i
    exact (eq_sub_of_add_eq hi).symm
  rw [stabilizationXSeries, LinearSpecialContraction.perturbationSeries_def]
  change H - H * (I * δ) * H = H * I
  calc
    _ = H * (1 - I * (δ * H)) := by
      apply LinearMap.ext
      intro z
      change H z - H (I (δ (H z))) = H (z - I (δ (H z)))
      exact (map_sub H z (I (δ (H z)))).symm
    _ = H * I := by rw [hI']

/-- The full comparison homotopy raises Laurent Maslov degree by one. -/
theorem fullStabilizationTransferredRetraction_homotopy_mem_maslovPiece {m : ℤ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m) :
    (fullStabilizationTransferredRetraction G s R).homotopy c ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R (m + 1) := by
  rw [fullStabilizationTransferredRetraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply localStabilizationRetraction_homotopy_mem_maslovPiece
  apply MatchingContraction.ringInverse_one_add_mem _
    (stabilizationXCrossing_homotopy_locallyNilpotent G s R)
    (laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m).toAddSubgroup _ hc
  intro z hz
  change laurentXCrossingDifferential (G.stabilizeX s.castSucc (G.X s).castSucc s)
    R {s.castSucc, s.succ} ((localStabilizationRetraction G s R).homotopy z) ∈
      laurentMaslovPiece (G.stabilizeX s.castSucc (G.X s).castSucc s) R m
  simpa only [Module.End.mul_apply, add_sub_cancel_right] using
    laurentXCrossingDifferential_mem_maslovPiece
      (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
      (localStabilizationRetraction_homotopy_mem_maslovPiece G s R hz)

/-- The full comparison homotopy preserves both real Laurent filtration coordinates. -/
theorem fullStabilizationTransferredRetraction_homotopy_mem_bifiltrationLevel {u v : ℝ}
    {c : LaurentChain R (n + 1)}
    (hc : c ∈ laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v) :
    (fullStabilizationTransferredRetraction G s R).homotopy c ∈
      laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v := by
  rw [fullStabilizationTransferredRetraction_homotopy_eq_inverse, Module.End.mul_apply]
  apply localStabilizationRetraction_homotopy_mem_bifiltrationLevel
  apply MatchingContraction.ringInverse_one_add_mem _
    (stabilizationXCrossing_homotopy_locallyNilpotent G s R)
    (laurentBifiltrationLevel (G.stabilizeX s.castSucc (G.X s).castSucc s) R u v).toAddSubgroup _ hc
  intro z hz y k hk
  obtain ⟨hfirst, hsecond⟩ := (laurentXCrossingDifferential_mem_bifiltrationLevel
    (G.stabilizeX s.castSucc (G.X s).castSucc s) R {s.castSucc, s.succ}
    (localStabilizationRetraction_homotopy_mem_bifiltrationLevel G s R hz)) y k hk
  exact ⟨hfirst, by linarith⟩

end OnLeConjecture.KnotFloer.GridFull
