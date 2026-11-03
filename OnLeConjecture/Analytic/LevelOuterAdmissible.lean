/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelRootInput

/-!
# Admissible setups for the outer braid

This module states the hypotheses under which the field (B) `OuterHolds` of a setup
`P : LevelProjectionSetup A L` (`LevelRootInput.lean`) is proved in `LevelOuterBraid.lean`. They
are the properties of the representative used in the paragraph "Over `|h| = ρ` the source sheets
vary by the implicit function theorem without collision as `v` moves from zero to the chosen
level" of Section 3 of the written proof of Statement E (`statement-E-complete-proof.tex`,
subsections "A proper representative with the correct number of sheets" and "Global
factorization, exponent count, and transitivity").

Write `R = L.radius`, `s = L.parameter`, `h = P.baseCoord`, `ζ = P.fibreCoord`,
`ρ₂ = P.outerRadius` and `v = H₀`.

* `levelBaseMap A h x = (v x, h (H x))`: the map of the source to the pairs of a level and a base
  value.
* `levelRootsAt A R h ζ s' c`: the roots of the level `v = s'` over the base value `c`, for an
  arbitrary level `s'`. The roots of the setup are `levelRootsAt A R h ζ s`.
* `LevelProjectionSetup.OuterAdmissible P`: the hypotheses. `H` is analytic at every point of
  the closed ball `B̄_R`; the base coordinate is transverse to the image curve `W` (the
  restriction of `W` to the line `{h = 0, ζ = 1}` of the target plane `{z₀ = 0}` has order `S`);
  the only common zero of `(v, h ∘ H)` on `B̄_R` is the origin; there are radii
  `η > |s|` (`levelDisc`) and `δ > ρ₂` (`centralDisc`) such that

  - no point of the sphere `∂B_R` with `|v| < η` has `|h ∘ H| = ρ₂`, and the differential of
    `levelBaseMap` is injective at every point of `B_R` with `|v| < η` and `|h ∘ H| = ρ₂`
    (the vertical boundary of the bidisc for all levels between `0` and `s`);
  - every point of `∂B_R` with `v = 0` has `|h ∘ H| ≥ δ`, and the differential of
    `levelBaseMap` is injective at every point of `B_R` with `v = 0` and `0 < |h ∘ H| < δ`
    (the central curve is unramified over the punctured disc of radius `δ`).
-/

@[expose] public noncomputable section

open Set Function Metric

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The map `x ↦ (v x, h (H x))` of the source to the pairs of a level and a base value. -/
def levelBaseMap (A : ResolutionSectionAssembly g hd hi) (baseCoord : Source 3 →L[ℂ] ℂ) :
    Source 2 → ℂ × ℂ := fun x => (A.H x 0, baseCoord (A.H x))

/-- The roots of the level `v = s` of the ball of radius `R` over the base value `c`, for an
arbitrary level `s`. -/
def levelRootsAt (A : ResolutionSectionAssembly g hd hi) (R : ℝ)
    (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) (s c : ℂ) : Set ℂ :=
  (fun x => fibreCoord (A.H x)) '' {x | x ∈ ball (0 : Source 2) R ∧ A.H x 0 = s ∧
    baseCoord (A.H x) = c}

theorem levelRoots_eq_levelRootsAt (A : ResolutionSectionAssembly g hd hi)
    (L : ResolutionSectionLevel A) (baseCoord fibreCoord : Source 3 →L[ℂ] ℂ) :
    levelRoots A L baseCoord fibreCoord =
      levelRootsAt A L.radius baseCoord fibreCoord L.parameter :=
  rfl

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}

/-- **The hypotheses for the outer braid.** -/
structure OuterAdmissible (P : LevelProjectionSetup A L) where
  /-- `H` is analytic at every point of the closed ball `B̄_R`. -/
  analyticAt : ∀ x ∈ closedBall (0 : Source 2) L.radius, AnalyticAt ℂ A.H x
  /-- The base coordinate is transverse to the image curve: the restriction of the image equation
  to the line `{h = 0, ζ = 1}` of the target plane has order `S`. -/
  transverse : ∃ u : Source 2, P.baseCoord (hyperplaneInclusion 2 u) = 0 ∧
    P.fibreCoord (hyperplaneInclusion 2 u) = 1 ∧
    vanishingOrder (lineRestriction u A.imageEquation) = (A.squareSum : ℕ∞)
  /-- The only common zero of `(v, h ∘ H)` on `B̄_R` is the origin. -/
  isolated : ∀ x ∈ closedBall (0 : Source 2) L.radius, A.H x 0 = 0 →
    P.baseCoord (A.H x) = 0 → x = 0
  /-- The radius `η` of the disc of levels. -/
  levelDisc : ℝ
  parameter_lt : ‖L.parameter‖ < levelDisc
  /-- No point of the sphere `∂B_R` lies over the vertical boundary `|v| < η`, `|h| = ρ₂`. -/
  outer_boundary : ∀ x : Source 2, ‖x‖ = L.radius → ‖A.H x 0‖ < levelDisc →
    ‖P.baseCoord (A.H x)‖ ≠ P.outerRadius
  /-- The vertical boundary `|v| < η`, `|h| = ρ₂` is unramified. -/
  outer_unramified : ∀ x ∈ ball (0 : Source 2) L.radius, ‖A.H x 0‖ < levelDisc →
    ‖P.baseCoord (A.H x)‖ = P.outerRadius → Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)
  /-- The radius `δ` of the punctured disc over which the central curve is unramified. -/
  centralDisc : ℝ
  outerRadius_lt : P.outerRadius < centralDisc
  /-- On the sphere `∂B_R`, the central curve lies over `|h| ≥ δ`. -/
  central_boundary : ∀ x : Source 2, ‖x‖ = L.radius → A.H x 0 = 0 →
    centralDisc ≤ ‖P.baseCoord (A.H x)‖
  /-- The central curve is unramified over the punctured disc `0 < |h| < δ`. -/
  central_unramified : ∀ x ∈ ball (0 : Source 2) L.radius, A.H x 0 = 0 →
    0 < ‖P.baseCoord (A.H x)‖ → ‖P.baseCoord (A.H x)‖ < centralDisc →
    Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)

end LevelProjectionSetup

end OnLeConjecture.Analytic
