/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.LevelOuterAdmissible

/-!
# The exported properties of the constructed projection setup

For a setup `P : LevelProjectionSetup A L` (`LevelRootInput.lean`) write `R = L.radius`,
`s = L.parameter`, `h = P.baseCoord`, `ζ = P.fibreCoord`, `ρ = P.radius` and `V = P.critical`.
The level is `Lev = {x ∈ B_R | H x 0 = s}` and its fibre over `c` is
`P.levelFibre c = {x ∈ Lev | h (H x) = c}`.

* `planeChartOf h ζ hc` and `P.planeChart`: the linear coordinates of the target plane
  `{z₀ = 0}` given by `(ζ, h)`, as the linear equivalence `y ↦ p` with `ζ (incl p) = y 0` and
  `h (incl p) = y 1`, where `incl = hyperplaneInclusion 2`.
* `LevelProjectionSetup.SetupProperties P`: the properties of the constructed setup used by the
  outer braid (B) and the local critical data (C). They are the hypotheses
  `LevelProjectionSetup.OuterAdmissible P` of `LevelOuterAdmissible.lean`, the compactness of
  `Lev ∩ (h ∘ H)⁻¹ (B̄(0, ρ))`, the description of `V` as the set of critical values of `h ∘ H`
  on `Lev` over `B(0, ρ)`, the finiteness of the fibres over `B(0, ρ)`, the membership of the
  base values of the singular points in `V`, the injectivity of `Re ζ` on every critical fibre,
  and the regularity of order `a_j` in the coordinate `ζ` of the local image equation at every
  singular point in the coordinates `P.planeChart`.
* `LevelSetupStatement`: every assembly has a level and a setup with these properties for which
  the fields (A) `RootFamilyHolds` and (D) `ConnectedHolds` hold.
* `levelProjectionSetupStatement_of_levelSetup`: this statement, together with the outer braid
  (B) for `OuterAdmissible` setups and the critical data (C) for setups with
  `SetupProperties`, gives `LevelProjectionSetupStatement`.
-/

@[expose] public noncomputable section

open Set Function Metric

namespace OnLeConjecture.Analytic

open OnLeConjecture.Analytic.Germ

variable {g : PointedMapGerm 2 3} {hd : g.differential = 0}
  {hi : g.HasInjectiveRepresentative}

/-- The linear map `p ↦ (ζ (incl p), h (incl p))` of the target plane `{z₀ = 0}`, for linear
forms `h` and `ζ` on the target. -/
def planeCoordinateMapOf (h ζ : Source 3 →L[ℂ] ℂ) : Source 2 →L[ℂ] Source 2 :=
  ContinuousLinearMap.pi fun i => Fin.cases (ζ.comp (hyperplaneInclusion 2))
    (fun _ => h.comp (hyperplaneInclusion 2)) i

@[simp]
theorem planeCoordinateMapOf_apply_zero (h ζ : Source 3 →L[ℂ] ℂ) (p : Source 2) :
    planeCoordinateMapOf h ζ p 0 = ζ (hyperplaneInclusion 2 p) := rfl

@[simp]
theorem planeCoordinateMapOf_apply_one (h ζ : Source 3 →L[ℂ] ℂ) (p : Source 2) :
    planeCoordinateMapOf h ζ p 1 = h (hyperplaneInclusion 2 p) := rfl

theorem planeCoordinateMapOf_injective {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) :
    Injective (planeCoordinateMapOf h ζ) := by
  intro p p' hpp
  have h0 := congrFun hpp 0
  have h1 := congrFun hpp 1
  simp only [planeCoordinateMapOf_apply_zero, planeCoordinateMapOf_apply_one] at h0 h1
  have hinc : hyperplaneInclusion 2 p = hyperplaneInclusion 2 p' := by
    apply hc
    simp only [hyperplaneInclusion_apply_zero, h0, h1]
  have := congrArg (hyperplaneTail 2) hinc
  simpa using this

/-- The linear coordinates of the target plane `{z₀ = 0}` given by `(ζ, h)`: the point
`planeChartOf h ζ hc y` of the plane has `ζ`-coordinate `y 0` and `h`-coordinate `y 1`. -/
def planeChartOf (h ζ : Source 3 →L[ℂ] ℂ) (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) :
    Source 2 ≃L[ℂ] Source 2 :=
  (LinearEquiv.ofInjectiveEndo (planeCoordinateMapOf h ζ).toLinearMap
    (planeCoordinateMapOf_injective hc)).symm.toContinuousLinearEquiv

theorem planeCoordinateMapOf_planeChartOf {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) (y : Source 2) :
    planeCoordinateMapOf h ζ (planeChartOf h ζ hc y) = y := by
  change (planeCoordinateMapOf h ζ).toLinearMap
    ((LinearEquiv.ofInjectiveEndo (planeCoordinateMapOf h ζ).toLinearMap
      (planeCoordinateMapOf_injective hc)).symm y) = y
  exact (LinearEquiv.ofInjectiveEndo (planeCoordinateMapOf h ζ).toLinearMap
    (planeCoordinateMapOf_injective hc)).apply_symm_apply y

theorem fibreCoord_planeChartOf {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) (y : Source 2) :
    ζ (hyperplaneInclusion 2 (planeChartOf h ζ hc y)) = y 0 := by
  rw [← planeCoordinateMapOf_apply_zero h ζ, planeCoordinateMapOf_planeChartOf]

theorem baseCoord_planeChartOf {h ζ : Source 3 →L[ℂ] ℂ}
    (hc : Injective fun y : Source 3 => (y 0, h y, ζ y)) (y : Source 2) :
    h (hyperplaneInclusion 2 (planeChartOf h ζ hc y)) = y 1 := by
  rw [← planeCoordinateMapOf_apply_one h ζ, planeCoordinateMapOf_planeChartOf]

namespace LevelProjectionSetup

variable {A : ResolutionSectionAssembly g hd hi} {L : ResolutionSectionLevel A}
  (P : LevelProjectionSetup A L)

/-- The linear coordinates of the target plane `{z₀ = 0}` given by `(ζ, h)`: the point
`P.planeChart y` of the plane has `ζ`-coordinate `y 0` and `h`-coordinate `y 1`. -/
def planeChart : Source 2 ≃L[ℂ] Source 2 := planeChartOf P.baseCoord P.fibreCoord P.coordinates

theorem fibreCoord_planeChart (y : Source 2) :
    P.fibreCoord (hyperplaneInclusion 2 (P.planeChart y)) = y 0 :=
  fibreCoord_planeChartOf P.coordinates y

theorem baseCoord_planeChart (y : Source 2) :
    P.baseCoord (hyperplaneInclusion 2 (P.planeChart y)) = y 1 :=
  baseCoord_planeChartOf P.coordinates y

/-- The fibre of the level over the base value `c`. -/
def levelFibre (c : ℂ) : Set (Source 2) :=
  {x | x ∈ ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter ∧ P.baseCoord (A.H x) = c}

theorem roots_eq_image_levelFibre (c : ℂ) :
    P.roots c = (fun x => P.fibreCoord (A.H x)) '' P.levelFibre c := rfl

/-- On the level, a point is determined by its base and fibre coordinates. -/
theorem injOn_level :
    InjOn (fun x => (P.baseCoord (A.H x), P.fibreCoord (A.H x)))
      {x | x ∈ ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter} := by
  intro x hx y hy hxy
  simp only [Prod.mk.injEq] at hxy
  apply L.injective hx.1 hy.1
  apply P.coordinates
  simp only [hx.2, hy.2, hxy.1, hxy.2]

/-- **The properties of the constructed setup** used by the outer braid (B) and the local
critical data (C). -/
structure SetupProperties where
  /-- The hypotheses of the outer braid. -/
  outer : P.OuterAdmissible
  /-- The part of the level over the closed disc `B̄(0, ρ)` is compact (and it lies in the open
  ball `B_R` by definition). -/
  compact : IsCompact {x | x ∈ ball (0 : Source 2) L.radius ∧ A.H x 0 = L.parameter ∧
    P.baseCoord (A.H x) ∈ closedBall (0 : ℂ) P.radius}
  /-- `V` is the set of critical values of `h ∘ H` on the level over `B(0, ρ)`. -/
  critical_iff : ∀ c : ℂ, c ∈ P.critical ↔ c ∈ ball (0 : ℂ) P.radius ∧
    ∃ x ∈ P.levelFibre c, ¬ Injective (fderiv ℂ (levelBaseMap A P.baseCoord) x)
  /-- The fibres over `B(0, ρ)` are finite. -/
  fibre_finite : ∀ c ∈ ball (0 : ℂ) P.radius, (P.levelFibre c).Finite
  /-- The base values of the singular points are critical values. -/
  point_critical : ∀ j : Fin L.points.card, P.baseCoord (A.H (L.point j)) ∈ P.critical
  /-- On every critical fibre the real part of `ζ` is injective. -/
  critical_re_injOn : ∀ c ∈ P.critical,
    InjOn (fun x => (P.fibreCoord (A.H x)).re) (P.levelFibre c)
  /-- At every singular point, the local image equation in the coordinates `(ζ, h)` is regular
  in the coordinate `ζ` of order its multiplicity. -/
  point_transverse : ∀ (j : Fin L.points.card) (a : ℕ),
    localSectionEquation A.H (L.point j) ∈ maximalIdeal 2 ^ a →
    localSectionEquation A.H (L.point j) ∉ maximalIdeal 2 ^ (a + 1) →
    IsRegularInFirstCoordinateOfOrder
      ((pointedEquivGermOfContinuousLinearEquiv P.planeChart).forward.pullbackRingHom
        (localSectionEquation A.H (L.point j))) a

end LevelProjectionSetup

/-- **The constructed setups**: every assembly has a level and a setup with the exported
properties, for which the fields (A) and (D) hold. -/
def LevelSetupStatement : Prop :=
  ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0) (hi : g.HasInjectiveRepresentative)
    (A : ResolutionSectionAssembly g hd hi),
    ∃ (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L),
      Nonempty P.SetupProperties ∧ P.RootFamilyHolds ∧ P.ConnectedHolds

/-- The constructed setups, the outer braid for admissible setups and the critical data for
setups with the exported properties give the split projection data. -/
theorem levelProjectionSetupStatement_of_levelSetup (hS : LevelSetupStatement)
    (hB : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi)
      (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L),
      P.OuterAdmissible → P.OuterHolds)
    (hC : ∀ (g : PointedMapGerm 2 3) (hd : g.differential = 0)
      (hi : g.HasInjectiveRepresentative) (A : ResolutionSectionAssembly g hd hi)
      (L : ResolutionSectionLevel A) (P : LevelProjectionSetup A L),
      P.SetupProperties → P.CriticalHolds) :
    LevelProjectionSetupStatement := by
  intro g hd hi
  obtain ⟨A⟩ := g.exists_resolutionSectionAssembly hd hi
  obtain ⟨L, P, ⟨hP⟩, h₁, h₄⟩ := hS g hd hi A
  exact ⟨A, L, P, h₁, hB g hd hi A L P hP.outer, hC g hd hi A L P hP, h₄⟩

end OnLeConjecture.Analytic
