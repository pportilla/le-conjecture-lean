/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.NestedMonicFinite
public import OnLeConjecture.Analytic.CyclicCoverAveraging
public import OnLeConjecture.Analytic.PullbackEquivalence

/-!
# Analytic descent through the cyclic cover

The cover is `(u,v) ↦ (u^r,v^r,uv)`. Its cyclic action multiplies the two
source coordinates by a primitive `r`th root and its inverse. Analytic
Weierstrass division supplies a finite residue decomposition over
`(u^r,v^r)`. Finite cyclic averaging leaves its diagonal residues, which
are analytic functions of the three cover coordinates.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic.CyclicCover

/-- Simultaneous power substitution in the two source coordinates. -/
@[expose] noncomputable def powerPairFunction (r : ℕ) (z : Source 2) : Source 2 :=
  fun i => z i ^ r

theorem powerPairFunction_analyticAt (r : ℕ) :
    AnalyticAt ℂ (powerPairFunction r) 0 := by
  apply AnalyticAt.pi
  intro i
  exact ((ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 2 => ℂ) i).analyticAt 0).pow r

theorem powerPairFunction_zero (r : ℕ) (hr : 0 < r) :
    powerPairFunction r (0 : Source 2) = 0 := by
  funext i
  simp [powerPairFunction, zero_pow hr.ne']

/-- The pointed analytic power substitution. -/
@[expose] noncomputable def powerPairGerm (r : ℕ) (hr : 0 < r) :
    PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (powerPairFunction r)
    (powerPairFunction_analyticAt r) (powerPairFunction_zero r hr)

/-- Every analytic germ has a finite residue decomposition with analytic
coefficients in the two powered coordinates. -/
theorem exists_power_residue_decomposition (r : ℕ) (hr : 0 < r) (f : Germ 2) :
    ∃ a : Fin r × Fin r → Germ 2,
      f = ∑ k, (powerPairGerm r hr).pullbackRingHom (a k) *
        Germ.coordinate (0 : Fin 2) ^ k.1.1 *
        Germ.coordinate (1 : Fin 2) ^ k.2.1 := by
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  let A := Germ.monicTriangularParameterCoefficients (r - 1)
    (fun _ _ => (0 : ℂ))
  have hA : AnalyticAt ℂ A (0, 0) :=
    Germ.analyticAt_monicTriangularParameterCoefficients (r - 1)
      (fun _ _ => 0) (fun _ => analyticAt_const)
  have hAzero : A (0, 0) = 0 :=
    Germ.monicTriangularParameterCoefficients_zero (r - 1)
      (fun _ _ => 0) (fun _ => rfl)
  have hpolynomial (x y t : ℂ) :
      Germ.generalDivisionPolynomialValue x (A (y, t)) = x ^ r - t := by
    rw [Germ.generalDivisionPolynomialValue_monicTriangularParameterCoefficients]
    simp [Germ.monicTriangularPolynomialFunction, hpred]
  have hfirst : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 0)
        (A (z 1, powerPairFunction r z 0)) = 0 := by
    exact Filter.Eventually.of_forall fun z => by
      rw [hpolynomial]
      simp [powerPairFunction]
  have hsecond : ∀ᶠ z : Source 2 in nhds 0,
      Germ.generalDivisionPolynomialValue (z 1)
        (A (powerPairFunction r z 0, powerPairFunction r z 1)) = 0 := by
    exact Filter.Eventually.of_forall fun z => by
      rw [hpolynomial]
      simp [powerPairFunction]
  obtain ⟨c, hc⟩ : ∃ c : Fin r × Fin r → (powerPairGerm r hr).ImageRing,
      f = ∑ k, (c k : Germ 2) * Germ.coordinate (0 : Fin 2) ^ k.1.1 *
        Germ.coordinate (1 : Fin 2) ^ k.2.1 := by
    have hdecomposition := PointedMapGerm.exists_nestedMonic_image_decomposition
        (powerPairFunction r) (powerPairFunction_analyticAt r)
        (powerPairFunction_zero r hr) (r - 1) (r - 1)
        A A hA hAzero hA hAzero hfirst hsecond f
    dsimp only at hdecomposition
    rw [hpred] at hdecomposition
    exact hdecomposition
  choose a ha using fun k => (powerPairGerm r hr).pullbackToImageRing_surjective (c k)
  refine ⟨a, ?_⟩
  rw [hc]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [← ha k]
  rfl

/-- The two coordinate scalars of the cyclic action. -/
@[expose] noncomputable def actionScalar (ζ : ℂ) : Fin 2 → ℂ := ![ζ, ζ⁻¹]

/-- The cyclic action on the source coordinates. -/
@[expose] noncomputable def actionFunction (ζ : ℂ) (z : Source 2) : Source 2 :=
  fun i => actionScalar ζ i * z i

theorem actionFunction_analyticAt (ζ : ℂ) : AnalyticAt ℂ (actionFunction ζ) 0 := by
  apply AnalyticAt.pi
  intro i
  exact analyticAt_const.mul
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i).analyticAt 0)

theorem actionFunction_zero (ζ : ℂ) : actionFunction ζ (0 : Source 2) = 0 := by
  funext i
  simp [actionFunction]

/-- The analytic germ of the cyclic action. -/
@[expose] noncomputable def actionGerm (ζ : ℂ) : PointedMapGerm 2 2 :=
  PointedMapGerm.ofFunction (actionFunction ζ)
    (actionFunction_analyticAt ζ) (actionFunction_zero ζ)

/-- Pullback by the cyclic action as a complex algebra homomorphism. -/
@[expose] noncomputable def actionAlgHom (ζ : ℂ) : Germ 2 →ₐ[ℂ] Germ 2 where
  toRingHom := (actionGerm ζ).pullbackRingHom
  commutes' c := (actionGerm ζ).pullback_constRingHom c

@[simp]
theorem actionAlgHom_coordinate (ζ : ℂ) (i : Fin 2) :
    actionAlgHom ζ (Germ.coordinate i) =
      Germ.constRingHom 2 (actionScalar ζ i) * Germ.coordinate i := by
  change (actionGerm ζ).pullbackRingHom (Germ.coordinate i) = _
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [show (actionGerm ζ).1 = MapGerm.ofFunction (actionFunction ζ)
    (actionFunction_analyticAt ζ) from rfl, MapGerm.component_ofFunction]
  rfl

/-- The two powered coordinates are invariant under the cyclic action. -/
theorem powerPair_comp_action (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : ζ ^ r = 1) :
    (powerPairGerm r hr).comp (actionGerm ζ) = powerPairGerm r hr := by
  simp only [powerPairGerm, actionGerm, PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  change (actionScalar ζ i * z i) ^ r = z i ^ r
  rw [mul_pow]
  have hscalar : actionScalar ζ i ^ r = 1 := by
    fin_cases i
    · simpa [actionScalar] using hζ
    · simp [actionScalar, inv_pow, hζ]
  rw [hscalar, one_mul]

/-- Every analytic coefficient in the powered coordinates is invariant.
-/
theorem actionAlgHom_powerPair_pullback (r : ℕ) (hr : 0 < r) (ζ : ℂ)
    (hζ : ζ ^ r = 1) (a : Germ 2) :
    actionAlgHom ζ ((powerPairGerm r hr).pullbackRingHom a) =
      (powerPairGerm r hr).pullbackRingHom a := by
  change ((actionGerm ζ).pullbackRingHom.comp
    (powerPairGerm r hr).pullbackRingHom) a = _
  rw [← PointedMapGerm.pullbackRingHom_comp, powerPair_comp_action r hr ζ hζ]

/-- Invariance leaves a finite sum of diagonal residues with analytic
coefficients in the two powered coordinates. -/
theorem exists_diagonal_power_residue_decomposition
    (r : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (f : Germ 2) (hinvariant : (actionGerm ζ).pullbackRingHom f = f) :
    ∃ a : Fin r → Germ 2,
      f = ∑ i, (powerPairGerm r hr).pullbackRingHom (a i) *
        (Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2)) ^ i.1 := by
  classical
  obtain ⟨a, ha⟩ := exists_power_residue_decomposition r hr f
  let q : Fin r → Fin r → Germ 2 := fun i j =>
    (powerPairGerm r hr).pullbackRingHom (a (i, j)) *
      Germ.coordinate (0 : Fin 2) ^ i.1 *
      Germ.coordinate (1 : Fin 2) ^ j.1
  have hdecomposition : f = ∑ i, ∑ j, q i j := by
    simpa only [Fintype.sum_prod_type, q] using ha
  have hcharacter (i j : Fin r) :
      (actionAlgHom ζ).toLinearMap (q i j) = (ζ ^ i.1 / ζ ^ j.1) • q i j := by
    change actionAlgHom ζ
      ((powerPairGerm r hr).pullbackRingHom (a (i, j)) *
        Germ.coordinate (0 : Fin 2) ^ i.1 *
        Germ.coordinate (1 : Fin 2) ^ j.1) = _
    rw [map_mul, map_mul, map_pow, map_pow,
      actionAlgHom_powerPair_pullback r hr ζ hζ.pow_eq_one,
      actionAlgHom_coordinate, actionAlgHom_coordinate]
    simp only [actionScalar, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def]
    change (powerPairGerm r hr).pullbackRingHom (a (i, j)) *
        (Germ.constRingHom 2 ζ * Germ.coordinate 0) ^ i.1 *
        (Germ.constRingHom 2 ζ⁻¹ * Germ.coordinate 1) ^ j.1 =
      Germ.constRingHom 2 (ζ ^ i.1 / ζ ^ j.1) *
        ((powerPairGerm r hr).pullbackRingHom (a (i, j)) *
          Germ.coordinate 0 ^ i.1 * Germ.coordinate 1 ^ j.1)
    rw [div_eq_mul_inv, ← inv_pow, map_mul, map_pow, map_pow, mul_pow, mul_pow]
    ring
  have hdiagonal := invariant_sum_eq_diagonal r hr ζ hζ
    (actionAlgHom ζ).toLinearMap q f hdecomposition hcharacter hinvariant
  refine ⟨fun i => a (i, i), hdiagonal.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _hi
  dsimp only [q]
  rw [mul_pow]
  ring

/-- The three coordinates of the cyclic cover. -/
@[expose] noncomputable def coverFunction (r : ℕ) (z : Source 2) : Source 3 :=
  ![z 0 ^ r, z 1 ^ r, z 0 * z 1]

theorem coverFunction_analyticAt (r : ℕ) : AnalyticAt ℂ (coverFunction r) 0 := by
  have hfirst := (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 2 => ℂ) (0 : Fin 2)).analyticAt (0 : Source 2)
  have hsecond := (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : Fin 2 => ℂ) (1 : Fin 2)).analyticAt (0 : Source 2)
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hfirst.pow r
  · exact hsecond.pow r
  · exact hfirst.mul hsecond

theorem coverFunction_zero (r : ℕ) (hr : 0 < r) :
    coverFunction r (0 : Source 2) = 0 := by
  funext i
  fin_cases i <;> simp [coverFunction, zero_pow hr.ne']

/-- The pointed analytic germ `(u,v) ↦ (u^r,v^r,uv)`. -/
@[expose] noncomputable def coverGerm (r : ℕ) (hr : 0 < r) : PointedMapGerm 2 3 :=
  PointedMapGerm.ofFunction (coverFunction r)
    (coverFunction_analyticAt r) (coverFunction_zero r hr)

/-- Projection from the three cover coordinates to the first two. -/
@[expose] noncomputable def projectionFunction (z : Source 3) : Source 2 :=
  ![z 0, z 1]

theorem projectionFunction_analyticAt : AnalyticAt ℂ projectionFunction 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 3 => ℂ) (0 : Fin 3)).analyticAt 0
  · exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Fin 3 => ℂ) (1 : Fin 3)).analyticAt 0

theorem projectionFunction_zero : projectionFunction (0 : Source 3) = 0 := by
  funext i
  fin_cases i <;> rfl

/-- The pointed projection to the first two target coordinates. -/
@[expose] noncomputable def projectionGerm : PointedMapGerm 3 2 :=
  PointedMapGerm.ofFunction projectionFunction projectionFunction_analyticAt
    projectionFunction_zero

theorem projection_comp_cover (r : ℕ) (hr : 0 < r) :
    projectionGerm.comp (coverGerm r hr) = powerPairGerm r hr := by
  simp only [projectionGerm, coverGerm, powerPairGerm,
    PointedMapGerm.comp_ofFunction]
  apply Subtype.ext
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  apply Filter.Eventually.of_forall
  intro z
  funext i
  fin_cases i <;> rfl

@[simp]
theorem coverGerm_pullback_last (r : ℕ) (hr : 0 < r) :
    (coverGerm r hr).pullbackRingHom (Germ.coordinate (2 : Fin 3)) =
      Germ.coordinate (0 : Fin 2) * Germ.coordinate (1 : Fin 2) := by
  rw [PointedMapGerm.pullback_coordinate]
  apply Subtype.ext
  rw [show (coverGerm r hr).1 = MapGerm.ofFunction (coverFunction r)
    (coverFunction_analyticAt r) from rfl, MapGerm.component_ofFunction]
  rfl

theorem coverGerm_pullback_projection (r : ℕ) (hr : 0 < r) (a : Germ 2) :
    (coverGerm r hr).pullbackRingHom (projectionGerm.pullbackRingHom a) =
      (powerPairGerm r hr).pullbackRingHom a := by
  change ((coverGerm r hr).pullbackRingHom.comp projectionGerm.pullbackRingHom) a = _
  rw [← PointedMapGerm.pullbackRingHom_comp, projection_comp_cover]

/-- Every analytic germ invariant under the primitive cyclic action is
the pullback of an actual analytic germ in the three cover coordinates. -/
theorem exists_analytic_descent
    (r : ℕ) (hr : 0 < r) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ r)
    (f : Germ 2) (hinvariant : (actionGerm ζ).pullbackRingHom f = f) :
    ∃ Φ : Germ 3, f = (coverGerm r hr).pullbackRingHom Φ := by
  obtain ⟨a, ha⟩ := exists_diagonal_power_residue_decomposition r hr ζ hζ f hinvariant
  let Φ : Germ 3 := ∑ i : Fin r, projectionGerm.pullbackRingHom (a i) *
    Germ.coordinate (2 : Fin 3) ^ i.1
  refine ⟨Φ, ?_⟩
  rw [ha]
  simp only [Φ, map_sum, map_mul, map_pow,
    coverGerm_pullback_last, coverGerm_pullback_projection]

end OnLeConjecture.Analytic.CyclicCover
