/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.FiniteParametricMorse
public import OnLeConjecture.Analytic.MonicTriangularFinite
public import OnLeConjecture.Analytic.CoordinatePermutation

/-!
# Specialization of a parametric quadratic crossing

Coordinates are ordered as `(Y, tau, x)`, with `Y` distinguished in the
Morse lemma. Specialization sets `tau = 0` and retains `(Y,x)`.
-/

public section

open Filter
open scoped BigOperators Topology

namespace OnLeConjecture.Analytic.QuadraticCrossing

open OnLeConjecture.Analytic.Germ

@[expose] def specialFunction (z : Source 2) : Source 3 := ![z 0, 0, z 1]

theorem specialFunction_analyticAt : AnalyticAt ℂ specialFunction 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0

@[expose] noncomputable def specialGerm : PointedMapGerm 2 3 :=
  PointedMapGerm.ofFunction specialFunction specialFunction_analyticAt (by
    ext i
    fin_cases i <;> rfl)

@[simp] theorem specialGerm_component (i : Fin 3) :
    specialGerm.1.component i = ![coordinate 0, 0, coordinate 1] i := by
  fin_cases i <;> apply Subtype.ext <;>
    change ((MapGerm.ofFunction specialFunction specialFunction_analyticAt).component _).1 = _
  all_goals rw [MapGerm.component_ofFunction]
  all_goals rfl

@[simp] theorem specialGerm_pullback_coordinate (i : Fin 3) :
    specialGerm.pullbackRingHom (coordinate i) = ![coordinate 0, 0, coordinate 1] i := by
  rw [PointedMapGerm.pullback_coordinate, specialGerm_component]

theorem specialGerm_pullback_hyperplaneExtension (h : Germ 2) :
    specialGerm.pullbackRingHom (hyperplaneExtension 2 h) =
      hyperplaneExtension 1 (hyperplaneRestriction 1 h) := by
  obtain ⟨H, hH, hh⟩ := exists_analyticRepresentative_allOrders h
  rw [hh, hyperplaneExtension_ofFunction, hyperplaneRestriction_ofFunction,
    hyperplaneExtension_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    change H (hyperplaneTail 2 (specialFunction z)) = H (hyperplaneInclusion 1 (hyperplaneTail 1 z))
    apply congrArg H
    ext i
    fin_cases i <;> rfl

theorem specialGerm_pullback_partialDerivative (f : Germ 3) :
    specialGerm.pullbackRingHom (partialDerivative 0 f) =
      partialDerivative 0 (specialGerm.pullbackRingHom f) := by
  change compPointed (partialDerivative 0 f) specialGerm =
    partialDerivative 0 (compPointed f specialGerm)
  rw [partialDerivative_compPointed_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp [specialGerm_component]

/-- A tail-fixing Morse change sends the special crossing to the same
crossing. Its first coordinate on the special fibre is either `Y` or `-Y`. -/
theorem morse_specialization_eq_or_eq_neg
    (g A : Germ 3) (e : PointedEquivGerm 3) (h : Germ 2)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A)
    (hnormal : e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension 2 h)
    (hfix : ∀ q : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 q) =
      hyperplaneExtension 2 q) :
    hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2) ∧
      (specialGerm.pullbackRingHom (e.forward.1.component 0) = coordinate 0 ∨
        specialGerm.pullbackRingHom (e.forward.1.component 0) = -coordinate 0) := by
  have htail := equiv_fixes_tail_of_fixes_hyperplaneExtension e hfix
  have heone : e.pullbackAlgEquiv (coordinate 1) = coordinate 1 := by
    exact htail 0
  have hetwo : e.pullbackAlgEquiv (coordinate 2) = coordinate 2 := by
    exact htail 1
  have hezero : e.pullbackAlgEquiv (coordinate 0) = e.forward.1.component 0 :=
    e.forward.pullback_coordinate 0
  let T : Germ 2 := specialGerm.pullbackRingHom (e.forward.1.component 0)
  have hequation : T ^ 2 - coordinate 1 ^ 2 =
      coordinate 0 ^ 2 + hyperplaneExtension 1 (hyperplaneRestriction 1 h) := by
    have heq := congrArg specialGerm.pullbackRingHom hnormal
    rw [hg, map_add, map_sub, map_pow, map_pow, map_mul, heone, hetwo, hezero,
      map_add, map_sub, map_pow, map_pow, map_mul, map_add, map_pow,
      specialGerm_pullback_hyperplaneExtension] at heq
    rw [specialGerm_pullback_coordinate 0, specialGerm_pullback_coordinate 1,
      specialGerm_pullback_coordinate 2] at heq
    change T ^ 2 - coordinate 1 ^ 2 + 0 * _ =
      coordinate 0 ^ 2 + hyperplaneExtension 1 (hyperplaneRestriction 1 h) at heq
    simpa only [zero_mul, add_zero] using heq
  have hTunit : IsUnit (partialDerivative 0 T) := by
    rw [← specialGerm_pullback_partialDerivative]
    exact (first_partialDerivative_isUnit_of_equiv_fixes_tail e htail).map
      specialGerm.pullbackRingHom
  have hderivative : 2 * T * partialDerivative 0 T = 2 * coordinate 0 := by
    have heq := congrArg (partialDerivative (0 : Fin 2)) hequation
    simp only [partialDerivative_sub, partialDerivative_add, partialDerivative_pow,
      partialDerivative_coordinate_same,
      partialDerivative_coordinate_ne (by decide : (0 : Fin 2) ≠ 1),
      partialDerivative_zero_hyperplaneExtension, Nat.reduceSub, pow_one,
      smul_zero, sub_zero, add_zero, nsmul_eq_mul] at heq
    simpa [smul_eq_mul, mul_assoc] using heq
  have hTzero : hyperplaneRestriction 1 T = 0 := by
    have hrestricted := congrArg (hyperplaneRestriction 1) hderivative
    simp only [map_mul, map_ofNat, hyperplaneRestriction_coordinate_zero, mul_zero] at hrestricted
    have hunit := hTunit.map (hyperplaneRestriction 1)
    have hprod : 2 * hyperplaneRestriction 1 T = 0 :=
      (mul_eq_zero.mp hrestricted).resolve_right hunit.ne_zero
    exact (mul_eq_zero.mp hprod).resolve_left (by
      intro htwo
      have hv := congrArg (valueRingHom 1) htwo
      rw [map_ofNat, map_zero] at hv
      exact two_ne_zero hv)
  have hh : hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2) := by
    have hrestricted := congrArg (hyperplaneRestriction 1) hequation
    simp only [map_sub, map_pow, map_add, hTzero,
      hyperplaneRestriction_coordinate_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      zero_sub, zero_add] at hrestricted
    have hxtail : hyperplaneRestriction 1 (coordinate (1 : Fin 2)) = coordinate 0 := by
      exact hyperplaneRestriction_coordinate_succ 1 (0 : Fin 1)
    have hext : hyperplaneRestriction 1
        (hyperplaneExtension 1 (hyperplaneRestriction 1 h)) = hyperplaneRestriction 1 h :=
      DFunLike.congr_fun (hyperplaneRestriction_comp_extension 1) _
    rw [hxtail, hext] at hrestricted
    exact hrestricted.symm
  refine ⟨hh, ?_⟩
  have hsquare : T ^ 2 = coordinate 0 ^ 2 := by
    rw [hh, map_neg, map_pow, hyperplaneExtension_coordinate] at hequation
    change T ^ 2 - coordinate 1 ^ 2 = coordinate 0 ^ 2 + -(coordinate 1 ^ 2) at hequation
    linear_combination hequation
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsquare

@[expose] def lineFunction (s : ℂ) (z : Source 1) : Source 2 := ![s * z 0, z 0]

theorem lineFunction_analyticAt (s : ℂ) : AnalyticAt ℂ (lineFunction s) 0 := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0)
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0

@[expose] noncomputable def lineGerm (s : ℂ) : PointedMapGerm 1 2 :=
  PointedMapGerm.ofFunction (lineFunction s) (lineFunction_analyticAt s) (by
    ext i
    fin_cases i <;> simp [lineFunction])

@[simp] theorem lineGerm_component (s : ℂ) (i : Fin 2) :
    (lineGerm s).1.component i = ![constRingHom 1 s * coordinate 0, coordinate 0] i := by
  fin_cases i <;> apply Subtype.ext <;>
    change ((MapGerm.ofFunction (lineFunction s) (lineFunction_analyticAt s)).component _).1 = _
  all_goals rw [MapGerm.component_ofFunction]
  all_goals rfl

@[simp] theorem lineGerm_pullback_coordinate (s : ℂ) (i : Fin 2) :
    (lineGerm s).pullbackRingHom (coordinate i) =
      ![constRingHom 1 s * coordinate 0, coordinate 0] i := by
  rw [PointedMapGerm.pullback_coordinate, lineGerm_component]

/-- The line `(Y,tau,x) = (s*x,0,x)` as a pointed analytic germ. -/
@[expose] noncomputable def branchGerm (s : ℂ) : PointedMapGerm 1 3 :=
  specialGerm.comp (lineGerm s)

@[simp] theorem branchGerm_component (s : ℂ) (i : Fin 3) :
    (branchGerm s).1.component i = ![constRingHom 1 s * coordinate 0, 0, coordinate 0] i := by
  rw [branchGerm, PointedMapGerm.component_comp_general, specialGerm_component]
  fin_cases i
  · exact lineGerm_pullback_coordinate s 0
  · exact map_zero _
  · exact lineGerm_pullback_coordinate s 1

/-- The sign of the first coordinate on the special fibre determines the
map induced on both crossing branches. -/
theorem equiv_comp_branchGerm
    (e : PointedEquivGerm 3) (epsilon s : ℂ)
    (hT : specialGerm.pullbackRingHom (e.forward.1.component 0) =
      constRingHom 2 epsilon * coordinate 0)
    (hfix : ∀ q : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 q) =
      hyperplaneExtension 2 q) :
    e.forward.comp (branchGerm s) = branchGerm (epsilon * s) := by
  have htail := equiv_fixes_tail_of_fixes_hyperplaneExtension e hfix
  apply PointedMapGerm.ext_components
  intro i
  fin_cases i
  · change (e.forward.comp (branchGerm s)).1.component 0 = _
    rw [PointedMapGerm.component_comp_general, branchGerm_component]
    change (branchGerm s).pullbackRingHom (e.forward.1.component 0) =
        constRingHom 1 (epsilon * s) * coordinate 0
    rw [branchGerm, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply]
    rw [hT, map_mul, PointedMapGerm.pullback_constRingHom, lineGerm_pullback_coordinate,
      Matrix.cons_val_zero, map_mul, mul_assoc]
  · change (e.forward.comp (branchGerm s)).1.component 1 = (branchGerm (epsilon * s)).1.component 1
    rw [PointedMapGerm.component_comp_general]
    have htail0 : e.forward.1.component 1 = coordinate 1 := htail 0
    rw [htail0, PointedMapGerm.pullback_coordinate, branchGerm_component, branchGerm_component]
    rfl
  · change (e.forward.comp (branchGerm s)).1.component 2 = (branchGerm (epsilon * s)).1.component 2
    rw [PointedMapGerm.component_comp_general]
    have htail1 : e.forward.1.component 2 = coordinate 2 := htail 1
    rw [htail1, PointedMapGerm.pullback_coordinate, branchGerm_component, branchGerm_component]
    rfl

theorem branchGerm_pullback_equiv
    (e : PointedEquivGerm 3) (epsilon s : ℂ) (f : Germ 3)
    (hT : specialGerm.pullbackRingHom (e.forward.1.component 0) =
      constRingHom 2 epsilon * coordinate 0)
    (hfix : ∀ q : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 q) =
      hyperplaneExtension 2 q) :
    (branchGerm s).pullbackRingHom (e.pullbackAlgEquiv f) =
      (branchGerm (epsilon * s)).pullbackRingHom f := by
  have heq := congrArg (fun p : PointedMapGerm 1 3 ↦ p.pullbackRingHom f)
    (equiv_comp_branchGerm e epsilon s hT hfix)
  rw [PointedMapGerm.pullbackRingHom_comp] at heq
  exact heq

/-- Neither original branch restriction becomes zero under the Morse
change. The two branches can only be fixed or exchanged. -/
theorem morse_branch_restrictions_ne_zero
    (g A f : Germ 3) (e : PointedEquivGerm 3) (h : Germ 2)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A)
    (hnormal : e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension 2 h)
    (hfix : ∀ q : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 q) =
      hyperplaneExtension 2 q)
    (hplus : (branchGerm 1).pullbackRingHom f ≠ 0)
    (hminus : (branchGerm (-1)).pullbackRingHom f ≠ 0) :
    (branchGerm 1).pullbackRingHom (e.pullbackAlgEquiv f) ≠ 0 ∧
      (branchGerm (-1)).pullbackRingHom (e.pullbackAlgEquiv f) ≠ 0 := by
  obtain ⟨_, hT | hT⟩ := morse_specialization_eq_or_eq_neg g A e h hg hnormal hfix
  · have hT' : specialGerm.pullbackRingHom (e.forward.1.component 0) =
        constRingHom 2 1 * coordinate 0 := by simpa using hT
    simpa only [branchGerm_pullback_equiv e 1 _ f hT' hfix, one_mul] using
      And.intro hplus hminus
  · have hT' : specialGerm.pullbackRingHom (e.forward.1.component 0) =
        constRingHom 2 (-1) * coordinate 0 := by simpa using hT
    constructor
    · rw [branchGerm_pullback_equiv e (-1) 1 f hT' hfix, mul_one]
      exact hminus
    · rw [branchGerm_pullback_equiv e (-1) (-1) f hT' hfix]
      simpa using hplus

theorem lineGerm_pullback_hyperplaneExtension (s : ℂ) (h : Germ 1) :
    (lineGerm s).pullbackRingHom (hyperplaneExtension 1 h) = h := by
  obtain ⟨H, hH, hh⟩ := exists_analyticRepresentative_allOrders h
  rw [hh, hyperplaneExtension_ofFunction]
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    change H (hyperplaneTail 1 (lineFunction s z)) = H z
    apply congrArg H
    ext i
    fin_cases i
    rfl

theorem branchGerm_pullback_hyperplaneExtension (s : ℂ) (h : Germ 2) :
    (branchGerm s).pullbackRingHom (hyperplaneExtension 2 h) = hyperplaneRestriction 1 h := by
  rw [branchGerm, PointedMapGerm.pullbackRingHom_comp, RingHom.comp_apply,
    specialGerm_pullback_hyperplaneExtension, lineGerm_pullback_hyperplaneExtension]

@[simp] theorem branchGerm_pullback_coordinate (s : ℂ) (i : Fin 3) :
    (branchGerm s).pullbackRingHom (coordinate i) =
      ![constRingHom 1 s * coordinate 0, 0, coordinate 0] i := by
  rw [PointedMapGerm.pullback_coordinate, branchGerm_component]

/-- The prepared linear remainder has nonzero restrictions to both
quadratic branches, as a consequence of the original restrictions. -/
theorem morse_linear_remainder_branches_ne_zero
    (g A f : Germ 3) (e : PointedEquivGerm 3) (h a b : Germ 2) (q : Germ 3)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A)
    (hnormal : e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension 2 h)
    (hdivision : e.pullbackAlgEquiv f = (coordinate 0 ^ 2 + hyperplaneExtension 2 h) * q +
      hyperplaneExtension 2 a + coordinate 0 * hyperplaneExtension 2 b)
    (hfix : ∀ r : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 r) =
      hyperplaneExtension 2 r)
    (hplus : (branchGerm 1).pullbackRingHom f ≠ 0)
    (hminus : (branchGerm (-1)).pullbackRingHom f ≠ 0) :
    hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2) ∧
      hyperplaneRestriction 1 a + coordinate 0 * hyperplaneRestriction 1 b ≠ 0 ∧
      hyperplaneRestriction 1 a - coordinate 0 * hyperplaneRestriction 1 b ≠ 0 := by
  have hh := (morse_specialization_eq_or_eq_neg g A e h hg hnormal hfix).1
  obtain ⟨hplus', hminus'⟩ := morse_branch_restrictions_ne_zero
    g A f e h hg hnormal hfix hplus hminus
  have hvalue (s : ℂ) : (branchGerm s).pullbackRingHom (e.pullbackAlgEquiv f) =
      ((constRingHom 1 s * coordinate 0) ^ 2 - coordinate 0 ^ 2) *
          (branchGerm s).pullbackRingHom q +
        hyperplaneRestriction 1 a +
          constRingHom 1 s * coordinate 0 * hyperplaneRestriction 1 b := by
    rw [hdivision, map_add, map_add, map_mul, map_add, map_pow, map_mul,
      branchGerm_pullback_coordinate, branchGerm_pullback_hyperplaneExtension,
      branchGerm_pullback_hyperplaneExtension, branchGerm_pullback_hyperplaneExtension, hh]
    rfl
  refine ⟨hh, ?_, ?_⟩
  · rw [hvalue] at hplus'
    simpa using hplus'
  · rw [hvalue] at hminus'
    simpa [sub_eq_add_neg] using hminus'

/-- The quadratic preparation and both nonzero remainder restrictions are
constructed from the original crossing equation and branch data. -/
theorem exists_crossing_morse_pair_preparation
    (g A f : Germ 3)
    (hg : g = coordinate 0 ^ 2 - coordinate 2 ^ 2 + coordinate 1 * A)
    (hf : f ∈ maximalIdeal 3)
    (hplus : (branchGerm 1).pullbackRingHom f ≠ 0)
    (hminus : (branchGerm (-1)).pullbackRingHom f ≠ 0) :
    ∃ e : PointedEquivGerm 3, ∃ h a b : Germ 2, ∃ q : Germ 3,
      e.pullbackAlgEquiv g = coordinate 0 ^ 2 + hyperplaneExtension 2 h ∧
      e.pullbackAlgEquiv f = (coordinate 0 ^ 2 + hyperplaneExtension 2 h) * q +
        hyperplaneExtension 2 a + coordinate 0 * hyperplaneExtension 2 b ∧
      (∀ r : Germ 2, e.pullbackAlgEquiv (hyperplaneExtension 2 r) = hyperplaneExtension 2 r) ∧
      h ∈ maximalIdeal 2 ∧ a ∈ maximalIdeal 2 ∧
      hyperplaneRestriction 1 h = -(coordinate (0 : Fin 1) ^ 2) ∧
      hyperplaneRestriction 1 a + coordinate 0 * hyperplaneRestriction 1 b ≠ 0 ∧
      hyperplaneRestriction 1 a - coordinate 0 * hyperplaneRestriction 1 b ≠ 0 := by
  have hgmax : g ∈ maximalIdeal 3 := by
    rw [mem_maximalIdeal_iff, hg]
    simp
  have hderivative : partialDerivative 0 g =
      (2 : Germ 3) * coordinate 0 + coordinate 1 * partialDerivative 0 A := by
    rw [hg, partialDerivative_add, partialDerivative_sub, partialDerivative_pow,
      partialDerivative_pow, partialDerivative_mul]
    simp [smul_eq_mul, nsmul_eq_mul]
  have hfirst : valueRingHom 3 (partialDerivative 0 g) = 0 := by
    rw [hderivative]
    simp
  have hsecond : valueRingHom 3 (partialDerivative 0 (partialDerivative 0 g)) ≠ 0 := by
    rw [hderivative, partialDerivative_add, partialDerivative_mul, partialDerivative_mul]
    simp only [Fin.isValue, partialDerivative_coordinate_same, mul_one, ne_eq,
      zero_ne_one, not_false_eq_true, partialDerivative_coordinate_ne, zero_mul,
      zero_add, map_add, map_mul, valueRingHom_coordinate, mul_zero, add_zero]
    rw [map_ofNat]
    exact two_ne_zero
  obtain ⟨e, h, a, b, q, hnormal, hdivision, hfix, hh⟩ :=
    exists_finite_parametric_morse_pair_preparation g f hgmax hfirst hsecond
  have hbranches := morse_linear_remainder_branches_ne_zero
    g A f e h a b q hg hnormal hdivision hfix hplus hminus
  have ha : a ∈ maximalIdeal 2 := by
    rw [mem_maximalIdeal_iff]
    have heval := congrArg (valueRingHom 3) hdivision
    have hleft : valueRingHom 3 (e.pullbackAlgEquiv f) = 0 := by
      change valueRingHom 3 (e.forward.pullbackRingHom f) = 0
      rw [PointedMapGerm.valueRingHom_pullback]
      exact mem_maximalIdeal_iff.mp hf
    have hext (r : Germ 2) : valueRingHom 3 (hyperplaneExtension 2 r) = valueRingHom 2 r :=
      PointedMapGerm.valueRingHom_pullback (hyperplaneTailGerm 2) r
    rw [hleft] at heval
    simp only [map_add, map_mul, map_pow, valueRingHom_coordinate,
      zero_pow (by decide : (2 : ℕ) ≠ 0),
      hext, mem_maximalIdeal_iff.mp hh, zero_add, zero_mul, add_zero] at heval
    exact heval.symm
  exact ⟨e, h, a, b, q, hnormal, hdivision, hfix, hh, ha, hbranches⟩

end OnLeConjecture.Analytic.QuadraticCrossing
