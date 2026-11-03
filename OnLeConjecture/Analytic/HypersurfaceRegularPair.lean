/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.RegularPairExtension
public import OnLeConjecture.Analytic.PrincipalImageEquation
public import OnLeConjecture.External.LocalComplexGeometry.FiniteProjection.PreparedQuotient
public import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Two regular elements in an analytic hypersurface ring

Weierstrass division identifies a prepared three-variable hypersurface
quotient with a finite free module over the two-variable analytic ring.
The two base coordinates therefore give a regular pair. Coordinate
regularization transports this pair to the original hypersurface quotient.
-/

public noncomputable section

namespace OnLeConjecture

/-- Regularity modulo a principal ideal is invariant under ring equivalence. -/
theorem regular_mod_principal_map_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) {x y : R}
    (h : IsSMulRegular (R ⧸ Ideal.span {x}) y) :
    IsSMulRegular (S ⧸ Ideal.span {e x}) (e y) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro a ha
  rw [smul_eq_mul, Ideal.mem_span_singleton] at ha
  rw [Ideal.mem_span_singleton]
  have hback : x ∣ y * e.symm a := by
    simpa using map_dvd e.symm ha
  have hdiv : x ∣ e.symm a := by
    apply Ideal.mem_span_singleton.mp
    exact mem_of_isSMulRegular_quotient_of_smul_mem h
      (show y • e.symm a ∈ Ideal.span {x} from Ideal.mem_span_singleton.mpr hback)
  simpa using map_dvd e hdiv

/-- A coefficient representation transfers regularity modulo a base element. -/
theorem regular_mod_principal_of_pi_linearEquiv
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (e : S ≃ₗ[R] (ι → R)) {x y : R}
    (h : IsSMulRegular (R ⧸ Ideal.span {x}) y) :
    IsSMulRegular (S ⧸ Ideal.span {algebraMap R S x}) (algebraMap R S y) := by
  classical
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro a ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
  have hi (i : ι) : x ∣ e a i := by
    apply Ideal.mem_span_singleton.mp
    apply mem_of_isSMulRegular_quotient_of_smul_mem h
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e b i, ?_⟩
    have he := congrArg (fun t => e t i) hb
    simp only [smul_eq_mul, ← Algebra.smul_def] at he
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using he
  choose c hc using hi
  apply Ideal.mem_span_singleton.mpr
  refine ⟨e.symm c, ?_⟩
  apply e.injective
  rw [← Algebra.smul_def]
  rw [map_smul, e.apply_symm_apply]
  exact funext hc

/-- A nonempty coefficient representation makes the base algebra map injective. -/
theorem algebraMap_injective_of_pi_linearEquiv
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Nonempty ι]
    (e : S ≃ₗ[R] (ι → R)) : Function.Injective (algebraMap R S) := by
  intro x y h
  have hs : x • e.symm (fun _ => 1) = y • e.symm (fun _ => 1) := by
    simp only [Algebra.smul_def, h]
  have he := congrArg (fun t => e t (Classical.choice ‹Nonempty ι›)) hs
  simpa using he

namespace Analytic.Germ

/-- The second coordinate is regular modulo the first coordinate. -/
theorem coordinate_one_regular_mod_coordinate_zero :
    IsSMulRegular (Germ 2 ⧸ Ideal.span {coordinate (0 : Fin 2)})
      (coordinate (1 : Fin 2)) := by
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro a ha
  rw [← ker_hyperplaneRestriction_eq_span_coordinate_zero, RingHom.mem_ker] at ha ⊢
  change hyperplaneRestriction 1 (coordinate 1 * a) = 0 at ha
  rw [map_mul, show (1 : Fin 2) = Fin.succ 0 from rfl,
    hyperplaneRestriction_coordinate_succ] at ha
  exact (mul_eq_zero.mp ha).resolve_left coordinate_zero_ne_zero

end Analytic.Germ

open LocalComplexGeometry LocalComplexGeometry.WPTBridge ClassicalComplexWPT

namespace Analytic.HolomorphicFactorization

/-- A prepared three-variable hypersurface quotient contains a nonzero
regular pair of nonunits, obtained from the two parameter coordinates. -/
theorem exists_regular_pair_prepared_quotient {d : ℕ} (hd : 0 < d)
    (a : Fin d → Base 2 → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (ha0 : ∀ i, a i 0 = 0) :
    ∃ x y : HolomorphicGerm 3 ⧸ preparedPolynomialIdeal a ha,
      x ≠ 0 ∧ ¬ IsUnit x ∧ ¬ IsUnit y ∧
        IsSMulRegular ((HolomorphicGerm 3 ⧸ preparedPolynomialIdeal a ha) ⧸
          Ideal.span {x}) y := by
  let A := HolomorphicGerm 2
  let B := HolomorphicGerm 3
  let Q := B ⧸ preparedPolynomialIdeal a ha
  let e := preparedQuotientRemainderEquiv a ha ha0
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let : Nontrivial Q := e.symm.injective.nontrivial
  let : IsLocalRing Q :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk (preparedPolynomialIdeal a ha)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let eA := holomorphicGermRingEquiv 2
  let x : A := eA (Germ.coordinate 0)
  let y : A := eA (Germ.coordinate 1)
  have hx0 : x ≠ 0 := by
    simpa only [map_zero] using eA.injective.ne (Germ.coordinate_ne_zero 0)
  have hxnu : ¬ IsUnit x := by
    simp only [x, isUnit_map_iff, Germ.isUnit_iff_valueRingHom_ne_zero,
      Germ.valueRingHom_coordinate, ne_eq, not_true_eq_false, not_false_eq_true]
  have hynu : ¬ IsUnit y := by
    simp only [y, isUnit_map_iff, Germ.isUnit_iff_valueRingHom_ne_zero,
      Germ.valueRingHom_coordinate, ne_eq, not_true_eq_false, not_false_eq_true]
  have hreg : IsSMulRegular (A ⧸ Ideal.span {x}) y :=
    regular_mod_principal_map_ringEquiv eA Germ.coordinate_one_regular_mod_coordinate_zero
  have hnu (c : A) (hc : ¬ IsUnit c) : ¬ IsUnit (algebraMap A Q c) := by
    intro hunit
    have hu : IsUnit (lowerDimensionalInclusion 2 c) :=
      isUnit_of_map_unit (Ideal.Quotient.mk (preparedPolynomialIdeal a ha)) _ hunit
    apply hc
    rw [holomorphicGerm_isUnit_iff, evalAtOrigin_lowerDimensionalInclusion] at hu
    exact (holomorphicGerm_isUnit_iff c).mpr hu
  refine ⟨algebraMap A Q x, algebraMap A Q y, ?_, hnu x hxnu, hnu y hynu,
    regular_mod_principal_of_pi_linearEquiv e hreg⟩
  exact (algebraMap_injective_of_pi_linearEquiv e).ne hx0

/-- Every nonzero nonunit holomorphic hypersurface equation in three
variables has a quotient containing a regular pair of nonunits. -/
theorem exists_regular_pair_hypersurface_quotient
    (f : HolomorphicGerm 3) (hf : f ≠ 0) (hfu : ¬ IsUnit f) :
    ∃ x y : HolomorphicGerm 3 ⧸ Ideal.span {f},
      x ≠ 0 ∧ ¬ IsUnit x ∧ ¬ IsUnit y ∧
        IsSMulRegular ((HolomorphicGerm 3 ⧸ Ideal.span {f}) ⧸ Ideal.span {x}) y := by
  let : IsDomain (HolomorphicGerm 3) :=
    (holomorphicGermRingEquiv 3).symm.injective.isDomain
      (holomorphicGermRingEquiv 3).symm.toRingHom
  have hf0 : evalAtOrigin f = 0 := by
    simpa only [holomorphicGerm_isUnit_iff, not_not] using hfu
  obtain ⟨L, d, H, a, u, hd, _, hcoord, _, _, hprep⟩ :=
    exists_regularized_weierstrassPreparation_pos hf hf0
  have hassoc := coordinatePullback_associated_preparedPolynomialGerm L H a u hcoord hprep
  let e := coordinatePullback L
  have hI : preparedPolynomialIdeal a hprep.1 = (Ideal.span {f}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).symm
  let E := Ideal.quotientEquiv (Ideal.span {f}) (preparedPolynomialIdeal a hprep.1) e hI
  obtain ⟨x, y, hx, hxu, hyu, hxy⟩ :=
    exists_regular_pair_prepared_quotient hd a hprep.1 hprep.2.1
  refine ⟨E.symm x, E.symm y, ?_, ?_, ?_,
    regular_mod_principal_map_ringEquiv E.symm hxy⟩
  · exact E.symm.injective.ne hx
  · simpa only [isUnit_map_iff] using hxu
  · simpa only [isUnit_map_iff] using hyu

end Analytic.HolomorphicFactorization

namespace Analytic.Germ

/-- The quotient by a nonzero nonunit analytic equation in three variables
contains a nonzero regular pair of nonunits. -/
theorem exists_regular_pair_hypersurface_quotient
    (f : Germ 3) (hf : f ≠ 0) (hfu : ¬ IsUnit f) :
    ∃ x y : Germ 3 ⧸ Ideal.span {f},
      x ≠ 0 ∧ ¬ IsUnit x ∧ ¬ IsUnit y ∧
        IsSMulRegular ((Germ 3 ⧸ Ideal.span {f}) ⧸ Ideal.span {x}) y := by
  let e := holomorphicGermRingEquiv 3
  have he0 : e f ≠ 0 := by simpa only [map_zero] using e.injective.ne hf
  have heu : ¬ IsUnit (e f) := by simpa only [isUnit_map_iff] using hfu
  let E := Ideal.quotientEquiv (Ideal.span {f}) (Ideal.span {e f}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  obtain ⟨x, y, hx, hxu, hyu, hxy⟩ :=
    HolomorphicFactorization.exists_regular_pair_hypersurface_quotient (e f) he0 heu
  refine ⟨E.symm x, E.symm y, ?_, ?_, ?_,
    regular_mod_principal_map_ringEquiv E.symm hxy⟩
  · simpa only [map_zero] using E.symm.injective.ne hx
  · simpa only [isUnit_map_iff] using hxu
  · simpa only [isUnit_map_iff] using hyu

end Analytic.Germ

namespace Analytic.PointedMapGerm

/-- The image ring of a finite plane germ in three-space contains a
nonzero regular pair whose members vanish at the source origin. -/
theorem exists_image_regular_pair_of_finite
    (g : PointedMapGerm 2 3) (hf : g.IsFiniteAtOrigin) :
    ∃ x y : g.ImageRing, x ≠ 0 ∧
      (x : Germ 2) ∈ Germ.maximalIdeal 2 ∧
      (y : Germ 2) ∈ Germ.maximalIdeal 2 ∧
      IsSMulRegular (g.ImageRing ⧸ Ideal.span {x}) y := by
  obtain ⟨f, hfirr, _, hker⟩ := g.exists_irreducible_generator_of_finite hf
  obtain ⟨x, y, hx, hxu, hyu, hxy⟩ :=
    Germ.exists_regular_pair_hypersurface_quotient f hfirr.ne_zero hfirr.not_isUnit
  let E := g.quotientEquationEquivImageRing f hker
  have hvanish (c : g.ImageRing) (hc : ¬ IsUnit c) :
      (c : Germ 2) ∈ Germ.maximalIdeal 2 := by
    rw [Germ.mem_maximalIdeal_iff]
    by_contra h
    exact hc (g.image_isUnit_of_value_ne_zero h)
  refine ⟨E x, E y, ?_, hvanish (E x) ?_, hvanish (E y) ?_,
    regular_mod_principal_map_ringEquiv E hxy⟩
  · simpa only [map_zero] using E.injective.ne hx
  · simpa only [isUnit_map_iff] using hxu
  · simpa only [isUnit_map_iff] using hyu

/-- A finite plane germ in three-space is an immersion if the conductor
contains a power of each source germ vanishing at the origin. -/
theorem differential_injective_of_finite_of_maximalIdeal_le_conductor_radical
    (g : PointedMapGerm 2 3) (hf : g.IsFiniteAtOrigin)
    (hc : Germ.maximalIdeal 2 ≤ g.imageConductor.radical) :
    Function.Injective g.differential := by
  obtain ⟨x, y, hx, hxm, hym, hxy⟩ := g.exists_image_regular_pair_of_finite hf
  exact g.differential_injective_of_regular_pair_in_conductor_radical
    x y hx hxy (hc hxm) (hc hym)

/-- A finite plane germ in three-space whose conductor has finite
colength is an immersion. -/
theorem differential_injective_of_finite_of_conductor_finite_colength
    (g : PointedMapGerm 2 3) (hf : g.IsFiniteAtOrigin)
    (hc : Module.Finite ℂ (Germ 2 ⧸ g.imageConductor)) :
    Function.Injective g.differential := by
  obtain ⟨N, hN⟩ :=
    (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le g.imageConductor).mp hc
  apply g.differential_injective_of_finite_of_maximalIdeal_le_conductor_radical hf
  intro a ha
  exact ⟨N, hN (Ideal.pow_mem_pow ha N)⟩

end Analytic.PointedMapGerm

end OnLeConjecture
