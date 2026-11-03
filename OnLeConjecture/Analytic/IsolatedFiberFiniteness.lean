/-
Copyright (c) 2026 Pablo Portilla Cuadrado. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Pablo Portilla Cuadrado
-/
module

public import OnLeConjecture.Analytic.IsolatedFiber
public import OnLeConjecture.Analytic.FiniteColength
public import OnLeConjecture.Analytic.PlaneElimination
public import OnLeConjecture.Analytic.LinearCoordinates

/-!
# The isolated fibre finiteness bridge

The local analytic finiteness theorem factors into two precise statements.
The local analytic Nullstellensatz identifies the radical of the coordinate
ideal of an isolated zero fibre. The finite fibre criterion then promotes
finite dimensionality of the coordinate quotient to module finiteness over
the analytic image ring.

The commutative algebra between these statements is proved here. In
particular, radical equality implies that the coordinate ideal contains a
power of the source maximal ideal and hence has finite complex colength.
-/

public section

namespace OnLeConjecture.Analytic

open Filter Metric
open scoped Topology

namespace PointedMapGerm

/-- The coordinate fibre algebra has finite complex dimension. -/
@[expose] def HasFiniteCoordinateFiber {n m : ℕ}
    (f : PointedMapGerm n m) : Prop :=
  Module.Finite ℂ (Germ n ⧸ f.1.coordinateIdeal)

/-- The local analytic Nullstellensatz at the origin for source and target
dimensions `n` and `m`. -/
@[expose] def LocalAnalyticNullstellensatzAtOrigin (n m : ℕ) : Prop :=
  ∀ f : PointedMapGerm n m,
    f.HasIsolatedZeroRepresentative →
      f.1.coordinateIdeal.radical = Germ.maximalIdeal n

/-- The finite fibre criterion for analytic map germs of fixed source and
target dimensions. -/
@[expose] def FiniteFiberCriterionAtOrigin (n m : ℕ) : Prop :=
  ∀ f : PointedMapGerm n m,
    f.HasFiniteCoordinateFiber → f.IsFiniteAtOrigin

/-- The isolated fibre finite colength theorem for fixed source and target
dimensions. -/
@[expose] def IsolatedFiberHasFiniteColengthAtOrigin (n m : ℕ) : Prop :=
  ∀ f : PointedMapGerm n m,
    f.HasIsolatedZeroRepresentative → f.HasFiniteCoordinateFiber

/-- The plane elimination principle for isolated zero fibres. -/
@[expose] def PlaneIsolatedFiberElimination (m : ℕ) : Prop :=
  ∀ (f : PointedMapGerm 2 m) (e : PointedEquivGerm 2)
    (g : Germ 2) (d : ℕ),
    f.HasIsolatedZeroRepresentative →
      g ∈ (f.comp e.forward).1.coordinateIdeal →
        Germ.IsRegularInFirstCoordinateOfOrder g (d + 1) →
          Ideal.comap (Germ.hyperplaneExtension 1)
            (f.comp e.forward).1.coordinateIdeal ≠ ⊥

/-- An isolated zero fibre in the plane has a nonzero coordinate ideal. -/
theorem HasIsolatedZeroRepresentative.coordinateIdeal_ne_bot
    {m : ℕ} {f : PointedMapGerm 2 m}
    (hisolated : f.HasIsolatedZeroRepresentative) :
    f.1.coordinateIdeal ≠ ⊥ := by
  rintro hbot
  rw [PointedMapGerm.HasIsolatedZeroRepresentative] at hisolated
  rcases hisolated with ⟨F, hF, hF0, hrepr, s, hs, hisolated⟩
  have hcomponent : ∀ i : Fin m,
      ((fun x : Source 2 ↦ F x i) : FunctionGerm 2) = 0 := by
    intro i
    have hi : f.1.component i = 0 := by
      rw [← Ideal.mem_bot, ← hbot]
      exact f.1.component_mem_coordinateIdeal i
    rw [hrepr] at hi
    exact (congrArg Subtype.val hi).trans (Filter.Germ.coe_zero.symm)
  have hcomponentEventually : ∀ i : Fin m,
      ∀ᶠ x in 𝓝 (0 : Source 2), F x i = 0 := by
    intro i
    exact Filter.Germ.coe_eq.mp (hcomponent i)
  have hzero : ∀ᶠ x in 𝓝 (0 : Source 2), F x = 0 := by
    have hall := Filter.eventually_all.mpr hcomponentEventually
    filter_upwards [hall] with x hx
    exact funext hx
  have hinter : s ∩ {x : Source 2 | F x = 0} ∈ 𝓝 (0 : Source 2) :=
    Filter.inter_mem hs hzero
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hinter
  let x : Source 2 :=
    Pi.single (0 : Fin 2) (epsilon / 2 : ℂ)
  have hxNorm : ‖x‖ = epsilon / 2 := by
    simp [x, Pi.norm_single, hepsilon.le]
  have hxBall : x ∈ Metric.ball (0 : Source 2) epsilon := by
    rw [Metric.mem_ball, dist_zero_right, hxNorm]
    linarith
  have hx := hball hxBall
  have hxZero : x = 0 := hisolated x hx.1 hx.2
  have hcoordinate := congrFun hxZero (0 : Fin 2)
  change (epsilon / 2 : ℂ) = 0 at hcoordinate
  have hcomplex : (epsilon / 2 : ℂ) ≠ 0 := by
    exact_mod_cast
      (div_ne_zero hepsilon.ne' (by norm_num : (2 : ℝ) ≠ 0))
  exact hcomplex hcoordinate

/-- Radical equality for the coordinate ideal implies that the coordinate
fibre algebra has finite complex dimension. -/
theorem hasFiniteCoordinateFiber_of_radical_coordinateIdeal_eq_maximalIdeal
    {n m : ℕ} (f : PointedMapGerm n m)
    (hradical : f.1.coordinateIdeal.radical = Germ.maximalIdeal n) :
    f.HasFiniteCoordinateFiber := by
  have hle : Germ.maximalIdeal n ≤ f.1.coordinateIdeal.radical := by
    rw [hradical]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    hle (Germ.maximalIdeal_fg n)
  exact Germ.quotient_moduleFinite_of_maximalIdeal_pow_le
    f.1.coordinateIdeal hN

/-- Finite complex dimension of the coordinate fibre is equivalent to the
coordinate ideal having radical equal to the source maximal ideal. -/
theorem hasFiniteCoordinateFiber_iff_radical_coordinateIdeal_eq_maximalIdeal
    {n m : ℕ} (f : PointedMapGerm n m) :
    f.HasFiniteCoordinateFiber ↔
      f.1.coordinateIdeal.radical = Germ.maximalIdeal n := by
  constructor
  · intro hfinite
    obtain ⟨N, hN⟩ :=
      (Germ.quotient_moduleFinite_iff_exists_maximalIdeal_pow_le
        f.1.coordinateIdeal).mp hfinite
    apply le_antisymm
    · exact (Germ.maximalIdeal_isMaximal n).isPrime.radical_le_iff.mpr
        f.coordinateIdeal_le_maximalIdeal
    · intro q hq
      exact ⟨N, hN (Ideal.pow_mem_pow hq N)⟩
  · exact f.hasFiniteCoordinateFiber_of_radical_coordinateIdeal_eq_maximalIdeal

/-- The isolated fibre finite colength theorem is equivalent to the local
analytic Nullstellensatz in the form relevant to coordinate ideals. -/
theorem isolatedFiberHasFiniteColengthAtOrigin_iff
    (n m : ℕ) :
    PointedMapGerm.IsolatedFiberHasFiniteColengthAtOrigin n m ↔
      PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin n m := by
  constructor
  · intro hfinite f hisolated
    exact
      (f.hasFiniteCoordinateFiber_iff_radical_coordinateIdeal_eq_maximalIdeal).mp
        (hfinite f hisolated)
  · intro hnull f hisolated
    exact
      (f.hasFiniteCoordinateFiber_iff_radical_coordinateIdeal_eq_maximalIdeal).mpr
        (hnull f hisolated)

/-- For a plane source, finite colength of every isolated zero fibre is
equivalent to the plane elimination principle. -/
theorem isolatedFiberHasFiniteColengthAtOrigin_two_iff_elimination
    (m : ℕ) :
    PointedMapGerm.IsolatedFiberHasFiniteColengthAtOrigin 2 m ↔
      PointedMapGerm.PlaneIsolatedFiberElimination m := by
  constructor
  · intro hfinite f e g d hisolated hg hregular
    have hmap := f.map_coordinateIdeal_pullbackRingEquiv e
    have htransformed : Module.Finite ℂ
        (Germ 2 ⧸ (f.comp e.forward).1.coordinateIdeal) :=
      (Germ.quotient_moduleFinite_iff_of_map_eq
        f.1.coordinateIdeal (f.comp e.forward).1.coordinateIdeal
        e.pullbackAlgEquiv hmap).mp (hfinite f hisolated)
    exact
      (Germ.quotient_moduleFinite_iff_comap_hyperplaneExtension_ne_bot
        (f.comp e.forward).1.coordinateIdeal hregular hg).mp htransformed
  · intro helimination f hisolated
    obtain ⟨q, hqI, hqZero⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot
        hisolated.coordinateIdeal_ne_bot
    obtain ⟨e, n, hregular⟩ :=
      Germ.exists_linear_equiv_regularInFirstCoordinate hqZero
    have hn : 0 < n := by
      by_contra hn
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      have hunitTransformed :
          IsUnit (e.forward.pullbackRingHom q) := by
        simpa using
          Germ.isUnit_firstCoordinateTailIterate_of_regular hregular
      have hunit : IsUnit q :=
        (MulEquiv.isUnit_map e.pullbackRingEquiv.toMulEquiv).mp (by
          simpa using hunitTransformed)
      have hqMaximal : q ∈ Germ.maximalIdeal 2 :=
        f.coordinateIdeal_le_maximalIdeal hqI
      rw [Germ.mem_maximalIdeal_iff] at hqMaximal
      exact (Germ.isUnit_iff_valueRingHom_ne_zero.mp hunit) hqMaximal
    obtain ⟨d, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    let g : Germ 2 := e.forward.pullbackRingHom q
    have hg : g ∈ (f.comp e.forward).1.coordinateIdeal := by
      rw [← f.map_coordinateIdeal_pullbackRingEquiv e]
      exact Ideal.mem_map_of_mem e.pullbackRingEquiv.toRingHom hqI
    have hgRegular :
        Germ.IsRegularInFirstCoordinateOfOrder g (d + 1) := by
      simpa [g, PointedEquivGerm.pullbackRingEquiv_apply] using hregular
    have helim : Ideal.comap (Germ.hyperplaneExtension 1)
        (f.comp e.forward).1.coordinateIdeal ≠ ⊥ :=
      helimination f e g d hisolated hg hgRegular
    have htransformed : Module.Finite ℂ
        (Germ 2 ⧸ (f.comp e.forward).1.coordinateIdeal) :=
      (Germ.quotient_moduleFinite_iff_comap_hyperplaneExtension_ne_bot
        (f.comp e.forward).1.coordinateIdeal hgRegular hg).mpr helim
    exact
      (Germ.quotient_moduleFinite_iff_of_map_eq
        f.1.coordinateIdeal (f.comp e.forward).1.coordinateIdeal
        e.pullbackAlgEquiv
        (f.map_coordinateIdeal_pullbackRingEquiv e)).mpr htransformed

/-- For a plane source, the local analytic Nullstellensatz for coordinate
ideals is equivalent to the plane elimination principle. -/
theorem localAnalyticNullstellensatzAtOrigin_two_iff_elimination
    (m : ℕ) :
    PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin 2 m ↔
      PointedMapGerm.PlaneIsolatedFiberElimination m := by
  rw [← PointedMapGerm.isolatedFiberHasFiniteColengthAtOrigin_iff]
  exact PointedMapGerm.isolatedFiberHasFiniteColengthAtOrigin_two_iff_elimination m

/-- Under the local analytic Nullstellensatz, the coordinate ideal of an
isolated zero fibre is primary for the source maximal ideal. -/
theorem HasIsolatedZeroRepresentative.coordinateIdeal_isPrimary
    {n m : ℕ} {f : PointedMapGerm n m}
    (hisolated : f.HasIsolatedZeroRepresentative)
    (hnullstellensatz :
      PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin n m) :
    f.1.coordinateIdeal.IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [hnullstellensatz f hisolated]
  exact Germ.maximalIdeal_isMaximal n

/-- The local analytic Nullstellensatz gives finite coordinate fibre for an
isolated zero representative. -/
theorem HasIsolatedZeroRepresentative.hasFiniteCoordinateFiber
    {n m : ℕ} {f : PointedMapGerm n m}
    (hisolated : f.HasIsolatedZeroRepresentative)
    (hnullstellensatz :
      PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin n m) :
    f.HasFiniteCoordinateFiber :=
  f.hasFiniteCoordinateFiber_of_radical_coordinateIdeal_eq_maximalIdeal
    (hnullstellensatz f hisolated)

/-- The local analytic Nullstellensatz and the finite fibre criterion imply
that every isolated zero fibre defines a finite analytic map germ. -/
theorem HasIsolatedZeroRepresentative.isFiniteAtOrigin
    {n m : ℕ} {f : PointedMapGerm n m}
    (hisolated : f.HasIsolatedZeroRepresentative)
    (hnullstellensatz :
      PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin n m)
    (hfiniteFiber : PointedMapGerm.FiniteFiberCriterionAtOrigin n m) :
    f.IsFiniteAtOrigin :=
  hfiniteFiber f
    (hisolated.hasFiniteCoordinateFiber hnullstellensatz)

/-- The isolated fibre finite colength theorem and the finite fibre
criterion imply local finiteness. -/
theorem HasIsolatedZeroRepresentative.isFiniteAtOrigin_of_finiteColength
    {n m : ℕ} {f : PointedMapGerm n m}
    (hisolated : f.HasIsolatedZeroRepresentative)
    (hcolength :
      PointedMapGerm.IsolatedFiberHasFiniteColengthAtOrigin n m)
    (hfiniteFiber : PointedMapGerm.FiniteFiberCriterionAtOrigin n m) :
    f.IsFiniteAtOrigin :=
  hfiniteFiber f (hcolength f hisolated)

/-- The two local analytic principles give the finiteness input used in the
assembly of Lê's conjecture. -/
theorem isFiniteAtOrigin_of_injective
    {n m : ℕ}
    (hnullstellensatz :
      PointedMapGerm.LocalAnalyticNullstellensatzAtOrigin n m)
    (hfiniteFiber : PointedMapGerm.FiniteFiberCriterionAtOrigin n m)
    (f : PointedMapGerm n m) (hinjective : f.HasInjectiveRepresentative) :
    f.IsFiniteAtOrigin :=
  (PointedMapGerm.hasIsolatedZeroRepresentative_of_injective
    f hinjective).isFiniteAtOrigin hnullstellensatz hfiniteFiber

/-- Plane elimination and the finite fibre criterion give the local
finiteness input for an injective map germ with plane source. -/
theorem isFiniteAtOrigin_of_injective_two
    {m : ℕ}
    (helimination : PointedMapGerm.PlaneIsolatedFiberElimination m)
    (hfiniteFiber : PointedMapGerm.FiniteFiberCriterionAtOrigin 2 m)
    (f : PointedMapGerm 2 m)
    (hinjective : f.HasInjectiveRepresentative) :
    f.IsFiniteAtOrigin := by
  apply PointedMapGerm.isFiniteAtOrigin_of_injective
    ((PointedMapGerm.localAnalyticNullstellensatzAtOrigin_two_iff_elimination
      m).mpr helimination) hfiniteFiber f hinjective

end PointedMapGerm

end OnLeConjecture.Analytic
