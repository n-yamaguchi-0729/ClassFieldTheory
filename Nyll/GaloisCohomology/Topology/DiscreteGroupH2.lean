/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousCrossedHom
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Group

/-!
# Comparing degree-two cohomology on discrete groups

Ordinary and continuous cohomology agree in degree two when the acting
group is discrete. The comparison keeps the given coefficient action and
sends a homogeneous cocycle `z` to `(g, h) ↦ z(1, g, g * h)`.
-/

@[expose] public section

open CategoryTheory TopRep ContRepresentation
open scoped Topology

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{u} ℤ G)

/-- The ordinary representation with lifted integer scalars and the same
carrier and action as the continuous representation. -/
def underlyingIntegralRep : Rep.{u} (ULift.{u} ℤ) G := by
  let : Module ℤ X := X.hV2
  exact (IntegralGroupCohomology.coefficientFunctor G).obj (Rep.of X.ρ.toRepresentation)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem ρ_mul_apply (g h : G) (a : X) : X.ρ g (X.ρ h a) = X.ρ (g * h) a := by
  let : Module ℤ X := X.hV2
  exact DFunLike.congr_fun (map_mul X.ρ g h).symm a

private theorem homogeneousOne_differential
    (z : (homogeneousCochains X).X 1) (a b c : G) :
    (((homogeneousCochains X).d 1 2).hom z).1 a b c = z.1 b c - z.1 a c + z.1 a b := by
  rw [congrArg (fun τ => τ a b c) (homogeneousCochains.d_apply X 1 z)]
  change z.1 b c - (z.1 a c - z.1 a b) = _
  abel

private theorem homogeneousTwo_differential
    (z : (homogeneousCochains X).X 2) (a b c d : G) :
    (((homogeneousCochains X).d 2 3).hom z).1 a b c d =
      z.1 b c d - z.1 a c d + z.1 a b d - z.1 a b c := by
  rw [congrArg (fun τ => τ a b c d) (homogeneousCochains.d_apply X 2 z)]
  change z.1 b c d - (z.1 a c d - (z.1 a b d - z.1 a b c)) = _
  abel

private theorem homogeneousTwo_equivariant
    (z : (homogeneousCochains X).X 2) (g a b c : G) :
    X.ρ g (z.1 a b c) = z.1 (g * a) (g * b) (g * c) := by
  have h := congrArg (fun τ => τ (g * a) (g * b) (g * c)) (z.2 g)
  change X.ρ g (z.1 (g⁻¹ * (g * a)) (g⁻¹ * (g * b)) (g⁻¹ * (g * c))) = _ at h
  simpa only [inv_mul_cancel_left] using h

private theorem homogeneousOne_equivariant
    (z : (homogeneousCochains X).X 1) (g a b : G) :
    X.ρ g (z.1 a b) = z.1 (g * a) (g * b) := by
  have h := congrArg (fun τ => τ (g * a) (g * b)) (z.2 g)
  change X.ρ g (z.1 (g⁻¹ * (g * a)) (g⁻¹ * (g * b))) = _ at h
  simpa only [inv_mul_cancel_left] using h

private theorem dehomogenizeTwo_injective :
    Function.Injective (fun z : (homogeneousCochains X).X 2 =>
      fun p : G × G => z.1 1 p.1 (p.1 * p.2)) := by
  intro z w h
  apply Subtype.ext
  ext a b c
  have norm (z₀ : (homogeneousCochains X).X 2) :
      X.ρ a (z₀.1 1 (a⁻¹ * b) (a⁻¹ * c)) = z₀.1 a b c := by
    simpa only [mul_one, mul_inv_cancel_left] using
      homogeneousTwo_equivariant X z₀ a 1 (a⁻¹ * b) (a⁻¹ * c)
  rw [← norm z, ← norm w]
  apply congrArg (X.ρ a)
  have h₀ := congrFun h (a⁻¹ * b, b⁻¹ * c)
  change z.1 1 (a⁻¹ * b) ((a⁻¹ * b) * (b⁻¹ * c)) =
    w.1 1 (a⁻¹ * b) ((a⁻¹ * b) * (b⁻¹ * c)) at h₀
  simpa only [mul_assoc, mul_inv_cancel_left] using h₀

/-- Dehomogenization on actual degree-two cocycles. -/
def dehomogenizeIntegralTwo :
    cocycles X 2 →+ groupCohomology.cocycles₂ (underlyingIntegralRep X) where
  toFun z := ⟨fun p => ((homogeneousCochains X).iCycles 2 z).1 1 p.1 (p.1 * p.2), by
    apply (groupCohomology.mem_cocycles₂_def _).mpr
    intro a b c
    let w := (homogeneousCochains X).iCycles 2 z
    have h := degreeTwo_cocycle_equation X z 1 a (a * b) (a * b * c)
    have he := homogeneousTwo_equivariant X w a 1 b (b * c)
    rw [mul_one, ← mul_assoc] at he
    change X.ρ a (w.1 1 b (b * c)) - w.1 1 (a * b) (a * b * c) +
      w.1 1 a (a * (b * c)) - w.1 1 a (a * b) = 0
    rw [he, ← mul_assoc]
    exact h⟩
  map_zero' := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    exact congrArg (fun f : (homogeneousCochains X).X 2 => f.1 1 a (a * b))
      (map_zero ((homogeneousCochains X).iCycles 2).hom)
  map_add' z w := by
    apply groupCohomology.cocycles₂_ext
    intro a b
    exact congrArg (fun f : (homogeneousCochains X).X 2 => f.1 1 a (a * b))
      (map_add ((homogeneousCochains X).iCycles 2).hom z w)

/-- The comparison retains the original inhomogeneous values. -/
theorem dehomogenizeIntegralTwo_apply (z : cocycles X 2) (a b : G) :
    dehomogenizeIntegralTwo X z (a, b) = ((homogeneousCochains X).iCycles 2 z).1 1 a (a * b) :=
  rfl

/-- The homogeneous cocycle is recovered using its actual coefficient
action and its two consecutive increments. -/
theorem homogeneousIntegralTwo_apply (z : cocycles X 2) (a b c : G) :
    ((homogeneousCochains X).iCycles 2 z).val a b c =
      X.ρ a (dehomogenizeIntegralTwo X z (a⁻¹ * b, b⁻¹ * c)) := by
  rw [dehomogenizeIntegralTwo_apply, mul_assoc, mul_inv_cancel_left]
  symm
  simpa only [mul_one, mul_inv_cancel_left] using
    homogeneousTwo_equivariant X ((homogeneousCochains X).iCycles 2 z) a 1 (a⁻¹ * b) (a⁻¹ * c)

/-- Dehomogenizing a continuous degree-two boundary gives the ordinary
boundary of the original degree-one primitive. -/
theorem dehomogenizeBoundary_one_apply
    (z : (homogeneousCochains X).X 1) (a b : G) :
    (((homogeneousCochains X).d 1 2).hom z).1 1 a (a * b) =
      groupCohomology.d₁₂ (underlyingIntegralRep X) (fun g => z.1 1 g) (a, b) := by
  rw [homogeneousOne_differential]
  change z.1 a (a * b) - z.1 1 (a * b) + z.1 1 a =
    X.ρ a (z.1 1 b) - z.1 1 (a * b) + z.1 1 a
  have h := homogeneousOne_equivariant X z a 1 b
  rw [mul_one] at h
  rw [h]

variable [DiscreteTopology G]

private def homogenizeOne (c : G → underlyingIntegralRep X) : (homogeneousCochains X).X 1 := by
  change G → X at c
  let w : C(G, C(G, X)) :=
    ⟨fun a => ⟨fun b => X.ρ a (c (a⁻¹ * b)), continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩
  refine ⟨w, ?_⟩
  intro g
  ext a b
  change X.ρ g (X.ρ (g⁻¹ * a) (c ((g⁻¹ * a)⁻¹ * (g⁻¹ * b)))) = X.ρ a (c (a⁻¹ * b))
  rw [ρ_mul_apply X, mul_inv_cancel_left,
    show (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = a⁻¹ * b by group]

private def homogenizeTwo (c : G × G → underlyingIntegralRep X) :
    (homogeneousCochains X).X 2 := by
  change G × G → X at c
  let w : C(G, C(G, C(G, X))) :=
    ⟨fun a => ⟨fun b => ⟨fun d => X.ρ a (c (a⁻¹ * b, b⁻¹ * d)),
        continuous_of_discreteTopology⟩, continuous_of_discreteTopology⟩,
      continuous_of_discreteTopology⟩
  refine ⟨w, ?_⟩
  intro g
  ext a b d
  change X.ρ g (X.ρ (g⁻¹ * a) (c ((g⁻¹ * a)⁻¹ * (g⁻¹ * b),
      (g⁻¹ * b)⁻¹ * (g⁻¹ * d)))) = X.ρ a (c (a⁻¹ * b, b⁻¹ * d))
  rw [ρ_mul_apply X, mul_inv_cancel_left,
    show (g⁻¹ * a)⁻¹ * (g⁻¹ * b) = a⁻¹ * b by group,
    show (g⁻¹ * b)⁻¹ * (g⁻¹ * d) = b⁻¹ * d by group]

private theorem homogenizeTwo_mem_cycles (z : groupCohomology.cocycles₂ (underlyingIntegralRep X)) :
    ((homogeneousCochains X).d 2 3).hom (homogenizeTwo X z) = 0 := by
  apply Subtype.ext
  ext a b c d
  rw [homogeneousTwo_differential]
  let z₀ : G × G → X := z
  have h := (groupCohomology.mem_cocycles₂_def _).mp z.2 (a⁻¹ * b) (b⁻¹ * c) (c⁻¹ * d)
  change X.ρ (a⁻¹ * b) (z₀ (b⁻¹ * c, c⁻¹ * d)) - z₀ ((a⁻¹ * b) * (b⁻¹ * c), c⁻¹ * d) +
    z₀ (a⁻¹ * b, (b⁻¹ * c) * (c⁻¹ * d)) - z₀ (a⁻¹ * b, b⁻¹ * c) = 0 at h
  rw [show (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c by group,
    show (b⁻¹ * c) * (c⁻¹ * d) = b⁻¹ * d by group] at h
  have h' := congrArg (X.ρ a) h
  simp only [map_sub, map_add, map_zero, ρ_mul_apply X, mul_inv_cancel_left] at h'
  exact h'

/-- Every ordinary cocycle comes from a homogeneous continuous cocycle
when the group is discrete. -/
theorem dehomogenizeIntegralTwo_surjective : Function.Surjective (dehomogenizeIntegralTwo X) := by
  intro z
  let w := homogenizeTwo X z
  let C := homogeneousCochains X
  let line := CrossedHom.scalarLine w
  have h := CrossedHom.scalarLine_comp_eq_zero w (C.d 2 3) (homogenizeTwo_mem_cycles X z)
  let w' := C.liftCycles line 3 (CochainComplex.next ℕ 2) h (ULift.up (1 : ℤ))
  have hw : C.iCycles 2 w' = w := by
    change C.iCycles 2 (C.liftCycles line 3 (CochainComplex.next ℕ 2) h (ULift.up (1 : ℤ))) = w
    rw [← ConcreteCategory.comp_apply, C.liftCycles_i]
    exact CrossedHom.scalarLine_one w
  refine ⟨w', groupCohomology.cocycles₂_ext (fun a b => ?_)⟩
  rw [dehomogenizeIntegralTwo_apply]
  change (C.iCycles 2 w').1 1 a (a * b) = _
  rw [hw]
  change X.ρ 1 (z (1⁻¹ * a, a⁻¹ * (a * b))) = z (a, b)
  rw [inv_one, one_mul, inv_mul_cancel_left, map_one]
  rfl

/-- The original continuous class vanishes precisely when the ordinary class vanishes. -/
theorem dehomogenizeIntegralTwo_class_eq_zero_iff (z : cocycles X 2) :
    groupCohomology.H2π (underlyingIntegralRep X) (dehomogenizeIntegralTwo X z) = 0 ↔
      π X 2 z = 0 := by
  rw [groupCohomology.H2π_eq_zero_iff]
  let C := homogeneousCochains X
  let y := C.iCycles 2 z
  constructor
  · rintro ⟨c, hc⟩
    let w := homogenizeOne X c
    have hw (a : G) : w.1 1 a = c a := by
      change X.ρ 1 (c (1⁻¹ * a)) = c a
      rw [inv_one, one_mul, map_one]
      rfl
    have hboundary : (C.d 1 2).hom w = y := by
      apply dehomogenizeTwo_injective X
      funext p
      change ((C.d 1 2).hom w).1 1 p.1 (p.1 * p.2) = y.1 1 p.1 (p.1 * p.2)
      rw [dehomogenizeBoundary_one_apply X w p.1 p.2]
      have hfun : (fun a => w.1 1 a) = c := funext hw
      rw [hfun]
      exact congrFun hc p
    have hcycle : (C.toCycles 1 2).hom w = z := by
      let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
      apply (ModuleCat.mono_iff_injective (F.map (C.iCycles 2))).mp inferInstance
      have hk := ConcreteCategory.congr_hom (C.toCycles_i 1 2) w
      exact hk.trans hboundary
    rw [← hcycle]
    exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) w
  · intro h
    obtain ⟨w, hw⟩ := exists_boundary_of_π_eq_zero X 1 z h
    change (C.d 1 2).hom w = y at hw
    refine ⟨fun a => w.1 1 a, ?_⟩
    funext p
    have he := congrArg (fun a : C.X 2 => a.1 1 p.1 (p.1 * p.2)) hw
    exact (dehomogenizeBoundary_one_apply X w p.1 p.2).symm.trans
      (he.trans (dehomogenizeIntegralTwo_apply X z p.1 p.2).symm)

/-- The cohomology map induced by ordinary dehomogenization. -/
def discreteIntegralH2Hom : continuousCohomology 2 X →+
    groupCohomology (underlyingIntegralRep X) 2 := by
  let p := (π X 2).hom.toLinearMap.toAddMonoidHom
  let f := (groupCohomology.H2π (underlyingIntegralRep X)).hom.toAddMonoidHom.comp
    (dehomogenizeIntegralTwo X)
  let e := QuotientAddGroup.quotientKerEquivOfSurjective p (π_surjective X 2)
  exact (QuotientAddGroup.lift p.ker f (fun z hz =>
    (dehomogenizeIntegralTwo_class_eq_zero_iff X z).mpr hz)).comp e.symm.toAddMonoidHom

/-- The comparison takes an actual class to its dehomogenized representative. -/
theorem discreteIntegralH2Hom_π (z : cocycles X 2) :
    discreteIntegralH2Hom X (π X 2 z) =
      groupCohomology.H2π (underlyingIntegralRep X) (dehomogenizeIntegralTwo X z) := by
  let p := (π X 2).hom.toLinearMap.toAddMonoidHom
  let e := QuotientAddGroup.quotientKerEquivOfSurjective p (π_surjective X 2)
  have he : e.symm (π X 2 z) = QuotientAddGroup.mk z := by
    apply e.injective
    exact e.apply_symm_apply _
  let f := (groupCohomology.H2π (underlyingIntegralRep X)).hom.toAddMonoidHom.comp
    (dehomogenizeIntegralTwo X)
  have hf : p.ker ≤ f.ker := fun w hw => (dehomogenizeIntegralTwo_class_eq_zero_iff X w).mpr hw
  change QuotientAddGroup.lift p.ker f hf (e.symm (π X 2 z)) = _
  exact (congrArg (QuotientAddGroup.lift p.ker f hf) he).trans rfl

/-- Actual continuous and ordinary degree-two classes agree on a discrete
group, with the original nontrivial coefficient action permitted. -/
def discreteIntegralH2Equiv : continuousCohomology 2 X ≃+
    groupCohomology (underlyingIntegralRep X) 2 := by
  apply AddEquiv.ofBijective (discreteIntegralH2Hom X)
  constructor
  · apply (injective_iff_map_eq_zero (discreteIntegralH2Hom X)).mpr
    intro h hh
    obtain ⟨z, rfl⟩ := π_surjective X 2 h
    rw [discreteIntegralH2Hom_π] at hh
    exact (dehomogenizeIntegralTwo_class_eq_zero_iff X z).mp hh
  · intro h
    induction h using groupCohomology.H2_induction_on with
    | h z =>
      obtain ⟨w, rfl⟩ := dehomogenizeIntegralTwo_surjective X z
      exact ⟨π X 2 w, discreteIntegralH2Hom_π X w⟩

section OriginalIntegers

variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q]
    (Y : TopRep.{0} ℤ Q)

/-- The ordinary integer representation has the original carrier and action. -/
abbrev underlyingIntegerRep : Rep ℤ Q := by
  let : Module ℤ Y := Y.hV2
  exact Rep.of Y.ρ.toRepresentation

/-- The same degree-two cocycle in the original integer-coefficient model. -/
def dehomogenizeTwoOriginal (z : cocycles Y 2) :
    groupCohomology.cocycles₂ (underlyingIntegerRep Y) :=
  ⟨fun p => ((homogeneousCochains Y).iCycles 2 z).val 1 p.1 (p.1 * p.2), by
    apply (groupCohomology.mem_cocycles₂_def _).mpr
    intro a b c
    exact (groupCohomology.mem_cocycles₂_def _).mp (dehomogenizeIntegralTwo Y z).property a b c⟩

omit [DiscreteTopology Q] in
/-- Dehomogenization in the original integer model evaluates the original cocycle. -/
theorem dehomogenizeTwoOriginal_apply (z : cocycles Y 2) (a b : Q) :
    dehomogenizeTwoOriginal Y z (a, b) = ((homogeneousCochains Y).iCycles 2 z).val 1 a (a * b) :=
  rfl

/-- A continuous class vanishes exactly when its original integer-coefficient class vanishes. -/
theorem dehomogenizeTwoOriginal_class_eq_zero_iff (z : cocycles Y 2) :
    groupCohomology.H2π (underlyingIntegerRep Y) (dehomogenizeTwoOriginal Y z) = 0 ↔
      π Y 2 z = 0 := by
  rw [← dehomogenizeIntegralTwo_class_eq_zero_iff Y z,
    groupCohomology.H2π_eq_zero_iff, groupCohomology.H2π_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, funext fun p => congrFun hb p⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, funext fun p => congrFun hb p⟩

end OriginalIntegers

end ContinuousCohomology
