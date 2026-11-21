/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousH0Naturality
public import Nyll.GaloisCohomology.Topology.ContinuousInvariantPairing
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.Topology.ContinuousSubgroupPrimitiveExtension
public import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient

/-! # Corestriction on actual continuous homogeneous cochains

Extend along the continuous subgroup retraction and sum the translates over
the original finite coset space. Coordinate omissions commute with this sum.
-/

@[expose] public section

open scoped Topology BigOperators
open CategoryTheory ContRepresentation TopRep ReidemeisterSchreier.Profinite

noncomputable section
namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (X : TopRep.{u} ℤ G) (H : OpenSubgroup G)

local notation "I" => Subtype (fun g : G => g ∈ H.toSubgroup)
local notation "Y" => TopRep.res H.toSubgroup.subtype X
local notation "Q" => G ⧸ (H : Subgroup G)

/-- The finite left-coset enumeration used by continuous corestriction. -/
@[instance_reducible] noncomputable def openSubgroupQuotientFintype : Fintype Q :=
  let : Finite Q := Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen'
  Fintype.ofFinite Q

local instance : Fintype Q := openSubgroupQuotientFintype H

/-- Translation acts on the value and diagonally on the original tuple arguments. -/
def translateTuple {n : ℕ} (g : G) (c : C(Fin n → G, X)) : C(Fin n → G, X) := by
  letI : Module ℤ X := X.hV2
  exact ⟨fun a => X.ρ g (c (fun i => g⁻¹ * a i)),
    (X.ρ g).continuous.comp (c.continuous.comp (continuous_pi fun i =>
      continuous_const.mul (continuous_apply i)))⟩

omit [CompactSpace G] in
private theorem translateTuple_mul {n : ℕ} (c : C(Fin n → G, X)) (g k : G) :
    translateTuple X (g * k) c = translateTuple X g (translateTuple X k c) := by
  let : Module ℤ X := X.hV2
  apply ContinuousMap.ext
  intro a
  have ha : (fun i => (g * k)⁻¹ * a i) = fun i => k⁻¹ * (g⁻¹ * a i) := by
    funext i
    rw [mul_inv_rev, mul_assoc]
  change X.ρ (g * k) (c (fun i => (g * k)⁻¹ * a i)) =
    X.ρ g (X.ρ k (c (fun i => k⁻¹ * (g⁻¹ * a i))))
  rw [ha]
  have h : X.ρ (g * k) = X.ρ g * X.ρ k := map_mul X.ρ g k
  exact DFunLike.congr_fun h (c (fun i => k⁻¹ * (g⁻¹ * a i)))

/-- Extend a subgroup cochain to ambient tuples using the subgroup retraction. -/
def extendedTuple (n : ℕ) (c : (homogeneousCochains Y).X n) : C(Fin (n + 1) → G, X) :=
  (resolutionTupleHomeomorph I Y (n + 1) c.val).comp
    ⟨fun a i => openSubgroupRetraction H (a i),
      continuous_pi fun i => (openSubgroupRetraction H).continuous.comp (continuous_apply i)⟩

/-- The extended cochain is fixed by diagonal translation along the subgroup. -/
theorem translateTuple_extendedTuple_subgroup (n : ℕ) (c : (homogeneousCochains Y).X n) (h : I) :
    translateTuple X (h : G) (extendedTuple X H n c) = extendedTuple X H n c := by
  apply ContinuousMap.ext
  intro a
  let b := resolutionTupleHomeomorph I Y (n + 1) c.val
  change X.ρ (h : G) (b (fun i => openSubgroupRetraction H ((h : G)⁻¹ * a i))) =
    b (fun i => openSubgroupRetraction H (a i))
  have ha : (fun i => openSubgroupRetraction H ((h : G)⁻¹ * a i)) =
      fun i => h⁻¹ * openSubgroupRetraction H (a i) := by
    funext i
    exact openSubgroupRetraction_subgroup_mul H h⁻¹ (a i)
  rw [ha]
  have hc := (homogeneousCochain_tuple_equivariant I Y n c h
    (fun i => h⁻¹ * openSubgroupRetraction H (a i))).symm
  change X.ρ (h : G) (b (fun i => h⁻¹ * openSubgroupRetraction H (a i))) =
    b (fun i => h * (h⁻¹ * openSubgroupRetraction H (a i))) at hc
  simpa only [mul_inv_cancel_left] using hc

/-- A subgroup-invariant tuple has a well-defined translate on each left coset. -/
def invariantTupleTranslateOnCoset {n : ℕ} (c : C(Fin n → G, X))
    (hc : ∀ h : I, translateTuple X (h : G) c = c) : Q → C(Fin n → G, X) :=
  Quotient.lift (fun g => translateTuple X g c) fun g k h => by
    let s : I := ⟨g⁻¹ * k, QuotientGroup.leftRel_apply.mp h⟩
    have hk : g * (s : G) = k := mul_inv_cancel_left g k
    rw [← hk, translateTuple_mul, hc]

omit [CompactSpace G] in
private theorem translateTuple_invariantTupleTranslateOnCoset {n : ℕ} (c : C(Fin n → G, X))
    (hc : ∀ h : I, translateTuple X (h : G) c = c) (g : G) (q : Q) :
    translateTuple X g (invariantTupleTranslateOnCoset X H c hc q) =
      invariantTupleTranslateOnCoset X H c hc (g • q) := by
  induction q using Quotient.inductionOn with
  | h k => exact (translateTuple_mul X c g k).symm

/-- The trace sums the translates of a subgroup-invariant tuple. -/
def invariantTupleTrace {n : ℕ} (c : C(Fin n → G, X))
    (hc : ∀ h : I, translateTuple X (h : G) c = c) : C(Fin n → G, X) :=
  ∑ q : Q, invariantTupleTranslateOnCoset X H c hc q

/-- The trace is equivariant for the ambient group. -/
theorem invariantTupleTrace_equivariant {n : ℕ} (c : C(Fin n → G, X))
    (hc : ∀ h : I, translateTuple X (h : G) c = c) (g : G) (a : Fin n → G) :
    invariantTupleTrace X H c hc (fun i => g * a i) = X.ρ g (invariantTupleTrace X H c hc a) := by
  let f := invariantTupleTranslateOnCoset X H c hc
  simp only [invariantTupleTrace, ContinuousMap.sum_apply, map_sum]
  calc
    ∑ q : Q, f q (fun i => g * a i) = ∑ q : Q, f (g • q) (fun i => g * a i) :=
      (Equiv.sum_comp (MulAction.toPerm g : Equiv.Perm Q) (fun q => f q (fun i => g * a i))).symm
    _ = ∑ q : Q, X.ρ g (f q a) := by
      apply Finset.sum_congr rfl
      intro q _
      have he : translateTuple X g (f q) = f (g • q) :=
        translateTuple_invariantTupleTranslateOnCoset X H c hc g q
      rw [← he]
      change X.ρ g (f q (fun i => g⁻¹ * (g * a i))) = X.ρ g (f q a)
      simp only [inv_mul_cancel_left]

/-- Extend an original subgroup cochain along the retraction and translate it by a coset. -/
def tupleTranslateOnCoset (n : ℕ) (c : (homogeneousCochains Y).X n) :
    Q → C(Fin (n + 1) → G, X) :=
  invariantTupleTranslateOnCoset X H (extendedTuple X H n c)
    (translateTuple_extendedTuple_subgroup X H n c)

/-- The finite coset sum on the standard continuous cochains. -/
def corestrictCochain (n : ℕ) (c : (homogeneousCochains Y).X n) : (homogeneousCochains X).X n :=
  let e := extendedTuple X H n c
  let he := translateTuple_extendedTuple_subgroup X H n c
  homogeneousCochainOfTuple G X n (invariantTupleTrace X H e he)
    (invariantTupleTrace_equivariant X H e he)

/-- In tuple coordinates corestriction is the same finite coset sum. -/
theorem corestrictCochain_tuple (n : ℕ) (c : (homogeneousCochains Y).X n) (a : Fin (n + 1) → G) :
    resolutionTupleHomeomorph G X (n + 1) (corestrictCochain X H n c).val a =
      ∑ q : Q, tupleTranslateOnCoset X H n c q a := by
  let e := extendedTuple X H n c
  let he := translateTuple_extendedTuple_subgroup X H n c
  let T := invariantTupleTrace X H e he
  let hT := invariantTupleTrace_equivariant X H e he
  have ht := homogeneousCochainOfTuple_apply G X n T hT
  have hs : T a = ∑ q : Q, tupleTranslateOnCoset X H n c q a :=
    ContinuousMap.sum_apply Finset.univ (tupleTranslateOnCoset X H n c) a
  exact (congrArg (fun f : C(Fin (n + 1) → G, X) => f a) ht).trans hs

/-- Evaluate a translated extended tuple using an original coset representative. -/
theorem tupleTranslateOnCoset_mk (n : ℕ) (c : (homogeneousCochains Y).X n)
    (g : G) (a : Fin (n + 1) → G) :
    tupleTranslateOnCoset X H n c (QuotientGroup.mk g) a =
      X.ρ g (resolutionTupleHomeomorph I Y (n + 1) c.val (fun i =>
        openSubgroupRetraction H (g⁻¹ * a i))) := rfl

/-- The degreewise coset sum on the underlying modules of the original cochains. -/
def corestrictCochainHom (n : ℕ) :
    ((continuousModuleComplexFunctor I).obj Y).X n ⟶
      ((continuousModuleComplexFunctor G).obj X).X n := by
  let A := ((continuousModuleComplexFunctor I).obj Y).X n
  let B := ((continuousModuleComplexFunctor G).obj X).X n
  have hadd (c d : (homogeneousCochains Y).X n) : corestrictCochain X H n (c + d) =
      corestrictCochain X H n c + corestrictCochain X H n d := by
    apply Subtype.ext
    apply (resolutionTupleHomeomorph G X (n + 1)).injective
    apply ContinuousMap.ext
    intro a
    change resolutionTupleHomeomorph G X (n + 1) (corestrictCochain X H n (c + d)).val a =
      resolutionTupleHomeomorph G X (n + 1)
        ((corestrictCochain X H n c).val + (corestrictCochain X H n d).val) a
    rw [resolutionTupleHomeomorph_add, ContinuousMap.add_apply,
      corestrictCochain_tuple, corestrictCochain_tuple, corestrictCochain_tuple,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [tupleTranslateOnCoset_mk]
      let t (i : Fin (n + 1)) := openSubgroupRetraction H (g⁻¹ * a i)
      change X.ρ g (resolutionTupleHomeomorph I Y (n + 1) (c.val + d.val) t) =
        X.ρ g (resolutionTupleHomeomorph I Y (n + 1) c.val t) +
          X.ρ g (resolutionTupleHomeomorph I Y (n + 1) d.val t)
      rw [resolutionTupleHomeomorph_add, ContinuousMap.add_apply, map_add]
  let m : A →+ B := AddMonoidHom.mk' (corestrictCochain X H n) hadd
  letI : Module ℤ A := A.isModule
  letI : Module ℤ B := B.isModule
  let l : A →ₗ[ℤ] B :=
    { toFun := m
      map_add' := m.map_add
      map_smul' := fun r a => by
        change m (A.isModule.smul r a) = B.isModule.smul r (m a)
        exact (congrArg m (int_smul_eq_zsmul A.isModule r a)).trans
          ((map_zsmul m r a).trans (int_smul_eq_zsmul B.isModule r (m a)).symm) }
  exact ModuleCat.ofHom l

/-- The module morphism uses the same degreewise cochain. -/
theorem corestrictCochainHom_apply (n : ℕ) (c : ((continuousModuleComplexFunctor I).obj Y).X n) :
    corestrictCochainHom X H n c = corestrictCochain X H n c := rfl

/-- The actual tuple trace commutes with the homogeneous differential. -/
theorem corestrictCochain_d (n : ℕ) (c : (homogeneousCochains Y).X n) :
    (homogeneousCochains X).d n (n + 1) (corestrictCochain X H n c) =
      corestrictCochain X H (n + 1) ((homogeneousCochains Y).d n (n + 1) c) := by
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G X (n + 2)).injective
  apply ContinuousMap.ext
  intro a
  let d := (homogeneousCochains Y).d n (n + 1) c
  let b := corestrictCochain X H n c
  have hb : ((homogeneousCochains X).d n (n + 1) b).val = (TopRep.d X (n + 1)).hom b.val :=
    homogeneousCochains.d_apply X n b
  have hd : d.val = (TopRep.d Y (n + 1)).hom c.val := homogeneousCochains.d_apply Y n c
  change resolutionTupleHomeomorph G X (n + 2) ((homogeneousCochains X).d n (n + 1) b).val a = _
  rw [hb, resolutionTupleHomeomorph_d]
  have heval (i : Fin (n + 2)) :
      resolutionTupleHomeomorph G X (n + 1) b.val (fun j => a (i.succAbove j)) =
        ∑ q : Q, tupleTranslateOnCoset X H n c q (fun j => a (i.succAbove j)) :=
    corestrictCochain_tuple X H n c (fun j => a (i.succAbove j))
  have hresult :
      resolutionTupleHomeomorph G X (n + 2) (corestrictCochain X H (n + 1) d).val a =
        ∑ q : Q, tupleTranslateOnCoset X H (n + 1) d q a :=
    corestrictCochain_tuple X H (n + 1) d a
  change _ = resolutionTupleHomeomorph G X (n + 2) (corestrictCochain X H (n + 1) d).val a
  simp only [heval, hresult, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [tupleTranslateOnCoset_mk]
    change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.ρ g
      (resolutionTupleHomeomorph I Y (n + 1) c.val
        (fun j => openSubgroupRetraction H (g⁻¹ * a (i.succAbove j))))) =
      X.ρ g (resolutionTupleHomeomorph I Y (n + 2) d.val
        (fun j => openSubgroupRetraction H (g⁻¹ * a j)))
    rw [hd, resolutionTupleHomeomorph_d, map_sum]
    simp only [map_zsmul]

/-- Actual corestriction is a map of the continuous module-valued cochain complexes. -/
def corestrictContinuousModuleComplex : (continuousModuleComplexFunctor I).obj Y ⟶
    (continuousModuleComplexFunctor G).obj X where
  f n := corestrictCochainHom X H n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    apply ConcreteCategory.hom_ext
    intro x
    simp only [ConcreteCategory.comp_apply, corestrictCochainHom_apply]
    exact corestrictCochain_d X H i x

/-- Actual continuous cohomological corestriction along the open subgroup. -/
def corestrict (n : ℕ) : continuousCohomology n Y →+ continuousCohomology n X :=
  ((continuousModuleHomologyIso I Y n).inv ≫
    HomologicalComplex.homologyMap (corestrictContinuousModuleComplex X H) n ≫
    (continuousModuleHomologyIso G X n).hom).hom.toAddMonoidHom

/-- Corestriction on the original continuous cohomology maps cocycle classes
by the same finite coset sum as the cochain map. -/
theorem corestrict_π_of_cochain (n : ℕ) (c : cocycles Y n) (z : cocycles X n)
    (h : corestrictCochain X H n ((homogeneousCochains Y).iCycles n c) =
      (homogeneousCochains X).iCycles n z) :
    corestrict X H n (π Y n c) = π X n z := by
  let A := (continuousModuleComplexFunctor I).obj Y
  let B := (continuousModuleComplexFunctor G).obj X
  let f := corestrictContinuousModuleComplex X H
  let e := continuousModuleHomologyIso I Y n
  let e' := continuousModuleHomologyIso G X n
  have hc : e.inv (π Y n c) = A.homologyπ n (moduleCycle Y n c) := by
    rw [← moduleCycle_homologyπ Y n c, Iso.hom_inv_id_apply]
  have hz : HomologicalComplex.cyclesMap f n (moduleCycle Y n c) = moduleCycle X n z := by
    apply (ModuleCat.mono_iff_injective (B.iCycles n)).mp inferInstance
    have hh := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) (moduleCycle Y n c)
    simp only [ConcreteCategory.comp_apply] at hh
    have hfn : f.f n (A.iCycles n (moduleCycle Y n c)) =
        corestrictCochain X H n (A.iCycles n (moduleCycle Y n c)) :=
      corestrictCochainHom_apply X H n (A.iCycles n (moduleCycle Y n c))
    have hc' := congrArg (corestrictCochain X H n) (moduleCycle_iCycles Y n c)
    exact hh.trans (hfn.trans (hc'.trans (h.trans (moduleCycle_iCycles X n z).symm)))
  have hnat : HomologicalComplex.homologyMap f n (A.homologyπ n (moduleCycle Y n c)) =
      B.homologyπ n (HomologicalComplex.cyclesMap f n (moduleCycle Y n c)) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) (moduleCycle Y n c)
  change e'.hom (HomologicalComplex.homologyMap f n (e.inv (π Y n c))) = _
  rw [hc, hnat, hz, moduleCycle_homologyπ]

/-- The ordinary restriction on continuous homogeneous cohomology along the open subgroup. -/
def openRestriction (n : ℕ) : continuousCohomology n X →+ continuousCohomology n Y :=
  (map (ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup : I →ₜ* G) (𝟙 Y) n).hom.toLinearMap
    |>.toAddMonoidHom

/-- Degree-zero restriction keeps the same coefficient in the larger fixed submodule. -/
theorem zeroIso_hom_openRestriction_val (x : continuousCohomology 0 X) :
    ((zeroIso Y).hom (openRestriction X H 0 x)).val = ((zeroIso X).hom x).val := by
  obtain ⟨z, rfl⟩ := π_surjective X 0 x
  let ι : I →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup
  have h : openRestriction X H 0 (π X 0 z) = π Y 0 (cocyclesMap ι (𝟙 Y) 0 z) :=
    ConcreteCategory.congr_hom (π_map ι (𝟙 Y) 0) z
  rw [h, zeroIso_hom_π_val, zeroIso_hom_π_val, cochainOfMappedCocycle]
  exact resolutionTupleHomeomorph_cochainsMap G X Y ι (𝟙 Y) 0
    ((homogeneousCochains X).iCycles 0 z) (fun _ => 1)

/-- An equivariant retraction prism gives the index law on the original cocycle class. -/
theorem corestrict_openRestriction_of_tuplePrism (n : ℕ) (z : cocycles X (n + 1))
    (P : C(Fin (n + 1) → G, X))
    (hP : ∀ h : I, translateTuple X (h : G) P = P)
    (hbound : ∀ a : Fin (n + 2) → G, (∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • P (fun j => a (i.succAbove j))) =
          resolutionTupleHomeomorph G X (n + 2) ((homogeneousCochains X).iCycles (n + 1) z).val a -
            resolutionTupleHomeomorph G X (n + 2) ((homogeneousCochains X).iCycles (n + 1) z).val
              (fun i => (openSubgroupRetraction H (a i) : G))) :
    corestrict X H (n + 1) (openRestriction X H (n + 1) (π X (n + 1) z)) =
      H.toSubgroup.index • π X (n + 1) z := by
  let C := homogeneousCochains X
  let D := homogeneousCochains Y
  let ι : I →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup
  let c := cocyclesMap ι (𝟙 Y) (n + 1) z
  let z₀ := C.iCycles (n + 1) z
  let Z := resolutionTupleHomeomorph G X (n + 2) z₀.val
  let w := homogeneousCochainOfTuple G X n (invariantTupleTrace X H P hP)
    (invariantTupleTrace_equivariant X H P hP)
  let dw := C.d n (n + 1) w
  let e := corestrictCochain X H (n + 1) (D.iCycles (n + 1) c)
  have hw (a : Fin (n + 1) → G) : resolutionTupleHomeomorph G X (n + 1) w.val a =
      ∑ q : Q, invariantTupleTranslateOnCoset X H P hP q a := by
    change resolutionTupleHomeomorph G X (n + 1) (homogeneousCochainOfTuple G X n
      (invariantTupleTrace X H P hP) (invariantTupleTrace_equivariant X H P hP)).val a = _
    rw [homogeneousCochainOfTuple_apply]
    simp only [invariantTupleTrace, ContinuousMap.sum_apply]
  have hZ (b : Fin (n + 2) → I) :
      resolutionTupleHomeomorph I Y (n + 2) (D.iCycles (n + 1) c).val b =
        Z (fun i => (b i : G)) := by
    change resolutionTupleHomeomorph I Y (n + 2)
      (D.iCycles (n + 1) (cocyclesMap ι (𝟙 Y) (n + 1) z)).val b = _
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
      resolutionTupleHomeomorph_cochainsMap, ConcreteCategory.id_apply]
    rfl
  have heach (q : Q) (a : Fin (n + 2) → G) : (∑ i : Fin (n + 2),
      (-1 : ℤ) ^ (i : ℕ) • invariantTupleTranslateOnCoset X H P hP q (fun j => a (i.succAbove j))) =
      Z a - tupleTranslateOnCoset X H (n + 1) (D.iCycles (n + 1) c) q a := by
    induction q using Quotient.inductionOn with
    | h g =>
      let t (i : Fin (n + 2)) := g⁻¹ * a i
      change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        X.ρ g (P (fun j => t (i.succAbove j)))) =
        Z a - X.ρ g (resolutionTupleHomeomorph I Y (n + 2) (D.iCycles (n + 1) c).val
          (fun j => openSubgroupRetraction H (t j)))
      simp only [← map_zsmul]
      rw [← map_sum, hbound t, map_sub, hZ]
      have ha : (fun i => g * t i) = a := funext fun i => mul_inv_cancel_left g (a i)
      have h := homogeneousCochain_tuple_equivariant G X (n + 1) z₀ g t
      change Z (fun i => g * t i) = X.ρ g (Z t) at h
      rw [ha] at h
      rw [← h]
  have hdw : dw = H.toSubgroup.index • z₀ - e := by
    apply Subtype.ext
    apply (resolutionTupleHomeomorph G X (n + 2)).injective
    apply ContinuousMap.ext
    intro a
    have h : dw.val = (TopRep.d X (n + 1)).hom w.val := homogeneousCochains.d_apply X n w
    rw [h, resolutionTupleHomeomorph_d]
    simp only [hw, Finset.smul_sum]
    rw [Finset.sum_comm]
    simp only [heach, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← H.toSubgroup.index_eq_card]
    change H.toSubgroup.index • Z a -
      ∑ q : Q, tupleTranslateOnCoset X H (n + 1) (D.iCycles (n + 1) c) q a =
      (resolutionTupleContinuousLinearEquiv G X (n + 2)) (H.toSubgroup.index • z₀.val - e.val) a
    rw [map_sub, map_nsmul, ContinuousMap.sub_apply, ContinuousMap.nsmul_apply]
    have hZ' : resolutionTupleContinuousLinearEquiv G X (n + 2) z₀.val a = Z a := rfl
    have he : resolutionTupleContinuousLinearEquiv G X (n + 2) e.val a =
        ∑ q : Q, tupleTranslateOnCoset X H (n + 1) (D.iCycles (n + 1) c) q a :=
      corestrictCochain_tuple X H (n + 1) (D.iCycles (n + 1) c) a
    rw [hZ', he]
  let v := H.toSubgroup.index • z - C.toCycles n (n + 1) w
  have hv : e = C.iCycles (n + 1) v := by
    change e = C.iCycles (n + 1) (H.toSubgroup.index • z - C.toCycles n (n + 1) w)
    rw [map_sub, map_nsmul]
    have h := ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) w
    change C.iCycles (n + 1) (C.toCycles n (n + 1) w) = dw at h
    rw [h, hdw, sub_sub_cancel]
  have hc : openRestriction X H (n + 1) (π X (n + 1) z) = π Y (n + 1) c :=
    ConcreteCategory.congr_hom (π_map ι (𝟙 Y) (n + 1)) z
  rw [hc, corestrict_π_of_cochain X H (n + 1) c v hv]
  change π X (n + 1) (H.toSubgroup.index • z - C.toCycles n (n + 1) w) = _
  have h := ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) w
  change π X (n + 1) (C.toCycles n (n + 1) w) = 0 at h
  rw [map_sub, map_nsmul, h, sub_zero]

/-- On degree-two classes the actual coset sum after restriction is the subgroup index. -/
theorem corestrict_openRestriction_two (x : continuousCohomology 2 X) :
    corestrict X H 2 (openRestriction X H 2 x) = H.toSubgroup.index • x := by
  let : Module ℤ X := X.hV2
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  let C := homogeneousCochains X
  let D := homogeneousCochains Y
  let ι : I →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup
  let c := cocyclesMap ι (𝟙 Y) 2 z
  let z₀ := C.iCycles 2 z
  let Z := z₀.val
  let p₀ := openSubgroupPrimitiveExtension H Z 0
  let P := resolutionTupleHomeomorph G X 2 p₀
  have hp (h : I) : translateTuple X (h : G) P = P := by
    apply ContinuousMap.ext
    intro a
    change X.ρ (h : G) (p₀ ((h : G)⁻¹ * a 0) ((h : G)⁻¹ * a 1)) = p₀ (a 0) (a 1)
    have he := openSubgroupPrimitiveExtension_equivariant X.ρ H Z
      (fun u a b c => degreeTwo_equivariant X z (u : G) a b c)
      0 (by intro u a b; simp only [ContinuousMap.zero_apply, map_zero]) h
      ((h : G)⁻¹ * a 0) ((h : G)⁻¹ * a 1)
    simpa only [mul_inv_cancel_left] using he
  let p := homogeneousCochainOfTuple G X 1 (invariantTupleTrace X H P hp)
    (invariantTupleTrace_equivariant X H P hp)
  let dp := C.d 1 2 p
  let e := corestrictCochain X H 2 (D.iCycles 2 c)
  have hpval (a b : G) :
      p.val a b = ∑ q : Q, invariantTupleTranslateOnCoset X H P hp q ![a, b] := by
    change resolutionTupleHomeomorph G X 2 p.val ![a, b] = _
    change resolutionTupleHomeomorph G X 2 (homogeneousCochainOfTuple G X 1
      (invariantTupleTrace X H P hp) (invariantTupleTrace_equivariant X H P hp)).val ![a, b] = _
    rw [homogeneousCochainOfTuple_apply]
    simp only [invariantTupleTrace, ContinuousMap.sum_apply]
  have heval (a b c' : G) :
      e.val a b c' = ∑ q : Q, tupleTranslateOnCoset X H 2 (D.iCycles 2 c) q ![a, b, c'] :=
    corestrictCochain_tuple X H 2 (D.iCycles 2 c) ![a, b, c']
  have hZ (a b c' : I) : (D.iCycles 2 c).val a b c' = Z a b c' :=
    mappedRelativeCocycle_apply ι (𝟙 Y) z a b c'
  have heach (q : Q) (a b c' : G) :
      invariantTupleTranslateOnCoset X H P hp q ![b, c'] -
        invariantTupleTranslateOnCoset X H P hp q ![a, c'] +
        invariantTupleTranslateOnCoset X H P hp q ![a, b] =
      Z a b c' - tupleTranslateOnCoset X H 2 (D.iCycles 2 c) q ![a, b, c'] := by
    induction q using Quotient.inductionOn with
    | h g =>
      let r := openSubgroupRetraction H
      rw [tupleTranslateOnCoset_mk]
      change X.ρ g (p₀ (g⁻¹ * b) (g⁻¹ * c')) - X.ρ g (p₀ (g⁻¹ * a) (g⁻¹ * c')) +
        X.ρ g (p₀ (g⁻¹ * a) (g⁻¹ * b)) =
        Z a b c' - X.ρ g ((D.iCycles 2 c).val (r (g⁻¹ * a)) (r (g⁻¹ * b)) (r (g⁻¹ * c')))
      rw [← map_sub, ← map_add, openSubgroupPrism_boundary H Z (degreeTwo_cocycle_equation X z),
        map_sub, hZ]
      have h := degreeTwo_equivariant X z g (g⁻¹ * a) (g⁻¹ * b) (g⁻¹ * c')
      change X.ρ g (Z (g⁻¹ * a) (g⁻¹ * b) (g⁻¹ * c')) = _ at h
      rw [mul_inv_cancel_left, mul_inv_cancel_left, mul_inv_cancel_left] at h
      rw [h]
  have hdp : dp = H.toSubgroup.index • z₀ - e := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro c'
    have hd := congrArg (fun w => w a b c') (homogeneousCochains.d_apply X 1 p)
    change dp.val a b c' = (H.toSubgroup.index : ℕ) • Z a b c' - e.val a b c'
    rw [hd]
    change p.val b c' - (p.val a c' - p.val a b) = _
    rw [show p.val b c' - (p.val a c' - p.val a b) =
      p.val b c' - p.val a c' + p.val a b from by abel,
      hpval, hpval, hpval, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    simp only [heach, Finset.sum_sub_distrib, heval, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← H.toSubgroup.index_eq_card]
  let w : cocycles X 2 := H.toSubgroup.index • z - C.toCycles 1 2 p
  have hw : e = C.iCycles 2 w := by
    change e = C.iCycles 2 (H.toSubgroup.index • z - C.toCycles 1 2 p)
    rw [map_sub, map_nsmul]
    have h := ConcreteCategory.congr_hom (C.toCycles_i 1 2) p
    change C.iCycles 2 (C.toCycles 1 2 p) = dp at h
    rw [h, hdp, sub_sub_cancel]
  have hc : openRestriction X H 2 (π X 2 z) = π Y 2 c :=
    ConcreteCategory.congr_hom (π_map ι (𝟙 Y) 2) z
  rw [hc, corestrict_π_of_cochain X H 2 c w hw]
  change π X 2 (H.toSubgroup.index • z - C.toCycles 1 2 p) = _
  rw [map_sub, map_nsmul]
  have h := ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) p
  change π X 2 (C.toCycles 1 2 p) = 0 at h
  rw [h, sub_zero]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
private theorem tupleThree_signedFaces (f : (Fin 3 → G) → X) (a b c d : G) :
    (∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • f (fun j => (![a, b, c, d] : Fin 4 → G) (i.succAbove j))) =
      f ![b, c, d] - f ![a, c, d] + f ![a, b, d] - f ![a, b, c] := by
  have hface0 : (fun j : Fin 3 => (![a, b, c, d] : Fin 4 → G) ((0 : Fin 4).succAbove j)) =
      ![b, c, d] := by
    funext j
    fin_cases j <;> rfl
  have hface1 : (fun j : Fin 3 => (![a, b, c, d] : Fin 4 → G) ((1 : Fin 4).succAbove j)) =
      ![a, c, d] := by
    funext j
    fin_cases j <;> rfl
  have hface2 : (fun j : Fin 3 => (![a, b, c, d] : Fin 4 → G) ((2 : Fin 4).succAbove j)) =
      ![a, b, d] := by
    funext j
    fin_cases j <;> rfl
  have hface3 : (fun j : Fin 3 => (![a, b, c, d] : Fin 4 → G) ((3 : Fin 4).succAbove j)) =
      ![a, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [Fin.sum_univ_four, hface0, hface1, hface2, hface3]
  change (-1 : ℤ) ^ (0 : ℕ) • f ![b, c, d] + (-1 : ℤ) ^ (1 : ℕ) • f ![a, c, d] +
      (-1 : ℤ) ^ (2 : ℕ) • f ![a, b, d] + (-1 : ℤ) ^ (3 : ℕ) • f ![a, b, c] = _
  have h₂ : (-1 : ℤ) ^ (2 : ℕ) = 1 := by norm_num
  have h₃ : (-1 : ℤ) ^ (3 : ℕ) = -1 := by norm_num
  simp only [pow_zero, pow_one, h₂, h₃, one_zsmul, neg_one_zsmul, sub_eq_add_neg]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
private theorem tupleFour_signedFaces (f : (Fin 4 → G) → X) (a b c d e : G) :
    (∑ i : Fin 5, (-1 : ℤ) ^ (i : ℕ) •
      f (fun j => (![a, b, c, d, e] : Fin 5 → G) (i.succAbove j))) =
      f ![b, c, d, e] - f ![a, c, d, e] + f ![a, b, d, e] - f ![a, b, c, e] + f ![a, b, c, d] := by
  have hface0 : (fun j : Fin 4 => (![a, b, c, d, e] : Fin 5 → G) ((0 : Fin 5).succAbove j)) =
      ![b, c, d, e] := by
    funext j
    fin_cases j <;> rfl
  have hface1 : (fun j : Fin 4 => (![a, b, c, d, e] : Fin 5 → G) ((1 : Fin 5).succAbove j)) =
      ![a, c, d, e] := by
    funext j
    fin_cases j <;> rfl
  have hface2 : (fun j : Fin 4 => (![a, b, c, d, e] : Fin 5 → G) ((2 : Fin 5).succAbove j)) =
      ![a, b, d, e] := by
    funext j
    fin_cases j <;> rfl
  have hface3 : (fun j : Fin 4 => (![a, b, c, d, e] : Fin 5 → G) ((3 : Fin 5).succAbove j)) =
      ![a, b, c, e] := by
    funext j
    fin_cases j <;> rfl
  have hface4 : (fun j : Fin 4 => (![a, b, c, d, e] : Fin 5 → G) ((4 : Fin 5).succAbove j)) =
      ![a, b, c, d] := by
    funext j
    fin_cases j <;> rfl
  rw [Fin.sum_univ_five, hface0, hface1, hface2, hface3, hface4]
  change (-1 : ℤ) ^ (0 : ℕ) • f ![b, c, d, e] + (-1 : ℤ) ^ (1 : ℕ) • f ![a, c, d, e] +
      (-1 : ℤ) ^ (2 : ℕ) • f ![a, b, d, e] + (-1 : ℤ) ^ (3 : ℕ) • f ![a, b, c, e] +
      (-1 : ℤ) ^ (4 : ℕ) • f ![a, b, c, d] = _
  have h₂ : (-1 : ℤ) ^ (2 : ℕ) = 1 := by norm_num
  have h₃ : (-1 : ℤ) ^ (3 : ℕ) = -1 := by norm_num
  have h₄ : (-1 : ℤ) ^ (4 : ℕ) = 1 := by norm_num
  simp only [pow_zero, pow_one, h₂, h₃, h₄, one_zsmul, neg_one_zsmul, sub_eq_add_neg]

omit [CompactSpace G] in
private theorem degreeThree_cocycle_differential (z : cocycles X 3) :
    (TopRep.d X 4).hom ((homogeneousCochains X).iCycles 3 z).val = 0 := by
  let C := homogeneousCochains X
  let c : C.X 3 := (C.iCycles 3).hom z
  have hc : (C.d 3 4).hom c = 0 := by
    have h := congrArg (fun f => TopModuleCat.Hom.hom f z) (C.iCycles_d 3 4)
    simpa only [c, TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
      TopModuleCat.hom_zero, _root_.zero_apply] using h
  have hd := homogeneousCochains.d_apply X 3 c
  exact hd.symm.trans (congrArg Subtype.val hc)

/-- In degree three the actual coset sum after restriction is the index.
The primitive uses the three insertions of the subgroup retraction. -/
theorem corestrict_openRestriction_three (x : continuousCohomology 3 X) :
    corestrict X H 3 (openRestriction X H 3 x) = H.toSubgroup.index • x := by
  obtain ⟨z, rfl⟩ := π_surjective X 3 x
  let z₀ := (homogeneousCochains X).iCycles 3 z
  let Z := resolutionTupleHomeomorph G X 4 z₀.val
  let r (g : G) : G := (openSubgroupRetraction H g : G)
  have hr : Continuous r := continuous_subtype_val.comp (openSubgroupRetraction H).continuous
  have hrh (h : I) (g : G) : r ((h : G) * g) = (h : G) * r g :=
    congrArg Subtype.val (openSubgroupRetraction_subgroup_mul H h g)
  let L (a : Fin 3 → G) : Fin 4 → G := ![a 0, r (a 0), r (a 1), r (a 2)]
  let M (a : Fin 3 → G) : Fin 4 → G := ![a 0, a 1, r (a 1), r (a 2)]
  let N (a : Fin 3 → G) : Fin 4 → G := ![a 0, a 1, a 2, r (a 2)]
  have hL : Continuous L := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact hr.comp (continuous_apply 0)
    · exact hr.comp (continuous_apply 1)
    · exact hr.comp (continuous_apply 2)
  have hM : Continuous M := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact hr.comp (continuous_apply 1)
    · exact hr.comp (continuous_apply 2)
  have hN : Continuous N := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_apply 2
    · exact hr.comp (continuous_apply 2)
  let P : C(Fin 3 → G, X) := ⟨fun a => -Z (L a) + Z (M a) - Z (N a),
    ((Z.continuous.comp hL).neg.add (Z.continuous.comp hM)).sub (Z.continuous.comp hN)⟩
  have hp (h : I) (a : Fin 3 → G) :
      X.ρ (h : G) (P a) = P (fun i => (h : G) * a i) := by
    let s (i : Fin 3) := (h : G) * a i
    have hL' : (fun i => (h : G) * L a i) = L s := by
      funext i
      fin_cases i
      · rfl
      · exact (hrh h (a 0)).symm
      · exact (hrh h (a 1)).symm
      · exact (hrh h (a 2)).symm
    have hM' : (fun i => (h : G) * M a i) = M s := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact (hrh h (a 1)).symm
      · exact (hrh h (a 2)).symm
    have hN' : (fun i => (h : G) * N a i) = N s := by
      funext i
      fin_cases i
      · rfl
      · rfl
      · rfl
      · exact (hrh h (a 2)).symm
    have hact (t : Fin 4 → G) : X.ρ (h : G) (Z t) = Z (fun i => (h : G) * t i) :=
      (homogeneousCochain_tuple_equivariant G X 3 z₀ (h : G) t).symm
    change X.ρ (h : G) (-Z (L a) + Z (M a) - Z (N a)) = -Z (L s) + Z (M s) - Z (N s)
    simp only [map_sub, map_add, map_neg, hact, hL', hM', hN']
  have hp' (h : I) : translateTuple X (h : G) P = P := by
    apply ContinuousMap.ext
    intro a
    change X.ρ (h : G) (P (fun i => (h : G)⁻¹ * a i)) = P a
    have hh := hp h (fun i => (h : G)⁻¹ * a i)
    simpa only [mul_inv_cancel_left] using hh
  apply corestrict_openRestriction_of_tuplePrism X H 2 z P hp'
  intro t
  let Z' := Z
  let a := t 0
  let b := t 1
  let c := t 2
  let d := t 3
  have ht : (![a, b, c, d] : Fin 4 → G) = t := by
    funext i
    fin_cases i <;> rfl
  have hrt : (fun i => r ((![a, b, c, d] : Fin 4 → G) i)) = ![r a, r b, r c, r d] := by
    funext i
    fin_cases i <;> rfl
  change (∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • P (fun j => t (i.succAbove j))) =
    Z' t - Z' (fun i => r (t i))
  rw [← ht, hrt, tupleThree_signedFaces]
  let W (a b c d : G) := Z' ![a, b, c, d]
  let B (a b c d e : G) :=
    W b c d e - W a c d e + W a b d e - W a b c e + W a b c d
  have hZ (a b c d e : G) : B a b c d e = 0 := by
    have h₀ := degreeThree_cocycle_differential X z
    have h := congrArg (fun q => (resolutionTupleContinuousLinearEquiv G X 5 q) ![a, b, c, d, e]) h₀
    change resolutionTupleHomeomorph G X 5 ((TopRep.d X 4).hom z₀.val) ![a, b, c, d, e] = _ at h
    rw [resolutionTupleHomeomorph_d, tupleFour_signedFaces, map_zero, ContinuousMap.zero_apply] at h
    exact h
  have hP (a b c : G) : P ![a, b, c] =
      -W a (r a) (r b) (r c) + W a b (r b) (r c) - W a b c (r c) := rfl
  rw [hP, hP, hP, hP]
  change _ = W a b c d - W (r a) (r b) (r c) (r d)
  calc
    _ = W a b c d - W (r a) (r b) (r c) (r d) +
        B a (r a) (r b) (r c) (r d) - B a b (r b) (r c) (r d) +
        B a b c (r c) (r d) - B a b c d (r d) := by
      dsimp only [B]
      abel
    _ = _ := by simp only [hZ, add_zero, sub_zero]

/-- Degree-three vanishing descends from an actual open subgroup of
prime-to-p index for coefficients annihilated by p. -/
theorem H3_eq_zero_of_primeToIndex_open_restriction (p : ℕ) [Fact p.Prime]
    (hpX : ∀ x : X, p • x = 0) (hindex : ¬ p ∣ H.toSubgroup.index)
    (hH : ∀ w : continuousCohomology 3 Y, w = 0) (x : continuousCohomology 3 X) :
    x = 0 := by
  by_contra hx
  have hp := nsmul_continuousCohomology_eq_zero_of_coefficients X p hpX 3 x
  have ho : addOrderOf x = p := addOrderOf_eq_prime hp hx
  have hi : H.toSubgroup.index • x = 0 := by
    exact (corestrict_openRestriction_three X H x).symm.trans
      ((congrArg (corestrict X H 3) (hH (openRestriction X H 3 x))).trans (map_zero _))
  exact hindex (ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hi)

omit [CompactSpace G] in
/-- A constant tuple with an invariant coefficient is fixed by the subgroup. -/
theorem translateConstantTuple_subgroup (b : TopRep.invariants Y) (h : I) :
    translateTuple X (h : G) (ContinuousMap.const (Fin 0 → G) b.val) =
      ContinuousMap.const (Fin 0 → G) b.val := by
  apply ContinuousMap.ext
  intro a
  exact b.property h

private def coefficientOnCoset (b : TopRep.invariants Y) (q : Q) : X :=
  invariantTupleTranslateOnCoset X H (ContinuousMap.const (Fin 0 → G) b.val)
    (translateConstantTuple_subgroup X H b) q Fin.elim0

/-- The norm of an open-subgroup invariant is the sum of its translates over
the finite left coset space. -/
def openSubgroupNorm (b : TopRep.invariants Y) : X.invariants := by
  let c := ContinuousMap.const (Fin 0 → G) b.val
  let hc := translateConstantTuple_subgroup X H b
  refine ⟨invariantTupleTrace X H c hc Fin.elim0, fun g => ?_⟩
  have h := invariantTupleTrace_equivariant X H c hc g Fin.elim0
  have he : (fun i : Fin 0 => g * Fin.elim0 i) = (Fin.elim0 : Fin 0 → G) :=
    funext fun i => Fin.elim0 i
  rw [he] at h
  exact h.symm

private theorem openSubgroupNorm_val' (b : TopRep.invariants Y) :
    (openSubgroupNorm X H b).val = ∑ q : Q, coefficientOnCoset X H b q := by
  change (∑ q : Q, invariantTupleTranslateOnCoset X H (ContinuousMap.const (Fin 0 → G) b.val)
    (translateConstantTuple_subgroup X H b) q) Fin.elim0 = _
  exact ContinuousMap.sum_apply _ _ _

/-- The norm evaluates by any representatives of the actual quotient. -/
theorem openSubgroupNorm_val (b : TopRep.invariants Y) (r : Q → G)
    (hr : ∀ q, QuotientGroup.mk (r q) = q) :
    (openSubgroupNorm X H b).val = ∑ q : Q, X.ρ (r q) b.val := by
  rw [openSubgroupNorm_val']
  apply Finset.sum_congr rfl
  intro q _
  calc
    coefficientOnCoset X H b q = coefficientOnCoset X H b (QuotientGroup.mk (r q)) :=
      congrArg (coefficientOnCoset X H b) (hr q).symm
    _ = _ := rfl

/-- Under the degree-zero invariant comparison, actual corestriction is the coset norm. -/
theorem corestrict_zero_eq_invariantNorm (x : continuousCohomology 0 Y) :
    (zeroIso X).hom (corestrict X H 0 x) = openSubgroupNorm X H ((zeroIso Y).hom x) := by
  obtain ⟨z, rfl⟩ := π_surjective Y 0 x
  let c := (homogeneousCochains Y).iCycles 0 z
  let b := (zeroIso Y).hom (π Y 0 z)
  let w := fixedCocycleZero X (openSubgroupNorm X H b)
  have hw : corestrictCochain X H 0 c = (homogeneousCochains X).iCycles 0 w := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    rw [fixedCocycleZero_apply X (openSubgroupNorm X H b) a]
    let t : Fin 1 → G := fun _ => a
    have ht : resolutionTupleHomeomorph G X 1 (corestrictCochain X H 0 c).val t =
        (corestrictCochain X H 0 c).val a := by
      rw [resolutionTupleHomeomorph_succ_apply, resolutionTupleHomeomorph_zero_apply]
    rw [← ht, corestrictCochain_tuple, openSubgroupNorm_val' X H]
    apply Finset.sum_congr rfl
    intro q _
    induction q using Quotient.inductionOn with
    | h g =>
      change tupleTranslateOnCoset X H 0 c (QuotientGroup.mk g) t = X.ρ g b.val
      rw [tupleTranslateOnCoset_mk, resolutionTupleHomeomorph_succ_apply,
        resolutionTupleHomeomorph_zero_apply]
      exact congrArg (X.ρ g) (zeroIso_hom_π_apply Y z _).symm
  rw [corestrict_π_of_cochain X H 0 z w hw]
  apply Subtype.ext
  exact (zeroIso_hom_π_val X w).trans (fixedCocycleZero_apply X (openSubgroupNorm X H b) 1)

/-- Corestriction after restriction multiplies degree-zero cohomology by the index. -/
theorem corestrict_openRestriction_zero (x : continuousCohomology 0 X) :
    corestrict X H 0 (openRestriction X H 0 x) = H.toSubgroup.index • x := by
  apply (ConcreteCategory.bijective_of_isIso (zeroIso X).hom).1
  rw [corestrict_zero_eq_invariantNorm]
  apply Subtype.ext
  let b := (zeroIso X).hom x
  change (openSubgroupNorm X H ((zeroIso Y).hom (openRestriction X H 0 x))).val =
    ((zeroIso X).hom.hom (H.toSubgroup.index • x)).val
  rw [openSubgroupNorm_val X H _ Quotient.out Quotient.out_eq,
    zeroIso_hom_openRestriction_val X H, map_nsmul]
  change (∑ q : Q, X.ρ (Quotient.out q) b.val) = H.toSubgroup.index • b.val
  calc
    _ = ∑ _ : Q, b.val := Finset.sum_congr rfl (fun q _ => b.property (Quotient.out q))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← H.toSubgroup.index_eq_card]

section Projection

variable {A B : TopRep.{u} ℤ G}
    (p : A →ₗ[ℤ] B →ₗ[ℤ] X)
    (hp : Continuous (fun t : A × B => p t.1 t.2))
    (he : ∀ (g : G) (a : A) (b : B), p (A.ρ g a) (B.ρ g b) = X.ρ g (p a b))

local notation "RA" => TopRep.res H.toSubgroup.subtype A
local notation "RB" => TopRep.res H.toSubgroup.subtype B

include he in
private theorem corestrict_invariantPairing_coset
    (b : TopRep.invariants RB) (z : cocycles A 2) (c : cocycles Y 2)
    (p₀ : C(G, C(G, A)))
    (hp₀ : ∀ a₀ a₁ a₂ : G, p₀ a₁ a₂ - p₀ a₀ a₂ + p₀ a₀ a₁ =
      ((homogeneousCochains A).iCycles 2 z).val a₀ a₁ a₂ -
        ((homogeneousCochains A).iCycles 2 z).val
          (openSubgroupRetraction H a₀) (openSubgroupRetraction H a₁)
          (openSubgroupRetraction H a₂))
    (P : C(Fin 2 → G, X)) (hP : ∀ h : I, translateTuple X (h : G) P = P)
    (hPeval : ∀ a₀ a₁ : G, P ![a₀, a₁] = p (p₀ a₀ a₁) b.val)
    (hceval : ∀ a₀ a₁ a₂ : I, ((homogeneousCochains Y).iCycles 2 c).val a₀ a₁ a₂ =
      p (((homogeneousCochains A).iCycles 2 z).val a₀ a₁ a₂) b.val)
    (q : Q) (a₀ a₁ a₂ : G) :
    invariantTupleTranslateOnCoset X H P hP q ![a₁, a₂] -
        invariantTupleTranslateOnCoset X H P hP q ![a₀, a₂] +
        invariantTupleTranslateOnCoset X H P hP q ![a₀, a₁] =
      p (((homogeneousCochains A).iCycles 2 z).val a₀ a₁ a₂) (coefficientOnCoset B H b q) -
        tupleTranslateOnCoset X H 2 ((homogeneousCochains Y).iCycles 2 c) q ![a₀, a₁, a₂] := by
  induction q using Quotient.inductionOn with
  | h g =>
    let D := homogeneousCochains Y
    let Z := ((homogeneousCochains A).iCycles 2 z).val
    let r := openSubgroupRetraction H
    let u₀ := g⁻¹ * a₀
    let u₁ := g⁻¹ * a₁
    let u₂ := g⁻¹ * a₂
    let y := B.ρ g b.val
    let s : A →+ X := AddMonoidHom.mk' (fun a => p a y) (fun a a' =>
      congrArg (fun f : B →ₗ[ℤ] X => f y) (map_add p a a'))
    have hleft (a a' : G) :
        invariantTupleTranslateOnCoset X H P hP (QuotientGroup.mk g) ![a, a'] =
          X.ρ g (P ![g⁻¹ * a, g⁻¹ * a']) := by
      change X.ρ g (P (fun i => g⁻¹ * ![a, a'] i)) = _
      apply congrArg (fun t : Fin 2 → G => X.ρ g (P t))
      funext i
      fin_cases i <;> rfl
    have hargs : (fun i : Fin 3 => r (g⁻¹ * ![a₀, a₁, a₂] i)) = ![r u₀, r u₁, r u₂] := by
      funext i
      fin_cases i <;> rfl
    rw [hleft, hleft, hleft, tupleTranslateOnCoset_mk, hargs]
    change X.ρ g (P ![u₁, u₂]) - X.ρ g (P ![u₀, u₂]) +
      X.ρ g (P ![u₀, u₁]) = s (Z a₀ a₁ a₂) -
      X.ρ g ((D.iCycles 2 c).val (r u₀) (r u₁) (r u₂))
    rw [hPeval, hPeval, hPeval, hceval]
    simp only [← he]
    change s (A.ρ g (p₀ u₁ u₂)) - s (A.ρ g (p₀ u₀ u₂)) + s (A.ρ g (p₀ u₀ u₁)) =
      s (Z a₀ a₁ a₂) - s (A.ρ g (Z (r u₀) (r u₁) (r u₂)))
    have h := degreeTwo_equivariant A z g u₀ u₁ u₂
    change A.ρ g (Z u₀ u₁ u₂) = Z (g * (g⁻¹ * a₀)) (g * (g⁻¹ * a₁)) (g * (g⁻¹ * a₂)) at h
    rw [mul_inv_cancel_left, mul_inv_cancel_left, mul_inv_cancel_left] at h
    calc
      _ = s (A.ρ g (p₀ u₁ u₂ - p₀ u₀ u₂ + p₀ u₀ u₁)) := by
        simp only [map_add, map_sub]
      _ = _ := by
        have hp₀' : p₀ u₁ u₂ - p₀ u₀ u₂ + p₀ u₀ u₁ =
            Z u₀ u₁ u₂ - Z (r u₀) (r u₁) (r u₂) := hp₀ u₀ u₁ u₂
        rw [hp₀', map_sub, map_sub, h]

include hp he in
private theorem corestrict_invariantPairing_boundary
    (b : TopRep.invariants RB) (z : cocycles A 2) (c : cocycles Y 2) (d : cocycles X 2)
    (hceval : ∀ a₀ a₁ a₂ : I, ((homogeneousCochains Y).iCycles 2 c).val a₀ a₁ a₂ =
      p (((homogeneousCochains A).iCycles 2 z).val a₀ a₁ a₂) b.val)
    (hdeval : ∀ a₀ a₁ a₂ : G, ((homogeneousCochains X).iCycles 2 d).val a₀ a₁ a₂ =
      p (((homogeneousCochains A).iCycles 2 z).val a₀ a₁ a₂) (openSubgroupNorm B H b).val) :
    ∃ w : (homogeneousCochains X).X 1, (homogeneousCochains X).d 1 2 w =
      (homogeneousCochains X).iCycles 2 d -
        corestrictCochain X H 2 ((homogeneousCochains Y).iCycles 2 c) := by
  let C := homogeneousCochains X
  let D := homogeneousCochains Y
  let Z := ((homogeneousCochains A).iCycles 2 z).val
  let p₀ := openSubgroupPrimitiveExtension H Z 0
  let P : C(Fin 2 → G, X) :=
    ⟨fun a => p (resolutionTupleHomeomorph G A 2 p₀ a) b.val,
      hp.comp ((resolutionTupleHomeomorph G A 2 p₀).continuous.prodMk continuous_const)⟩
  have hP (h : I) : translateTuple X (h : G) P = P := by
    apply ContinuousMap.ext
    intro a
    change X.ρ (h : G) (p (p₀ ((h : G)⁻¹ * a 0) ((h : G)⁻¹ * a 1)) b.val) =
      p (p₀ (a 0) (a 1)) b.val
    have h₀ : A.ρ (h : G) (p₀ ((h : G)⁻¹ * a 0) ((h : G)⁻¹ * a 1)) =
        p₀ ((h : G) * ((h : G)⁻¹ * a 0)) ((h : G) * ((h : G)⁻¹ * a 1)) := by
      let : Module ℤ A := A.hV2
      exact openSubgroupPrimitiveExtension_equivariant A.ρ H Z
        (fun u a₀ b₀ c₀ => degreeTwo_equivariant A z (u : G) a₀ b₀ c₀)
        0 (by intro u a₀ b₀; simp only [ContinuousMap.zero_apply, map_zero]) h
        ((h : G)⁻¹ * a 0) ((h : G)⁻¹ * a 1)
    have hb : B.ρ (h : G) b.val = b.val := b.property h
    rw [← he, hb, h₀, mul_inv_cancel_left, mul_inv_cancel_left]
  let w := homogeneousCochainOfTuple G X 1 (invariantTupleTrace X H P hP)
    (invariantTupleTrace_equivariant X H P hP)
  let dw := C.d 1 2 w
  let e := corestrictCochain X H 2 (D.iCycles 2 c)
  have hw (a₀ a₁ : G) :
      w.val a₀ a₁ = ∑ q : Q, invariantTupleTranslateOnCoset X H P hP q ![a₀, a₁] := by
    change resolutionTupleHomeomorph G X 2 (homogeneousCochainOfTuple G X 1
      (invariantTupleTrace X H P hP) (invariantTupleTrace_equivariant X H P hP)).val ![a₀, a₁] = _
    rw [homogeneousCochainOfTuple_apply]
    simp only [invariantTupleTrace, ContinuousMap.sum_apply]
  have heval (a₀ a₁ a₂ : G) :
      e.val a₀ a₁ a₂ = ∑ q : Q, tupleTranslateOnCoset X H 2 (D.iCycles 2 c) q ![a₀, a₁, a₂] :=
    corestrictCochain_tuple X H 2 (D.iCycles 2 c) ![a₀, a₁, a₂]
  have hp₀ (a₀ a₁ a₂ : G) :
      p₀ a₁ a₂ - p₀ a₀ a₂ + p₀ a₀ a₁ = Z a₀ a₁ a₂ -
        Z (openSubgroupRetraction H a₀) (openSubgroupRetraction H a₁)
          (openSubgroupRetraction H a₂) :=
    openSubgroupPrism_boundary H Z (degreeTwo_cocycle_equation A z) a₀ a₁ a₂
  have hPeval (a₀ a₁ : G) : P ![a₀, a₁] = p (p₀ a₀ a₁) b.val := rfl
  have heach (q : Q) (a₀ a₁ a₂ : G) :
      invariantTupleTranslateOnCoset X H P hP q ![a₁, a₂] -
        invariantTupleTranslateOnCoset X H P hP q ![a₀, a₂] +
        invariantTupleTranslateOnCoset X H P hP q ![a₀, a₁] =
      p (Z a₀ a₁ a₂) (coefficientOnCoset B H b q) -
        tupleTranslateOnCoset X H 2 (D.iCycles 2 c) q ![a₀, a₁, a₂] :=
    corestrict_invariantPairing_coset X H p he b z c p₀ hp₀ P hP hPeval hceval q a₀ a₁ a₂
  have hdw : dw = C.iCycles 2 d - e := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a₀
    apply ContinuousMap.ext
    intro a₁
    apply ContinuousMap.ext
    intro a₂
    have hd := congrArg (fun v => v a₀ a₁ a₂) (homogeneousCochains.d_apply X 1 w)
    change dw.val a₀ a₁ a₂ = (C.iCycles 2 d).val a₀ a₁ a₂ - e.val a₀ a₁ a₂
    rw [hd]
    change w.val a₁ a₂ - (w.val a₀ a₂ - w.val a₀ a₁) = _
    rw [show w.val a₁ a₂ - (w.val a₀ a₂ - w.val a₀ a₁) =
      w.val a₁ a₂ - w.val a₀ a₂ + w.val a₀ a₁ from by abel,
      hw, hw, hw, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    simp only [heach, Finset.sum_sub_distrib, heval]
    have hsum : (∑ q : Q, p (Z a₀ a₁ a₂) (coefficientOnCoset B H b q)) =
        p (Z a₀ a₁ a₂) (openSubgroupNorm B H b).val := by
      exact (map_sum (p (Z a₀ a₁ a₂)) (coefficientOnCoset B H b) Finset.univ).symm.trans
        (congrArg (p (Z a₀ a₁ a₂)) (openSubgroupNorm_val' B H b).symm)
    exact congrArg (fun z : X => z - _)
      (hsum.trans (hdeval a₀ a₁ a₂).symm)
  exact ⟨w, hdw⟩

private theorem corestrict_π_eq_of_boundary (c : cocycles Y 2) (d : cocycles X 2)
    (w : (homogeneousCochains X).X 1)
    (hw : (homogeneousCochains X).d 1 2 w =
      (homogeneousCochains X).iCycles 2 d -
        corestrictCochain X H 2 ((homogeneousCochains Y).iCycles 2 c)) :
    corestrict X H 2 (π Y 2 c) = π X 2 d := by
  let C := homogeneousCochains X
  let v : cocycles X 2 := d - C.toCycles 1 2 w
  have h := ConcreteCategory.congr_hom (C.toCycles_i 1 2) w
  have hv : corestrictCochain X H 2 ((homogeneousCochains Y).iCycles 2 c) = C.iCycles 2 v := by
    change _ = C.iCycles 2 (d - C.toCycles 1 2 w)
    change C.iCycles 2 (C.toCycles 1 2 w) = C.d 1 2 w at h
    rw [map_sub, h, hw, sub_sub_cancel]
  have hzero := ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) w
  change π X 2 (C.toCycles 1 2 w) = 0 at hzero
  rw [corestrict_π_of_cochain X H 2 c v hv]
  change π X 2 (d - C.toCycles 1 2 w) = _
  rw [map_sub, hzero, sub_zero]

/-- The degree-two projection formula on the original continuous cohomology.
The left input is restricted and paired with an open-subgroup invariant.
On corestriction the right coefficient becomes its finite coset norm. -/
theorem corestrict_degreeTwoInvariantMap_general
    (b : TopRep.invariants RB) (x : continuousCohomology 2 A) :
    corestrict X H 2
        (degreeTwoInvariantMap (A := RA) (B := RB) (C := Y) p hp (fun h => he (h : G)) b
          (openRestriction A H 2 x)) =
      degreeTwoInvariantMap p hp he (openSubgroupNorm B H b) x := by
  obtain ⟨z, rfl⟩ := π_surjective A 2 x
  let C := homogeneousCochains X
  let D := homogeneousCochains Y
  let ι : I →ₜ* G := ProCGroups.ContinuousMonoidHom.subtype H.toSubgroup
  let f := rightInvariantCoefficientMap (A := RA) (B := RB) (C := Y) p hp (fun h => he (h : G)) b
  let F := rightInvariantCoefficientMap p hp he (openSubgroupNorm B H b)
  let cA := cocyclesMap ι (𝟙 RA) 2 z
  let c := cocyclesMap (ContinuousMonoidHom.id I) f 2 cA
  let d := cocyclesMap (ContinuousMonoidHom.id G) F 2 z
  let Z := ((homogeneousCochains A).iCycles 2 z).val
  have hceval (a₀ a₁ a₂ : I) : (D.iCycles 2 c).val a₀ a₁ a₂ = p (Z a₀ a₁ a₂) b.val := by
    have h := mappedRelativeCocycle_apply (ContinuousMonoidHom.id I) f cA a₀ a₁ a₂
    have h₀ : (D.iCycles 2 c).val a₀ a₁ a₂ =
        p (((homogeneousCochains RA).iCycles 2 cA).val a₀ a₁ a₂) b.val := h
    exact h₀.trans (congrArg (fun t => p t b.val)
      (mappedRelativeCocycle_apply ι (𝟙 RA) z a₀ a₁ a₂))
  have hdeval (a₀ a₁ a₂ : G) :
      (C.iCycles 2 d).val a₀ a₁ a₂ = p (Z a₀ a₁ a₂) (openSubgroupNorm B H b).val :=
    mappedRelativeCocycle_apply (ContinuousMonoidHom.id G) F z a₀ a₁ a₂
  obtain ⟨w, hdw⟩ := corestrict_invariantPairing_boundary X H p hp he b z c d hceval hdeval
  have hres : openRestriction A H 2 (π A 2 z) = π RA 2 cA :=
    ConcreteCategory.congr_hom (π_map ι (𝟙 RA) 2) z
  let U := degreeTwoInvariantMap (A := RA) (B := RB) (C := Y) p hp (fun h => he (h : G)) b
  have hinput : U (π RA 2 cA) = π Y 2 c :=
    degreeTwoInvariantMap_π (A := RA) (B := RB) (C := Y) p hp (fun h => he (h : G)) b cA
  have houtput : degreeTwoInvariantMap p hp he (openSubgroupNorm B H b) (π A 2 z) = π X 2 d :=
    degreeTwoInvariantMap_π (A := A) (B := B) (C := X) p hp he (openSubgroupNorm B H b) z
  exact (congrArg (corestrict X H 2) ((congrArg U hres).trans hinput)).trans
    ((corestrict_π_eq_of_boundary X H c d w hdw).trans houtput.symm)

end Projection

/-- The degree-two projection formula when the right coefficient is also the target. -/
theorem corestrict_degreeTwoInvariantMap {A : TopRep.{u} ℤ G}
    (p : A →ₗ[ℤ] X →ₗ[ℤ] X) (hp : Continuous (fun t : A × X => p t.1 t.2))
    (he : ∀ (g : G) (a : A) (b : X), p (A.ρ g a) (X.ρ g b) = X.ρ g (p a b))
    (b : TopRep.invariants Y) (x : continuousCohomology 2 A) :
    corestrict X H 2
        (degreeTwoInvariantMap (A := TopRep.res H.toSubgroup.subtype A) (B := Y)
          p hp (fun h => he (h : G)) b (openRestriction A H 2 x)) =
      degreeTwoInvariantMap p hp he (openSubgroupNorm X H b) x :=
  corestrict_degreeTwoInvariantMap_general X H p hp he b x

end ContinuousCohomology
