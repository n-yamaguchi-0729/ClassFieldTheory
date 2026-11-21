/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.GaloisCohomology.Topology.ContinuousCupLow

/-! # Corestriction and the continuous cup pairing

The finite coset trace extends cochains along the open-subgroup retraction.
The prism for a homogeneous one-cocycle compares its two evaluations along
that retraction and gives the projection formula at the cocycle level.
-/

@[expose] public section

open ProCGroups.ContinuousMonoidHom (subtype)
open scoped BigOperators Topology
open CategoryTheory ContRepresentation TopRep ReidemeisterSchreier.Profinite

noncomputable section

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (H : OpenSubgroup G)

local notation "I" => Subtype (fun g : G => g ∈ H.toSubgroup)
local notation "R" X => TopRep.res H.toSubgroup.subtype X
local notation "Q" => G ⧸ (H : Subgroup G)

omit [CompactSpace G] in
private theorem openSubgroupRetraction_mul_val (h : I) (g : G) :
    (openSubgroupRetraction H ((h : G) * g) : G) =
      (h : G) * (openSubgroupRetraction H g : G) :=
  congrArg Subtype.val (openSubgroupRetraction_subgroup_mul H h g)

/-- On degree-one continuous cohomology the actual restriction followed by
corestriction is multiplication by the index. -/
theorem corestrict_openRestriction_one (X : TopRep.{u} ℤ G) (x : continuousCohomology 1 X) :
    corestrict X H 1 (openRestriction X H 1 x) = H.toSubgroup.index • x := by
  obtain ⟨z, rfl⟩ := π_surjective X 1 x
  let Z := ((homogeneousCochains X).iCycles 1 z).val
  let r := openSubgroupRetraction H
  let P : C(Fin 1 → G, X) :=
    ⟨fun a => Z (r (a 0)) (a 0), by
      have hr : Continuous (fun a : Fin 1 → G => (r (a 0) : G)) :=
        continuous_subtype_val.comp (r.continuous.comp (continuous_apply 0))
      exact (Z.continuous.comp hr).eval (continuous_apply 0)⟩
  have hP (h : I) : translateTuple X (h : G) P = P := by
    apply ContinuousMap.ext
    intro a
    change X.ρ (h : G) (Z (r ((h : G)⁻¹ * a 0)) ((h : G)⁻¹ * a 0)) =
      Z (r (a 0)) (a 0)
    have he := cochainOne_equivariant ((homogeneousCochains X).iCycles 1 z) (h : G)
      (r ((h : G)⁻¹ * a 0)) ((h : G)⁻¹ * a 0)
    rw [he, ← openSubgroupRetraction_mul_val H h, mul_inv_cancel_left]
  apply corestrict_openRestriction_of_tuplePrism X H 0 z P hP
  intro a
  change (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • P (fun j => a (i.succAbove j))) =
    Z (a 0) (a 1) - Z (r (a 0)) (r (a 1))
  have hfirst : (fun j : Fin 1 => a ((0 : Fin 2).succAbove j)) = fun _ => a 1 := by
    funext j
    fin_cases j
    rfl
  have hsecond : (fun j : Fin 1 => a ((1 : Fin 2).succAbove j)) = fun _ => a 0 := by
    funext j
    fin_cases j
    rfl
  rw [Fin.sum_univ_two, hfirst, hsecond]
  change (-1 : ℤ) ^ (0 : ℕ) • Z (r (a 1)) (a 1) +
    (-1 : ℤ) ^ (1 : ℕ) • Z (r (a 0)) (a 0) = _
  simp only [pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  change Z (r (a 1)) (a 1) + -Z (r (a 0)) (a 0) = Z (a 0) (a 1) - Z (r (a 0)) (r (a 1))
  have h₀ : Z (r (a 0)) (a 1) = Z (r (a 0)) (a 0) + Z (a 0) (a 1) :=
    oneCocycle_add z _ _ _
  have h₁ : Z (r (a 0)) (a 1) = Z (r (a 0)) (r (a 1)) + Z (r (a 1)) (a 1) :=
    oneCocycle_add z _ _ _
  calc
    _ = (Z (r (a 0)) (r (a 1)) + Z (r (a 1)) (a 1)) -
        (Z (r (a 0)) (a 0) + Z (a 0) (a 1)) +
        (Z (a 0) (a 1) - Z (r (a 0)) (r (a 1))) := by abel
    _ = _ := by rw [← h₁, ← h₀, sub_self, zero_add]

section Cocycle

variable (X : TopRep.{u} ℤ G)

/-- The finite coset trace of a cocycle is closed. -/
theorem corestrictCocycle_closed (n : ℕ) (z : cocycles (R X) n) :
    (homogeneousCochains X).d n (n + 1)
      (corestrictCochain X H n ((homogeneousCochains (R X)).iCycles n z)) = 0 := by
  let c := (homogeneousCochains (R X)).iCycles n z
  have hc : (homogeneousCochains (R X)).d n (n + 1) c = 0 :=
    ConcreteCategory.congr_hom ((homogeneousCochains (R X)).iCycles_d n (n + 1)) z
  have hz : corestrictCochain X H (n + 1) (0 : (homogeneousCochains (R X)).X (n + 1)) = 0 :=
    map_zero ((corestrictContinuousModuleComplex X H).f (n + 1)).hom
  exact (corestrictCochain_d X H n c).trans
    ((congrArg (corestrictCochain X H (n + 1)) hc).trans hz)

/-- Corestriction applied to an original continuous homogeneous cocycle. -/
def corestrictCocycle (n : ℕ) (z : cocycles (R X) n) : cocycles X n := by
  let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let T := (continuousModuleComplexFunctor G).obj X
  let v := corestrictCochain X H n ((homogeneousCochains (R X)).iCycles n z)
  have hv : T.d n (n + 1) v = 0 := by
    exact corestrictCocycle_closed H X n z
  let c := T.cyclesMk (i := n) v (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hv
  exact (((homogeneousCochains X).sc n).mapCyclesIso F).hom c

theorem corestrictCocycle_iCycles (n : ℕ) (z : cocycles (R X) n) :
    (homogeneousCochains X).iCycles n (corestrictCocycle H X n z) =
      corestrictCochain X H n ((homogeneousCochains (R X)).iCycles n z) := by
  let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let e := ((homogeneousCochains X).sc n).mapCyclesIso F
  let T := (continuousModuleComplexFunctor G).obj X
  let v := corestrictCochain X H n ((homogeneousCochains (R X)).iCycles n z)
  have hv : T.d n (n + 1) v = 0 := corestrictCocycle_closed H X n z
  let c := T.cyclesMk (i := n) v (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hv
  have hc : moduleCycle X n (corestrictCocycle H X n z) = c := Iso.hom_inv_id_apply e c
  exact (moduleCycle_iCycles X n (corestrictCocycle H X n z)).symm.trans
    ((congrArg (T.iCycles n) hc).trans (T.i_cyclesMk _ _ _ _))

/-- The cohomology class of the averaged cocycle is the actual corestriction. -/
theorem corestrict_π (n : ℕ) (z : cocycles (R X) n) :
    corestrict X H n (π (R X) n z) = π X n (corestrictCocycle H X n z) :=
  corestrict_π_of_cochain X H n z _ (corestrictCocycle_iCycles H X n z).symm

private theorem corestrictCochain_map_coeff {Y : TopRep.{u} ℤ G} (f : X ⟶ Y) (n : ℕ)
    (z : (homogeneousCochains (R X)).X n) :
    corestrictCochain Y H n (((cochainsMap (ContinuousMonoidHom.id I)
      ((TopRep.resFunctor H.toSubgroup.subtype).map f)).f n) z) =
      ((cochainsMap (ContinuousMonoidHom.id G) f).f n) (corestrictCochain X H n z) := by
  let f' : (R X) ⟶ (R Y) := (TopRep.resFunctor H.toSubgroup.subtype).map f
  let idI := ContinuousMonoidHom.id I
  let idG := ContinuousMonoidHom.id G
  let z' := ((cochainsMap idI f').f n) z
  let c := corestrictCochain X H n z
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G Y (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  let : Fintype Q := openSubgroupQuotientFintype H
  have hmap := resolutionTupleHomeomorph_cochainsMap G X Y idG f n c a
  change resolutionTupleHomeomorph G Y (n + 1) (corestrictCochain Y H n z').val a =
    resolutionTupleHomeomorph G Y (n + 1) (((cochainsMap idG f).f n) c).val a
  refine (corestrictCochain_tuple Y H n z' a).trans (Eq.trans ?_ hmap.symm)
  calc
    (∑ q : Q, tupleTranslateOnCoset Y H n z' q a) =
        ∑ q : Q, f (tupleTranslateOnCoset X H n z q a) := by
      apply Finset.sum_congr rfl
      intro q _
      induction q using Quotient.inductionOn with
      | h g =>
        let b (i : Fin (n + 1)) := openSubgroupRetraction H (g⁻¹ * a i)
        have hz := resolutionTupleHomeomorph_cochainsMap I (R X) (R Y) idI f' n z b
        calc
          _ = Y.ρ g (resolutionTupleHomeomorph I (R Y) (n + 1) z'.val b) :=
            tupleTranslateOnCoset_mk Y H n z' g a
          _ = Y.ρ g (f (resolutionTupleHomeomorph I (R X) (n + 1) z.val b)) :=
            congrArg (fun v : Y => Y.ρ g v) hz
          _ = f (X.ρ g (resolutionTupleHomeomorph I (R X) (n + 1) z.val b)) :=
            (TopRep.hom_comm_apply f g _).symm
          _ = _ := congrArg f (tupleTranslateOnCoset_mk X H n z g a).symm
    _ = f (∑ q : Q, tupleTranslateOnCoset X H n z q a) := (map_sum f.hom _ _).symm
    _ = f (resolutionTupleHomeomorph G X (n + 1) c.val a) :=
      congrArg f (corestrictCochain_tuple X H n z a).symm

private theorem corestrictCocycle_map_coeff {Y : TopRep.{u} ℤ G} (f : X ⟶ Y) (n : ℕ)
    (z : cocycles (R X) n) :
    corestrictCocycle H Y n (cocyclesMap (ContinuousMonoidHom.id I)
      ((TopRep.resFunctor H.toSubgroup.subtype).map f) n z) =
      cocyclesMap (ContinuousMonoidHom.id G) f n (corestrictCocycle H X n z) := by
  let f' : (R X) ⟶ (R Y) := (TopRep.resFunctor H.toSubgroup.subtype).map f
  let idI := ContinuousMonoidHom.id I
  let idG := ContinuousMonoidHom.id G
  let z' := cocyclesMap idI f' n z
  let c := corestrictCocycle H X n z
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  apply (ModuleCat.mono_iff_injective
    (F.map ((homogeneousCochains Y).iCycles n))).mp inferInstance
  change (homogeneousCochains Y).iCycles n (corestrictCocycle H Y n z') =
    (homogeneousCochains Y).iCycles n (cocyclesMap idG f n c)
  rw [corestrictCocycle_iCycles H, cochainOfMappedCocycle idI f' n z,
    cochainOfMappedCocycle idG f n c, corestrictCocycle_iCycles H]
  exact corestrictCochain_map_coeff H X f n _

private theorem corestrict_map_coeff_π {Y : TopRep.{u} ℤ G} (f : X ⟶ Y) (n : ℕ)
    (z : cocycles (R X) n) :
    corestrict Y H n (map (ContinuousMonoidHom.id I)
      ((TopRep.resFunctor H.toSubgroup.subtype).map f) n (π (R X) n z)) =
      map (ContinuousMonoidHom.id G) f n (corestrict X H n (π (R X) n z)) := by
  let f' : (R X) ⟶ (R Y) := (TopRep.resFunctor H.toSubgroup.subtype).map f
  let idI := ContinuousMonoidHom.id I
  let idG := ContinuousMonoidHom.id G
  let z' : cocycles (R Y) n := cocyclesMap (X := R X) (Y := R Y) idI f' n z
  let c : cocycles X n := corestrictCocycle H X n z
  let mI : continuousCohomology n (R X) ⟶ continuousCohomology n (R Y) :=
    map (X := R X) (Y := R Y) idI f' n
  let mG : continuousCohomology n X ⟶ continuousCohomology n Y :=
    map (X := X) (Y := Y) idG f n
  have hleft : mI (π (R X) n z) = π (R Y) n z' :=
    ConcreteCategory.congr_hom (π_map (X := R X) (Y := R Y) idI f' n) z
  have hright : mG (π X n c) = π Y n (cocyclesMap (X := X) (Y := Y) idG f n c) :=
    ConcreteCategory.congr_hom (π_map (X := X) (Y := Y) idG f n) c
  have hc := congrArg (π Y n) (corestrictCocycle_map_coeff H X f n z)
  calc
    _ = corestrict Y H n (π (R Y) n z') := congrArg (corestrict Y H n) hleft
    _ = π Y n (corestrictCocycle H Y n z') := corestrict_π H Y n z'
    _ = π Y n (cocyclesMap idG f n c) := hc
    _ = mG (π X n c) := hright.symm
    _ = _ := congrArg mG (corestrict_π H X n z).symm

/-- Corestriction commutes with morphisms of the original coefficients. -/
theorem corestrict_map_coeff {Y : TopRep.{u} ℤ G} (f : X ⟶ Y) (n : ℕ)
    (x : continuousCohomology n (R X)) :
    corestrict Y H n (map (ContinuousMonoidHom.id I)
      ((TopRep.resFunctor H.toSubgroup.subtype).map f) n x) =
      map (ContinuousMonoidHom.id G) f n (corestrict X H n x) := by
  obtain ⟨z, hz⟩ := π_surjective (R X) n x
  rw [← hz]
  exact corestrict_map_coeff_π H X f n z

end Cocycle

section Cup

variable {A B C : TopRep.{u} ℤ G}
variable (p : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (hp : Continuous (fun x : A × B => p x.1 x.2))
    (he : ∀ (g : G) (a : A) (b : B), p (A.ρ g a) (B.ρ g b) = C.ρ g (p a b))

omit [CompactSpace G] in
private theorem openRestriction_π (X : TopRep.{u} ℤ G) (n : ℕ) (z : cocycles X n) :
    openRestriction X H n (π X n z) =
      π (R X) n (cocyclesMap (subtype H.toSubgroup) (𝟙 (R X)) n z) :=
  ConcreteCategory.congr_hom (π_map (subtype H.toSubgroup) (𝟙 (R X)) n) z

private theorem restrictOneCocycle_apply (X : TopRep.{u} ℤ G) (z : cocycles X 1) (a b : I) :
    ((homogeneousCochains (R X)).iCycles 1
      (cocyclesMap (subtype H.toSubgroup) (𝟙 (R X)) 1 z)).val a b =
      ((homogeneousCochains X).iCycles 1 z).val a b := by
  change resolutionTupleHomeomorph I (R X) 2
    ((homogeneousCochains (R X)).iCycles 1
      (cocyclesMap (subtype H.toSubgroup) (𝟙 (R X)) 1 z)).val ![a, b] = _
  rw [cochainOfMappedCocycle, resolutionTupleHomeomorph_cochainsMap, ConcreteCategory.id_apply]
  rfl

omit [CompactSpace G] in
private theorem degreeOne_retraction_difference (x : cocycles A 1) (a b : G) :
    let X := ((homogeneousCochains A).iCycles 1 x).val
    let r := openSubgroupRetraction H
    X (r a) (r b) - X a b = X b (r b) - X a (r a) := by
  dsimp only
  let X := ((homogeneousCochains A).iCycles 1 x).val
  let r := openSubgroupRetraction H
  change X (r a) (r b) - X a b = X b (r b) - X a (r a)
  have h₀ : X a (r b) = X a (r a) + X (r a) (r b) := oneCocycle_add x _ _ _
  have h₁ : X a (r b) = X a b + X b (r b) := oneCocycle_add x _ _ _
  calc
    _ = (X a (r a) + X (r a) (r b)) - (X a b + X b (r b)) +
        (X b (r b) - X a (r a)) := by abel
    _ = _ := by rw [← h₀, ← h₁, sub_self, zero_add]

/-- The projection formula for the actual continuous cup of two degree-one classes. -/
theorem corestrict_cupOneOne_left (a : continuousCohomology 1 A)
    (b : continuousCohomology 1 (R B)) :
    corestrict C H 2
      (cupOneOne (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        (openRestriction A H 1 a) b) = cupOneOne p hp he a (corestrict B H 1 b) := by
  obtain ⟨x, rfl⟩ := π_surjective A 1 a
  obtain ⟨y, rfl⟩ := π_surjective (R B) 1 b
  let x' := cocyclesMap (subtype H.toSubgroup) (𝟙 (R A)) 1 x
  let c := cupOneOneCocycle (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G)) x' y
  let e := corestrictCocycle H C 2 c
  let z := cupOneOneCocycle p hp he x (corestrictCocycle H B 1 y)
  have hres := openRestriction_π H A 1 x
  have hcup := cupOneOne_π (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G)) x' y
  have hfirst := (congrArg (corestrict C H 2) ((congrArg (fun t =>
    cupOneOne (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
      t (π (R B) 1 y)) hres).trans hcup)).trans (corestrict_π H C 2 c)
  have hlast := (cupOneOne_π p hp he x (corestrictCocycle H B 1 y)).symm.trans
    (congrArg (cupOneOne p hp he (π A 1 x)) (corestrict_π H B 1 y).symm)
  refine hfirst.trans ((show π C 2 e = π C 2 z from ?_).trans hlast)
  have hclass : π C 2 (e - z) = 0 := by
    let X := ((homogeneousCochains A).iCycles 1 x).val
    let Y := ((homogeneousCochains (R B)).iCycles 1 y).val
    let r := openSubgroupRetraction H
    let P : C(Fin 2 → G, C) :=
      ⟨fun t => p (X (t 0) (r (t 0))) (Y (r (t 0)) (r (t 1))), by
        have hr (i : Fin 2) : Continuous (fun t : Fin 2 → G => r (t i)) :=
          r.continuous.comp (continuous_apply i)
        have hX : Continuous (fun t : Fin 2 → G => X (t 0) (r (t 0))) :=
          (X.continuous.comp (continuous_apply 0)).eval (continuous_subtype_val.comp (hr 0))
        have hY : Continuous (fun t : Fin 2 → G => Y (r (t 0)) (r (t 1))) :=
          (Y.continuous.comp (hr 0)).eval (hr 1)
        exact hp.comp (hX.prodMk hY)⟩
    have hP (h : I) : translateTuple C (h : G) P = P := by
      apply ContinuousMap.ext
      intro t
      let v (i : Fin 2) := (h : G)⁻¹ * t i
      change C.ρ (h : G) (p (X (v 0) (r (v 0))) (Y (r (v 0)) (r (v 1)))) =
        p (X (t 0) (r (t 0))) (Y (r (t 0)) (r (t 1)))
      have hX : A.ρ (h : G) (X (v 0) (r (v 0))) = X (t 0) (r (t 0)) := by
        have hh := cochainOne_equivariant ((homogeneousCochains A).iCycles 1 x)
          (h : G) (v 0) (r (v 0))
        change _ = X ((h : G) * v 0) ((h : G) * (r (v 0) : G)) at hh
        rw [← openSubgroupRetraction_mul_val H h] at hh
        simpa only [v, mul_inv_cancel_left] using hh
      have hY : B.ρ (h : G) (Y (r (v 0)) (r (v 1))) = Y (r (t 0)) (r (t 1)) := by
        have hh := cochainOne_equivariant ((homogeneousCochains (R B)).iCycles 1 y)
          h (r (v 0)) (r (v 1))
        have hr (i : Fin 2) : h * r (v i) = r (t i) :=
          (openSubgroupRetraction_subgroup_mul H h (v i)).symm.trans
            (congrArg r (mul_inv_cancel_left (h : G) (t i)))
        exact hh.trans (congrArg₂ (fun s t : I => Y s t) (hr 0) (hr 1))
      rw [← he, hX, hY]
    let w := homogeneousCochainOfTuple G C 1 (invariantTupleTrace C H P hP)
      (invariantTupleTrace_equivariant C H P hP)
    let : Fintype Q := openSubgroupQuotientFintype H
    let W := invariantTupleTranslateOnCoset C H P hP
    let E := tupleTranslateOnCoset C H 2 ((homogeneousCochains (R C)).iCycles 2 c)
    let F := tupleTranslateOnCoset B H 1 ((homogeneousCochains (R B)).iCycles 1 y)
    have hw (a b : G) : w.val a b = ∑ q : Q, W q ![a, b] := by
      change resolutionTupleHomeomorph G C 2 w.val ![a, b] = _
      rw [show w = homogeneousCochainOfTuple G C 1 (invariantTupleTrace C H P hP)
        (invariantTupleTrace_equivariant C H P hP) from rfl, homogeneousCochainOfTuple_apply]
      simp only [invariantTupleTrace, ContinuousMap.sum_apply, W]
    have heval (a b d : G) : ((homogeneousCochains C).iCycles 2 e).val a b d =
        ∑ q : Q, E q ![a, b, d] := by
      change resolutionTupleHomeomorph G C 3
        ((homogeneousCochains C).iCycles 2 e).val ![a, b, d] = _
      rw [corestrictCocycle_iCycles H, corestrictCochain_tuple]
    have hfval (a b : G) : ((homogeneousCochains B).iCycles 1 (corestrictCocycle H B 1 y)).val a b =
        ∑ q : Q, F q ![a, b] := by
      change resolutionTupleHomeomorph G B 2
        ((homogeneousCochains B).iCycles 1 (corestrictCocycle H B 1 y)).val ![a, b] = _
      rw [corestrictCocycle_iCycles H, corestrictCochain_tuple]
    have hcoset (a b d : G) (q : Q) : W q ![b, d] - W q ![a, d] + W q ![a, b] =
        E q ![a, b, d] - p (X a b) (F q ![b, d]) := by
      induction q using Quotient.inductionOn with
      | h g =>
        let a' := g⁻¹ * a
        let b' := g⁻¹ * b
        let d' := g⁻¹ * d
        change C.ρ g (p (X b' (r b')) (Y (r b') (r d'))) -
            C.ρ g (p (X a' (r a')) (Y (r a') (r d'))) +
            C.ρ g (p (X a' (r a')) (Y (r a') (r b'))) =
          C.ρ g (((homogeneousCochains (R C)).iCycles 2 c).val (r a') (r b') (r d')) -
            p (X a b) (B.ρ g (Y (r b') (r d')))
        have hx : A.ρ g (X a' b') = X a b := by
          have hh := cochainOne_equivariant ((homogeneousCochains A).iCycles 1 x) g a' b'
          simpa only [a', b', mul_inv_cancel_left] using hh
        rw [← hx, he, ← map_sub, ← map_add, ← map_sub]
        apply congrArg (C.ρ g)
        have hc : ((homogeneousCochains (R C)).iCycles 2 c).val (r a') (r b') (r d') =
            p (((homogeneousCochains (R A)).iCycles 1 x').val (r a') (r b'))
              (Y (r b') (r d')) :=
          (congrArg (fun f : (homogeneousCochains (R C)).X 2 => f.val (r a') (r b') (r d'))
            (iCycles_cupOneOneCocycle (A := R A) (B := R B) (C := R C)
              p hp (fun h => he (h : G)) x' y)).trans
            (cupOneOneCochain_apply (A := R A) (B := R B) (C := R C)
              p hp (fun h => he (h : G)) _ _ (r a') (r b') (r d'))
        rw [hc]
        rw [restrictOneCocycle_apply H, ← LinearMap.sub_apply, ← map_sub]
        change _ = p (X (r a') (r b') - X a' b') (Y (r b') (r d'))
        rw [degreeOne_retraction_difference H x a' b']
        have hy : Y (r a') (r d') = Y (r a') (r b') + Y (r b') (r d') := oneCocycle_add y _ _ _
        rw [hy]
        simp only [map_add, map_sub, LinearMap.sub_apply]
        abel
    apply class_zero_of_degreeTwo_boundary (e - z) w
    apply Subtype.ext
    apply ContinuousMap.ext
    intro a
    apply ContinuousMap.ext
    intro b
    apply ContinuousMap.ext
    intro d
    change ((homogeneousCochains C).d 1 2 w).val a b d =
      ((homogeneousCochains C).iCycles 2 (e - z)).val a b d
    rw [oneBoundary_apply, map_sub]
    change w.val b d - (w.val a d - w.val a b) =
      ((homogeneousCochains C).iCycles 2 e).val a b d -
        ((homogeneousCochains C).iCycles 2 z).val a b d
    rw [show w.val b d - (w.val a d - w.val a b) = w.val b d - w.val a d + w.val a b from by abel,
      hw, hw, hw, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    simp only [hcoset, Finset.sum_sub_distrib, heval]
    have hz : ((homogeneousCochains C).iCycles 2 z).val a b d =
        p (X a b) (∑ q : Q, F q ![b, d]) :=
      (congrArg (fun f : (homogeneousCochains C).X 2 => f.val a b d)
        (iCycles_cupOneOneCocycle p hp he x (corestrictCocycle H B 1 y))).trans
        ((cupOneOneCochain_apply p hp he _ _ a b d).trans
          (congrArg (p (X a b)) (hfval b d)))
    rw [hz, map_sum]
  apply sub_eq_zero.mp
  rwa [map_sub] at hclass

/-- Graded commutativity in bidegree `(1,1)` on the actual representatives. -/
theorem cupOneOne_flip (a : continuousCohomology 1 A) (b : continuousCohomology 1 B) :
    cupOneOne p hp he a b = -cupOneOne p.flip (hp.comp continuous_swap)
      (fun g b a => he g a b) b a := by
  obtain ⟨x, rfl⟩ := π_surjective A 1 a
  obtain ⟨y, rfl⟩ := π_surjective B 1 b
  let X := (homogeneousCochains A).iCycles 1 x
  let Y := (homogeneousCochains B).iCycles 1 y
  let P : C(Fin 2 → G, C) := ⟨fun t => p (X.val (t 0) (t 1)) (Y.val (t 0) (t 1)), by
    have hX : Continuous (fun t : Fin 2 → G => X.val (t 0) (t 1)) :=
      (X.val.continuous.comp (continuous_apply 0)).eval (continuous_apply 1)
    have hY : Continuous (fun t : Fin 2 → G => Y.val (t 0) (t 1)) :=
      (Y.val.continuous.comp (continuous_apply 0)).eval (continuous_apply 1)
    exact hp.comp (hX.prodMk hY)⟩
  have hP (g : G) (t : Fin 2 → G) : P (fun i => g * t i) = C.ρ g (P t) := by
    change p (X.val (g * t 0) (g * t 1)) (Y.val (g * t 0) (g * t 1)) =
      C.ρ g (p (X.val (t 0) (t 1)) (Y.val (t 0) (t 1)))
    rw [← cochainOne_equivariant X, ← cochainOne_equivariant Y, he]
  let w := homogeneousCochainOfTuple G C 1 (-P) (by
    intro g t
    simp only [ContinuousMap.neg_apply, hP, map_neg])
  let c := cupOneOneCocycle p hp he x y
  let c' := cupOneOneCocycle p.flip (hp.comp continuous_swap) (fun g b a => he g a b) y x
  have hw (a b : G) : w.val a b = -p (X.val a b) (Y.val a b) := by
    change resolutionTupleHomeomorph G C 2 w.val ![a, b] = _
    rw [show w = homogeneousCochainOfTuple G C 1 (-P) _ from rfl,
      homogeneousCochainOfTuple_apply]
    rfl
  have h : π C 2 (c + c') = 0 := by
    apply class_zero_of_degreeTwo_boundary (c + c') w
    apply Subtype.ext
    ext a b d
    rw [oneBoundary_apply, map_add]
    let ev (v : (homogeneousCochains C).X 2) := v.val a b d
    have hc : ev ((homogeneousCochains C).iCycles 2 c) = p (X.val a b) (Y.val b d) :=
      (congrArg ev (iCycles_cupOneOneCocycle p hp he x y)).trans
        (cupOneOneCochain_apply p hp he X Y a b d)
    have hc' : ev ((homogeneousCochains C).iCycles 2 c') = p (X.val b d) (Y.val a b) :=
      (congrArg ev (iCycles_cupOneOneCocycle p.flip (hp.comp continuous_swap)
        (fun g b a => he g a b) y x)).trans
          (cupOneOneCochain_apply p.flip (hp.comp continuous_swap)
            (fun g b a => he g a b) Y X a b d)
    change w.val b d - (w.val a d - w.val a b) =
      ev ((homogeneousCochains C).iCycles 2 c) + ev ((homogeneousCochains C).iCycles 2 c')
    rw [hc, hc', hw, hw, hw]
    rw [show X.val a d = X.val a b + X.val b d from oneCocycle_add x a b d,
      show Y.val a d = Y.val a b + Y.val b d from oneCocycle_add y a b d]
    simp only [map_add, LinearMap.add_apply]
    abel
  have hc : π C 2 c = -π C 2 c' := eq_neg_of_add_eq_zero_left (by rwa [map_add] at h)
  have hflip := cupOneOne_π p.flip (hp.comp continuous_swap) (fun g b a => he g a b) y x
  exact (cupOneOne_π p hp he x y).trans (hc.trans (congrArg Neg.neg hflip.symm))

/-- Corestriction and cup projection when the right degree-one argument
was restricted from the large group. -/
theorem corestrict_cupOneOne_right (a : continuousCohomology 1 (R A))
    (b : continuousCohomology 1 B) :
    corestrict C H 2
      (cupOneOne (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        a (openRestriction B H 1 b)) = cupOneOne p hp he (corestrict A H 1 a) b := by
  have hflip := cupOneOne_flip (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
    a (openRestriction B H 1 b)
  have hproj := corestrict_cupOneOne_left H p.flip (hp.comp continuous_swap)
    (fun g b a => he g a b) b a
  exact (congrArg (corestrict C H 2) hflip).trans ((map_neg (corestrict C H 2) _).trans
    ((congrArg Neg.neg hproj).trans (cupOneOne_flip p hp he (corestrict A H 1 a) b).symm))

/-- Corestriction and cup projection for a restricted degree-two argument
and an invariant of the open subgroup. -/
theorem corestrict_cupTwoZero_left (a : continuousCohomology 2 A)
    (b : continuousCohomology 0 (R B)) :
    corestrict C H 2
      (cupTwoZero (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        (openRestriction A H 2 a) b) = cupTwoZero p hp he a (corestrict B H 0 b) := by
  unfold cupTwoZero
  rw [corestrict_zero_eq_invariantNorm]
  exact corestrict_degreeTwoInvariantMap_general C H p hp he ((zeroIso (R B)).hom b) a

private theorem restrict_rightInvariantCoefficientMap (b : continuousCohomology 0 B) :
    (TopRep.resFunctor H.toSubgroup.subtype).map
        (rightInvariantCoefficientMap p hp he ((zeroIso B).hom b)) =
      rightInvariantCoefficientMap (A := R A) (B := R B) (C := R C)
        p hp (fun g => he (g : G)) ((zeroIso (R B)).hom (openRestriction B H 0 b)) := by
  let : Module ℤ (R A) := (R A).hV2
  let : Module ℤ (R C) := (R C).hV2
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext (π₁ := (R A).ρ) (π₂ := (R C).ρ)
  apply ContinuousLinearMap.ext
  intro x
  change p x ((zeroIso B).hom b).val = p x ((zeroIso (R B)).hom (openRestriction B H 0 b)).val
  exact congrArg (p x) (zeroIso_hom_openRestriction_val B H b).symm

/-- Corestriction commutes with the cup by a restricted invariant right coefficient. -/
theorem corestrict_cupTwoZero_right (a : continuousCohomology 2 (R A))
    (b : continuousCohomology 0 B) :
    corestrict C H 2
      (cupTwoZero (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        a (openRestriction B H 0 b)) = cupTwoZero p hp he (corestrict A H 2 a) b := by
  let f := rightInvariantCoefficientMap p hp he ((zeroIso B).hom b)
  let f' := rightInvariantCoefficientMap (A := R A) (B := R B) (C := R C)
    p hp (fun g => he (g : G)) ((zeroIso (R B)).hom (openRestriction B H 0 b))
  have hf : (TopRep.resFunctor H.toSubgroup.subtype).map f = f' :=
    restrict_rightInvariantCoefficientMap H p hp he b
  change corestrict C H 2 (map (ContinuousMonoidHom.id I) f' 2 a) =
    map (ContinuousMonoidHom.id G) f 2 (corestrict A H 2 a)
  rw [← hf]
  exact corestrict_map_coeff H A f 2 a

/-- Corestriction and cup projection for a restricted invariant left coefficient. -/
theorem corestrict_cupZeroTwo_left (a : continuousCohomology 0 A)
    (b : continuousCohomology 2 (R B)) :
    corestrict C H 2
      (cupZeroTwo (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        (openRestriction A H 0 a) b) = cupZeroTwo p hp he a (corestrict B H 2 b) := by
  have hflip := cupZeroTwo_flip (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
    (openRestriction A H 0 a) b
  have hproj := corestrict_cupTwoZero_right H p.flip (hp.comp continuous_swap)
    (fun g b a => he g a b) b a
  exact (congrArg (corestrict C H 2) hflip).trans
    (hproj.trans (cupZeroTwo_flip p hp he a (corestrict B H 2 b)).symm)

/-- Corestriction and cup projection for a restricted degree-two right coefficient. -/
theorem corestrict_cupZeroTwo_right (a : continuousCohomology 0 (R A))
    (b : continuousCohomology 2 B) :
    corestrict C H 2
      (cupZeroTwo (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
        a (openRestriction B H 2 b)) = cupZeroTwo p hp he (corestrict A H 0 a) b := by
  have hflip := cupZeroTwo_flip (A := R A) (B := R B) (C := R C) p hp (fun g => he (g : G))
    a (openRestriction B H 2 b)
  have hproj := corestrict_cupTwoZero_left H p.flip (hp.comp continuous_swap)
    (fun g b a => he g a b) b a
  exact (congrArg (corestrict C H 2) hflip).trans
    (hproj.trans (cupZeroTwo_flip p hp he (corestrict A H 0 a) b).symm)

end Cup

end ContinuousCohomology
