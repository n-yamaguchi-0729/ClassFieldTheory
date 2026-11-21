/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousRepresentationUniverseLift
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.ContinuousH0Naturality
public import Nyll.GaloisCohomology.Topology.ContinuousSubgroupPrimitiveExtension
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.GaloisCohomology.Topology.OpenSubgroupCoinduction
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

/-! # Continuous Shapiro evaluation for an open subgroup -/

@[expose] public section

open ProCGroups.ContinuousMonoidHom (subtype)
open CategoryTheory ContRepresentation TopRep ReidemeisterSchreier.Profinite
open scoped BigOperators Topology

noncomputable section

namespace ContinuousCohomology

universe u

attribute [local instance] TopRep.integralModuleOfRepresentation

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (U : OpenSubgroup G)

variable (A : TopRep.{u} ℤ (↥U.toSubgroup))

/-- Restrict original cochains and evaluate the coinduced coefficient at the identity. -/
def openShapiroRestriction (n : ℕ) :
    continuousCohomology.{0, u, u} n (openCoinduced U A) →+ continuousCohomology.{0, u, u} n A := by
  let B : TopRep.{u} ℤ G := openCoinduced U A
  let i : ↥U.toSubgroup →ₜ* G := subtype U.toSubgroup
  let ev : TopRep.res i.toMonoidHom B ⟶ A := openCoinducedEval U A
  let m : continuousCohomology.{0, u, u} n B ⟶ continuousCohomology.{0, u, u} n A :=
    map.{0, u, u} (X := B) (Y := A) i ev n
  exact m.hom.toLinearMap.toAddMonoidHom

private def coinduceTuple {k : ℕ} (z : C(Fin k → G, A))
    (hz : ∀ (h : (↥U.toSubgroup)) (a : Fin k → G), z (fun i => (h : G) * a i) = A.ρ h (z a)) :
    C(Fin k → G, (openCoinduced U A)) := by
  let f : C((Fin k → G) × G, A) :=
    ⟨fun ag => z (fun i => ag.2 * ag.1 i),
      z.continuous.comp (continuous_pi fun i =>
        continuous_snd.mul ((continuous_apply i).comp continuous_fst))⟩
  let e := Homeomorph.curry f
  have he (a : Fin k → G) (h : (↥U.toSubgroup)) (g : G) : e a ((h : G) * g) = A.ρ h (e a g) := by
    change z (fun i => ((h : G) * g) * a i) = A.ρ h (z (fun i => g * a i))
    simp only [mul_assoc]
    exact hz h (fun i => g * a i)
  exact ⟨fun a => ⟨e a, he a⟩, e.continuous.subtype_mk _⟩

private theorem coinduceTuple_equivariant {k : ℕ} (z : C(Fin k → G, A))
    (hz : ∀ (h : (↥U.toSubgroup)) (a : Fin k → G), z (fun i => (h : G) * a i) = A.ρ h (z a))
    (g : G) (a : Fin k → G) :
    coinduceTuple U A z hz (fun i => g * a i) =
      (openCoinduced U A).ρ g (coinduceTuple U A z hz a) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change z (fun i => x * (g * a i)) = z (fun i => (x * g) * a i)
  simp only [mul_assoc]

private def openShapiroRetractedTuple (n : ℕ) (c : (homogeneousCochains.{0, u, u} A).X n) :
    C(Fin (n + 1) → G, A) := by
  let z := resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1) c.val
  let r := openSubgroupRetraction U
  exact ⟨fun a => z (fun i => r (a i)),
    z.continuous.comp (continuous_pi fun i => r.continuous.comp (continuous_apply i))⟩

private theorem openShapiroRetractedTuple_equivariant (n : ℕ)
    (c : (homogeneousCochains.{0, u, u} A).X n)
    (h : (↥U.toSubgroup)) (a : Fin (n + 1) → G) :
    openShapiroRetractedTuple U A n c (fun i => (h : G) * a i) =
      A.ρ h (openShapiroRetractedTuple U A n c a) := by
  let z := resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1) c.val
  let r := openSubgroupRetraction U
  change z (fun i => r ((h : G) * a i)) = A.ρ h (z (fun i => r (a i)))
  have hr (i : Fin (n + 1)) : r ((h : G) * a i) = h * r (a i) :=
    openSubgroupRetraction_subgroup_mul U h (a i)
  exact (congrArg z (funext hr)).trans
    (homogeneousCochain_tuple_equivariant (↥U.toSubgroup) A n c h (fun i => r (a i)))

private def coinduceCochain (n : ℕ) (z : C(Fin (n + 1) → G, A))
    (hz : ∀ (h : (↥U.toSubgroup)) (a : Fin (n + 1) → G), z (fun i => (h : G) * a i) = A.ρ h (z a)) :
    (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n := by
  let B : TopRep.{u} ℤ G := openCoinduced U A
  let t : C(Fin (n + 1) → G, B) := coinduceTuple U A z hz
  exact homogeneousCochainOfTuple G B n t
    (coinduceTuple_equivariant U A z hz)

private theorem coinduceCochain_apply (n : ℕ) (z : C(Fin (n + 1) → G, A))
    (hz : ∀ (h : (↥U.toSubgroup)) (a : Fin (n + 1) → G), z (fun i => (h : G) * a i) = A.ρ h (z a))
    (a : Fin (n + 1) → G) (g : G) :
    openCoinducedValue U A g
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) (coinduceCochain U A n z hz).val a) =
      z (fun i => g * a i) := by
  let B : TopRep.{u} ℤ G := openCoinduced U A
  let t : C(Fin (n + 1) → G, B) := coinduceTuple U A z hz
  exact (congrArg (fun f : C(Fin (n + 1) → G, B) => openCoinducedValue U A g (f a))
    (homogeneousCochainOfTuple_apply G B n t (coinduceTuple_equivariant U A z hz))).trans rfl

private def openShapiroExtendedCochain (n : ℕ) (c : (homogeneousCochains.{0, u, u} A).X n) :
    (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n :=
  coinduceCochain U A n (openShapiroRetractedTuple U A n c)
    (openShapiroRetractedTuple_equivariant U A n c)

private theorem openShapiroExtendedCochain_apply (n : ℕ) (c : (homogeneousCochains.{0, u, u} A).X n)
    (a : Fin (n + 1) → G) (g : G) :
    openCoinducedValue U A g
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1)
        (openShapiroExtendedCochain U A n c).val a) =
      resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1) c.val
        (fun i => openSubgroupRetraction U (g * a i)) := by
  exact coinduceCochain_apply U A n _ _ a g

private theorem openShapiroExtendedCochain_d (n : ℕ) (c : (homogeneousCochains.{0, u, u} A).X n) :
    (homogeneousCochains.{0, u, u} (openCoinduced U A)).d n (n + 1)
        (openShapiroExtendedCochain U A n c) =
      openShapiroExtendedCochain U A (n + 1) ((homogeneousCochains.{0, u, u} A).d n (n + 1) c) := by
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)).injective
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  let w := openShapiroExtendedCochain U A n c
  rw [homogeneousCochains.d_eq]
  change openCoinducedValue U A g
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)
        ((TopRep.d.{0, u, u} (openCoinduced U A) (n + 1)).hom w.val) a) =
    openCoinducedValue U A g
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)
        (openShapiroExtendedCochain U A (n + 1)
          ((homogeneousCochains.{0, u, u} A).d n (n + 1) c)).val a)
  rw [resolutionTupleHomeomorph_d, map_sum]
  simp only [map_zsmul]
  rw [openShapiroExtendedCochain_apply]
  rw [homogeneousCochains.d_eq]
  calc
    _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1) c.val
          (fun j => openSubgroupRetraction U (g * a (i.succAbove j))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun v : A => (-1 : ℤ) ^ (i : ℕ) • v)
        (openShapiroExtendedCochain_apply U A n c (fun j => a (i.succAbove j)) g)
    _ = _ := (resolutionTupleHomeomorph_d (↥U.toSubgroup) A (n + 1) c.val
      (fun i => openSubgroupRetraction U (g * a i))).symm

private theorem openShapiroExtendedCochain_zero (n : ℕ) :
    openShapiroExtendedCochain U A n 0 = 0 := by
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  change openCoinducedValue U A g
    (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1)
      (openShapiroExtendedCochain U A n 0).val a) =
      openCoinducedValue U A g
        (resolutionTupleContinuousLinearEquiv G (openCoinduced U A) (n + 1) 0 a)
  rw [openShapiroExtendedCochain_apply]
  change resolutionTupleContinuousLinearEquiv (↥U.toSubgroup) A (n + 1) 0
    (fun i => openSubgroupRetraction U (g * a i)) = _
  simp only [map_zero, ContinuousMap.zero_apply]

private theorem openShapiroCochain_restriction_extension (n : ℕ)
    (c : (homogeneousCochains.{0, u, u} A).X n) :
    ((cochainsMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A)).f n)
      (openShapiroExtendedCochain U A n c) = c := by
  apply Subtype.ext
  apply (resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  rw [resolutionTupleHomeomorph_cochainsMap]
  change openCoinducedValue U A 1
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1)
        (openShapiroExtendedCochain U A n c).val
        (fun i => (a i : G))) = resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1) c.val a
  rw [openShapiroExtendedCochain_apply]
  simp only [one_mul, openSubgroupRetraction_subtype]

/-- The original continuous Shapiro map is surjective in every degree. -/
theorem openShapiroRestriction_surjective (n : ℕ) :
    Function.Surjective (openShapiroRestriction U A n) := by
  intro x
  obtain ⟨z, rfl⟩ := π_surjective.{0, u} A n x
  let C := homogeneousCochains.{0, u, u} A
  let E := homogeneousCochains.{0, u, u} (openCoinduced U A)
  let w := openShapiroExtendedCochain U A n (C.iCycles n z)
  have hz : C.d n (n + 1) (C.iCycles n z) = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  have hw : E.d n (n + 1) w = 0 := by
    change E.d n (n + 1) (openShapiroExtendedCochain U A n (C.iCycles n z)) = 0
    rw [openShapiroExtendedCochain_d, hz, openShapiroExtendedCochain_zero]
  let B := openCoinduced U A
  let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let T := (continuousModuleComplexFunctor G).obj B
  let z' := T.cyclesMk (i := n) w (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hw
  let e := (E.sc n).mapCyclesIso F
  let y : cocycles.{0, u, u} B n := e.hom z'
  have hy : E.iCycles n y = w := by
    have hy' : moduleCycle B n y = z' := Iso.hom_inv_id_apply e z'
    exact (moduleCycle_iCycles B n y).symm.trans
      ((congrArg (T.iCycles n) hy').trans (T.i_cyclesMk _ _ _ _))
  have hm : cocyclesMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) n y = z := by
    let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
    apply (ModuleCat.mono_iff_injective (F.map (C.iCycles n))).mp inferInstance
    change C.iCycles n (cocyclesMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) n y) =
      C.iCycles n z
    let m := cochainsMap.{0, u, u} (X := B) (Y := A) (subtype U.toSubgroup) (openCoinducedEval U A)
    exact (cochainOfMappedCocycle (subtype U.toSubgroup) (openCoinducedEval U A) n y).trans
      ((congrArg (fun t : E.X n => m.f n t) hy).trans
        (openShapiroCochain_restriction_extension U A n (C.iCycles n z)))
  refine ⟨π.{0, u, u} (openCoinduced U A) n y, ?_⟩
  have hmap := ConcreteCategory.congr_hom
    (π_map.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) n) y
  exact hmap.trans (congrArg (π.{0, u, u} A n) hm)

private def evaluatedCoinducedTuple (n : ℕ)
    (w : (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n) :
    C(Fin (n + 1) → G, A) :=
  ⟨fun a => openCoinducedValue U A 1
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val a),
    (openCoinducedValue U A 1).continuous.comp
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val).continuous⟩

private theorem evaluatedCoinducedTuple_translate (n : ℕ)
    (w : (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n)
    (g : G) (a : Fin (n + 1) → G) :
    evaluatedCoinducedTuple U A n w (fun i => g * a i) =
      openCoinducedValue U A g
        (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val a) := by
  have h := congrArg (openCoinducedValue U A 1)
    (homogeneousCochain_tuple_equivariant G (openCoinduced U A) n w g a)
  change evaluatedCoinducedTuple U A n w (fun i => g * a i) =
    (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val a).val (1 * g) at h
  rw [one_mul] at h
  exact h

private theorem evaluatedCoinducedTuple_equivariant (n : ℕ)
    (w : (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n)
    (h : (↥U.toSubgroup)) (a : Fin (n + 1) → G) :
    evaluatedCoinducedTuple U A n w (fun i => (h : G) * a i) =
      A.ρ h (evaluatedCoinducedTuple U A n w a) := by
  rw [evaluatedCoinducedTuple_translate]
  let F := resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val a
  change F.val (h : G) = A.ρ h (F.val 1)
  exact (congrArg F.val (mul_one (h : G))).symm.trans (F.property h 1)

private theorem evaluatedCoinducedTuple_closed (n : ℕ)
    (z : cocycles.{0, u, u} (openCoinduced U A) n)
    (a : Fin (n + 2) → G) :
    (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • evaluatedCoinducedTuple U A n
      ((homogeneousCochains.{0, u, u} (openCoinduced U A)).iCycles n z)
      (fun j => a (i.succAbove j))) = 0 := by
  let C := homogeneousCochains.{0, u, u} (openCoinduced U A)
  let w := C.iCycles n z
  let e := resolutionTupleContinuousLinearEquiv G (openCoinduced U A) (n + 2)
  have hc : C.d n (n + 1) w = 0 := ConcreteCategory.congr_hom (C.iCycles_d n (n + 1)) z
  rw [homogeneousCochains.d_eq] at hc
  have h := congrArg (fun y : C.X (n + 1) => openCoinducedValue U A 1 (e y.val a)) hc
  change openCoinducedValue U A 1
    (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)
        ((TopRep.d.{0, u, u} (openCoinduced U A) (n + 1)).hom w.val) a) =
    openCoinducedValue U A 1 (e 0 a) at h
  rw [resolutionTupleHomeomorph_d, map_sum] at h
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    openCoinducedValue U A 1
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 1) w.val
        (fun j => a (i.succAbove j)))) = 0
  simpa only [map_zsmul, map_zero, ContinuousMap.zero_apply] using h

private theorem evaluatedCoinducedTuple_restrict (n : ℕ)
    (w : (homogeneousCochains.{0, u, u} (openCoinduced U A)).X n)
    (a : Fin (n + 1) → (↥U.toSubgroup)) :
    resolutionTupleHomeomorph (↥U.toSubgroup) A (n + 1)
        (((cochainsMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A)).f n) w).val a =
      evaluatedCoinducedTuple U A n w (fun i => (a i : G)) :=
  resolutionTupleHomeomorph_cochainsMap G (openCoinduced U A) A
    (subtype U.toSubgroup) (openCoinducedEval U A) n w a

private theorem π_eq_zero_of_coinducedPrimitive (n : ℕ)
    (z : cocycles.{0, u, u} (openCoinduced U A) (n + 1))
    (P : C(Fin (n + 1) → G, A))
    (hP : ∀ (h : (↥U.toSubgroup)) (a : Fin (n + 1) → G), P (fun i => (h : G) * a i) = A.ρ h (P a))
    (hd : ∀ a : Fin (n + 2) → G,
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P (fun j => a (i.succAbove j))) =
        evaluatedCoinducedTuple U A (n + 1)
          ((homogeneousCochains.{0, u, u} (openCoinduced U A)).iCycles (n + 1) z) a) :
    π.{0, u, u} (openCoinduced U A) (n + 1) z = 0 := by
  let C := homogeneousCochains.{0, u, u} (openCoinduced U A)
  let w := coinduceCochain U A n P hP
  let v := C.iCycles (n + 1) z
  have hv : C.d n (n + 1) w = v := by
    apply Subtype.ext
    apply (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)).injective
    apply ContinuousMap.ext
    intro a
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    rw [homogeneousCochains.d_eq]
    change openCoinducedValue U A g
      (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2)
        ((TopRep.d.{0, u, u} (openCoinduced U A) (n + 1)).hom w.val) a) =
        openCoinducedValue U A g (resolutionTupleHomeomorph G (openCoinduced U A) (n + 2) v.val a)
    rw [resolutionTupleHomeomorph_d, map_sum]
    simp only [map_zsmul]
    calc
      _ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P (fun j => g * a (i.succAbove j)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun v : A => (-1 : ℤ) ^ (i : ℕ) • v)
          (coinduceCochain_apply U A n P hP (fun j => a (i.succAbove j)) g)
      _ = _ := (hd (fun i => g * a i)).trans
        (evaluatedCoinducedTuple_translate U A (n + 1) v g a)
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  have hz : C.toCycles n (n + 1) w = z := by
    apply (ModuleCat.mono_iff_injective (F.map (C.iCycles (n + 1)))).mp inferInstance
    change C.iCycles (n + 1) (C.toCycles n (n + 1) w) = v
    exact (ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) w).trans hv
  change C.homologyπ (n + 1) z = 0
  rw [← hz]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) w

/-- Degree-zero Shapiro evaluation keeps the value of the original invariant at one. -/
theorem openShapiroRestriction_zero_val (x : continuousCohomology 0 (openCoinduced U A)) :
    ((zeroIso A).hom (openShapiroRestriction U A 0 x)).val =
      openCoinducedValue U A 1 ((zeroIso (openCoinduced U A)).hom x).val := by
  obtain ⟨z, rfl⟩ := π_surjective.{0, u} (openCoinduced U A) 0 x
  have h : openShapiroRestriction U A 0 (π.{0, u, u} (openCoinduced U A) 0 z) =
      π.{0, u, u} A 0 (cocyclesMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 0 z) :=
    ConcreteCategory.congr_hom (π_map.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 0) z
  rw [h, zeroIso_hom_π_val, zeroIso_hom_π_val, cochainOfMappedCocycle]
  exact evaluatedCoinducedTuple_restrict U A 0
    ((homogeneousCochains.{0, u, u} (openCoinduced U A)).iCycles 0 z) (fun _ => 1)

/-- The actual Shapiro restriction is injective in degree zero. -/
theorem openShapiroRestriction_injective_zero :
    Function.Injective (openShapiroRestriction U A 0) := by
  apply (injective_iff_map_eq_zero (openShapiroRestriction U A 0)).mpr
  intro x hx
  let f := (zeroIso (openCoinduced U A)).hom x
  have hf₁ : openCoinducedValue U A 1 f.val = 0 := by
    rw [← openShapiroRestriction_zero_val U A x, hx]
    exact congrArg Subtype.val (map_zero (zeroIso A).hom.hom)
  have hf : f = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    have h := congrArg (openCoinducedValue U A 1) (f.property g)
    change f.val.val (1 * g) = f.val.val 1 at h
    rw [one_mul] at h
    exact h.trans hf₁
  apply (ConcreteCategory.bijective_of_isIso (zeroIso (openCoinduced U A)).hom).1
  rw [map_zero]
  exact hf

omit [IsTopologicalGroup G] [CompactSpace G] in
private theorem signedFaces_one {J : Type u} (f : (Fin 1 → J) → A) (a b : J) :
    (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • f (fun j => (![a, b] : Fin 2 → J) (i.succAbove j))) =
      f ![b] - f ![a] := by
  rw [Fin.sum_univ_two]
  have h₀ : (fun j => (![a, b] : Fin 2 → J) ((0 : Fin 2).succAbove j)) = ![b] := by
    funext j
    fin_cases j
    rfl
  have h₁ : (fun j => (![a, b] : Fin 2 → J) ((1 : Fin 2).succAbove j)) = ![a] := by
    funext j
    fin_cases j
    rfl
  rw [h₀, h₁]
  change (-1 : ℤ) ^ (0 : ℕ) • f ![b] + (-1 : ℤ) ^ (1 : ℕ) • f ![a] = _
  simp only [pow_zero, pow_one, one_zsmul, neg_one_zsmul, sub_eq_add_neg]

omit [IsTopologicalGroup G] [CompactSpace G] in
private theorem signedFaces_two {J : Type u} (f : (Fin 2 → J) → A) (a b c : J) :
    (∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • f (fun j => (![a, b, c] : Fin 3 → J) (i.succAbove j))) =
      f ![b, c] - f ![a, c] + f ![a, b] := by
  rw [Fin.sum_univ_three]
  have h₀ : (fun j => (![a, b, c] : Fin 3 → J) ((0 : Fin 3).succAbove j)) = ![b, c] := by
    funext j
    fin_cases j <;> rfl
  have h₁ : (fun j => (![a, b, c] : Fin 3 → J) ((1 : Fin 3).succAbove j)) = ![a, c] := by
    funext j
    fin_cases j <;> rfl
  have h₂' : (fun j => (![a, b, c] : Fin 3 → J) ((2 : Fin 3).succAbove j)) = ![a, b] := by
    funext j
    fin_cases j <;> rfl
  rw [h₀, h₁, h₂']
  change (-1 : ℤ) ^ (0 : ℕ) • f ![b, c] + (-1 : ℤ) ^ (1 : ℕ) • f ![a, c] +
    (-1 : ℤ) ^ (2 : ℕ) • f ![a, b] = _
  have h₂ : (-1 : ℤ) ^ (2 : ℕ) = 1 := by decide
  simp only [pow_zero, pow_one, h₂, one_zsmul, neg_one_zsmul, sub_eq_add_neg]

omit [IsTopologicalGroup G] [CompactSpace G] in
private theorem signedFaces_three (f : (Fin 3 → G) → A) (a b c d : G) :
    (∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • f (fun j => (![a, b, c, d] : Fin 4 → G) (i.succAbove j))) =
      f ![b, c, d] - f ![a, c, d] + f ![a, b, d] - f ![a, b, c] := by
  rw [Fin.sum_univ_four]
  have h₀ : (fun j => (![a, b, c, d] : Fin 4 → G) ((0 : Fin 4).succAbove j)) = ![b, c, d] := by
    funext j
    fin_cases j <;> rfl
  have h₁ : (fun j => (![a, b, c, d] : Fin 4 → G) ((1 : Fin 4).succAbove j)) = ![a, c, d] := by
    funext j
    fin_cases j <;> rfl
  have h₂' : (fun j => (![a, b, c, d] : Fin 4 → G) ((2 : Fin 4).succAbove j)) = ![a, b, d] := by
    funext j
    fin_cases j <;> rfl
  have h₃' : (fun j => (![a, b, c, d] : Fin 4 → G) ((3 : Fin 4).succAbove j)) = ![a, b, c] := by
    funext j
    fin_cases j <;> rfl
  rw [h₀, h₁, h₂', h₃']
  change (-1 : ℤ) ^ (0 : ℕ) • f ![b, c, d] + (-1 : ℤ) ^ (1 : ℕ) • f ![a, c, d] +
    (-1 : ℤ) ^ (2 : ℕ) • f ![a, b, d] + (-1 : ℤ) ^ (3 : ℕ) • f ![a, b, c] = _
  have h₂ : (-1 : ℤ) ^ (2 : ℕ) = 1 := by decide
  have h₃ : (-1 : ℤ) ^ (3 : ℕ) = -1 := by decide
  simp only [pow_zero, pow_one, h₂, h₃, one_zsmul, neg_one_zsmul, sub_eq_add_neg]

/-- A subgroup primitive produces an actual ambient primitive in degree one. -/
theorem openShapiroRestriction_injective_one :
    Function.Injective (openShapiroRestriction U A 1) := by
  apply (injective_iff_map_eq_zero (openShapiroRestriction U A 1)).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := π_surjective.{0, u} (openCoinduced U A) 1 x
  let D := homogeneousCochains.{0, u, u} A
  let w := (homogeneousCochains.{0, u, u} (openCoinduced U A)).iCycles 1 z
  let z' := cocyclesMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 1 z
  have hmap := ConcreteCategory.congr_hom
    (π_map.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 1) z
  have hp : π.{0, u, u} A 1 z' = 0 := hmap.symm.trans hx
  obtain ⟨b, hb⟩ := exists_boundary_of_π_eq_zero A 0 z' hp
  let Z := evaluatedCoinducedTuple U A 1 w
  let r := openSubgroupRetraction U
  let P : C(Fin 1 → G, A) :=
    ⟨fun a => b.val (r (a 0)) - Z ![a 0, r (a 0)], by
      have ht : Continuous (fun a : Fin 1 → G => ![(a 0), (r (a 0) : G)]) := by
        apply continuous_pi
        intro i
        fin_cases i
        · exact continuous_apply 0
        · exact continuous_subtype_val.comp (r.continuous.comp (continuous_apply 0))
      exact (b.val.continuous.comp (r.continuous.comp (continuous_apply 0))).sub
        (Z.continuous.comp ht)⟩
  have hP (h : (↥U.toSubgroup)) (a : Fin 1 → G) : P (fun i => (h : G) * a i) = A.ρ h (P a) := by
    change b.val (r ((h : G) * a 0)) - Z ![(h : G) * a 0, r ((h : G) * a 0)] =
      A.ρ h (b.val (r (a 0)) - Z ![a 0, r (a 0)])
    rw [openSubgroupRetraction_subgroup_mul, map_sub]
    have hb' := homogeneousCochain_tuple_equivariant (↥U.toSubgroup) A 0 b h (fun _ => r (a 0))
    change b.val (h * r (a 0)) = A.ρ h (b.val (r (a 0))) at hb'
    rw [hb']
    have hvec : (![(h : G) * a 0, ((h * r (a 0) : (↥U.toSubgroup)) : G)] : Fin 2 → G) =
        fun i => (h : G) * (![a 0, (r (a 0) : G)] : Fin 2 → G) i := by
      funext i
      fin_cases i <;> rfl
    rw [hvec]
    exact congrArg (A.ρ h (b.val (r (a 0))) - ·)
      (evaluatedCoinducedTuple_equivariant U A 1 w h ![a 0, r (a 0)])
  apply π_eq_zero_of_coinducedPrimitive U A 0 z P hP
  intro a
  let x₀ := a 0
  let x₁ := a 1
  have ha : a = ![x₀, x₁] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, signedFaces_one U A P]
  have hbound : b.val (r x₁) - b.val (r x₀) = Z ![r x₀, r x₁] := by
    let a' : Fin 2 → (↥U.toSubgroup) := ![r x₀, r x₁]
    have hd := (resolutionTupleHomeomorph_d (↥U.toSubgroup) A 1 b.val a').trans
      (signedFaces_one U A (resolutionTupleHomeomorph (↥U.toSubgroup) A 1 b.val) (r x₀) (r x₁))
    change resolutionTupleHomeomorph (↥U.toSubgroup) A 2 ((D.d 0 1).hom b).val a' = _ at hd
    have hvec : (fun i => (a' i : G)) = ![(r x₀ : G), (r x₁ : G)] := by
      funext i
      fin_cases i <;> rfl
    rw [hb, cochainOfMappedCocycle, evaluatedCoinducedTuple_restrict] at hd
    rw [hvec] at hd
    exact hd.symm
  have h₀ := evaluatedCoinducedTuple_closed U A 1 z ![x₀, r x₀, r x₁]
  have h₁ := evaluatedCoinducedTuple_closed U A 1 z ![x₀, x₁, r x₁]
  rw [signedFaces_two] at h₀ h₁
  change Z ![r x₀, r x₁] - Z ![x₀, r x₁] + Z ![x₀, r x₀] = 0 at h₀
  change Z ![x₁, r x₁] - Z ![x₀, r x₁] + Z ![x₀, x₁] = 0 at h₁
  change (b.val (r x₁) - Z ![x₁, r x₁]) - (b.val (r x₀) - Z ![x₀, r x₀]) = Z ![x₀, x₁]
  calc
    _ = b.val (r x₁) - b.val (r x₀) - Z ![x₁, r x₁] + Z ![x₀, r x₀] := by abel
    _ = Z ![x₀, x₁] +
        (Z ![r x₀, r x₁] - Z ![x₀, r x₁] + Z ![x₀, r x₀]) -
        (Z ![x₁, r x₁] - Z ![x₀, r x₁] + Z ![x₀, x₁]) := by rw [hbound]; abel
    _ = _ := by simp only [h₀, h₁, add_zero, sub_zero]

/-- A subgroup primitive produces an actual ambient primitive in degree two. -/
theorem openShapiroRestriction_injective_two :
    Function.Injective (openShapiroRestriction U A 2) := by
  apply (injective_iff_map_eq_zero (openShapiroRestriction U A 2)).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := π_surjective.{0, u} (openCoinduced U A) 2 x
  let D := homogeneousCochains.{0, u, u} A
  let w := (homogeneousCochains.{0, u, u} (openCoinduced U A)).iCycles 2 z
  let z' := cocyclesMap.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 2 z
  have hmap := ConcreteCategory.congr_hom
    (π_map.{0, u, u} (subtype U.toSubgroup) (openCoinducedEval U A) 2) z
  have hp : π.{0, u, u} A 2 z' = 0 := hmap.symm.trans hx
  obtain ⟨b, hb⟩ := exists_boundary_of_π_eq_zero A 1 z' hp
  let Z := evaluatedCoinducedTuple U A 2 w
  let r := openSubgroupRetraction U
  let T := TopRep.of (ContRepresentation.trivial ℤ G A)
  let Z₀ := (resolutionTupleHomeomorph G T 3).symm Z
  have hZ (a b c : G) : Z₀ a b c = Z ![a, b, c] :=
    congrArg (fun F : C(Fin 3 → G, A) => F ![a, b, c])
      ((resolutionTupleHomeomorph G T 3).apply_symm_apply Z)
  have hZclosed (a b c d : G) :
      Z₀ b c d - Z₀ a c d + Z₀ a b d - Z₀ a b c = 0 := by
    have h := evaluatedCoinducedTuple_closed U A 2 z ![a, b, c, d]
    rw [signedFaces_three] at h
    simpa only [hZ] using h
  have hZcov (h : (↥U.toSubgroup)) (a b c : G) :
      Z₀ ((h : G) * a) ((h : G) * b) ((h : G) * c) = A.ρ h (Z₀ a b c) := by
    have hvec : (![(h : G) * a, (h : G) * b, (h : G) * c] : Fin 3 → G) =
        fun i => (h : G) * (![a, b, c] : Fin 3 → G) i := by
      funext i
      fin_cases i <;> rfl
    simp only [hZ]
    rw [hvec]
    exact evaluatedCoinducedTuple_equivariant U A 2 w h ![a, b, c]
  have hbp (x y t : (↥U.toSubgroup)) : b.val y t - b.val x t + b.val x y = Z₀ x y t := by
    let a' : Fin 3 → (↥U.toSubgroup) := ![x, y, t]
    have hd := (resolutionTupleHomeomorph_d (↥U.toSubgroup) A 2 b.val a').trans
      (signedFaces_two U A (resolutionTupleHomeomorph (↥U.toSubgroup) A 2 b.val) x y t)
    change resolutionTupleHomeomorph (↥U.toSubgroup) A 3 ((D.d 1 2).hom b).val a' = _ at hd
    have hvec : (fun i => (a' i : G)) = ![(x : G), (y : G), (t : G)] := by
      funext i
      fin_cases i <;> rfl
    rw [hb, cochainOfMappedCocycle, evaluatedCoinducedTuple_restrict] at hd
    rw [hvec] at hd
    rw [hZ]
    exact hd.symm
  let P₀ := openSubgroupPrimitiveExtension U Z₀ b.val
  let P := resolutionTupleHomeomorph G T 2 P₀
  have hP (h : (↥U.toSubgroup)) (a : Fin 2 → G) : P (fun i => (h : G) * a i) = A.ρ h (P a) := by
    let x := a 0
    let y := a 1
    have hbCov := homogeneousCochain_tuple_equivariant (↥U.toSubgroup) A 1 b h ![r x, r y]
    change b.val (h * r x) (h * r y) = A.ρ h (b.val (r x) (r y)) at hbCov
    change b.val (r ((h : G) * x)) (r ((h : G) * y)) -
          Z₀ ((h : G) * x) (r ((h : G) * x)) (r ((h : G) * y)) +
          Z₀ ((h : G) * x) ((h : G) * y) (r ((h : G) * y)) =
      A.ρ h (b.val (r x) (r y) - Z₀ x (r x) (r y) + Z₀ x y (r y))
    have hrx : r ((h : G) * x) = h * r x := openSubgroupRetraction_subgroup_mul U h x
    have hry : r ((h : G) * y) = h * r y := openSubgroupRetraction_subgroup_mul U h y
    simp only [hrx, hry, Subgroup.coe_mul, hbCov, hZcov, map_add,
      map_sub]
  apply π_eq_zero_of_coinducedPrimitive U A 1 z P hP
  intro a
  let x := a 0
  let y := a 1
  let t := a 2
  have ha : a = ![x, y, t] := by
    funext i
    fin_cases i <;> rfl
  rw [ha, signedFaces_two U A P]
  change P ![y, t] - P ![x, t] + P ![x, y] = Z ![x, y, t]
  rw [← hZ]
  exact openSubgroupPrimitiveExtension_boundary U Z₀ hZclosed b.val hbp x y t

/-- Shapiro's isomorphism in the three degrees of the local Euler characteristic. -/
def openShapiroEquiv (n : ℕ) (hn : n < 3) :
    continuousCohomology.{0, u, u} n (openCoinduced U A) ≃+ continuousCohomology.{0, u, u} n A :=
  AddEquiv.ofBijective (openShapiroRestriction U A n) ⟨by
    interval_cases n
    · exact openShapiroRestriction_injective_zero U A
    · exact openShapiroRestriction_injective_one U A
    · exact openShapiroRestriction_injective_two U A, openShapiroRestriction_surjective U A n⟩

end ContinuousCohomology
