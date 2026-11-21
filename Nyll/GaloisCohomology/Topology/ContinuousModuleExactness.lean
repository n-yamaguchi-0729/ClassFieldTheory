/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousEquivariantTupleLifting
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Exact sequences of actual continuous cochains

For discrete coefficients with jointly continuous actions, pointwise short
exact coefficient sequences induce actual short exact sequences of the
module-valued continuous cochain complexes.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual continuous homogeneous complex after forgetting its topology. -/
def continuousModuleComplexFunctor :
    TopRep.{u} ℤ G ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  homogeneousContinuousCochainsFunctor G ⋙
    (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The module-valued continuous cochain functor is additive. -/
instance continuousModuleComplexFunctor_additive [LocallyCompactSpace G] :
    (continuousModuleComplexFunctor G).Additive where
  map_add := by
    intro A B φ ψ
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h :
        ((homogeneousContinuousCochainsFunctor G).map (φ + ψ)).f n =
          ((homogeneousContinuousCochainsFunctor G).map φ).f n +
            ((homogeneousContinuousCochainsFunctor G).map ψ).f n :=
      congrArg
        (fun m : (homogeneousContinuousCochainsFunctor G).obj A ⟶
          (homogeneousContinuousCochainsFunctor G).obj B => m.f n)
        ((homogeneousContinuousCochainsFunctor G).map_add (f := φ) (g := ψ))
    exact ConcreteCategory.congr_hom h x

/-- Pointwise exact discrete coefficients give degreewise exact cochains. -/
theorem continuousModuleComplex_degree_exact [LocallyCompactSpace G]
    (S : ShortComplex (TopRep.{u} ℤ G)) [DiscreteTopology S.X₂]
    (hS : ∀ y : S.X₂, S.g y = 0 → ∃ x : S.X₁, S.f x = y)
    (hA : Continuous (fun p : G × S.X₁ => S.X₁.ρ p.1 p.2)) (n : ℕ) :
    ((S.map (continuousModuleComplexFunctor G)).map
      (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n)).Exact := by
  apply (ShortComplex.exact_iff_of_hasForget _).mpr
  intro z hz
  exact homogeneousCochains_map_exact G S.X₁ S.X₂ S.X₃
    S.f S.g hS hA n z hz

/-- Actual pointwise short exact discrete coefficients give an actual short
exact sequence of continuous cochain complexes. -/
theorem continuousModuleComplex_shortExact [LocallyCompactSpace G]
    (S : ShortComplex (TopRep.{u} ℤ G))
    [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hf : Function.Injective S.f) (hg : Function.Surjective S.g)
    (hS : ∀ y : S.X₂, S.g y = 0 → ∃ x : S.X₁, S.f x = y)
    (hA : Continuous (fun p : G × S.X₁ => S.X₁.ρ p.1 p.2))
    (hB : Continuous (fun p : G × S.X₂ => S.X₂.ρ p.1 p.2)) :
    (S.map (continuousModuleComplexFunctor G)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine
    { exact := continuousModuleComplex_degree_exact G S hS hA n
      mono_f := ?_
      epi_g := ?_ }
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact homogeneousCochains_map_injective G S.X₁ S.X₂ S.f hf n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact homogeneousCochains_map_surjective G S.X₂ S.X₃ S.g hg hB n

/-- Forgetting topology identifies actual continuous homology with the
homology of the module-valued continuous complex. -/
def continuousModuleHomologyIso (X : TopRep.{u} ℤ G) (n : ℕ) :
    ((continuousModuleComplexFunctor G).obj X).homology n ≅
      (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
        (continuousCohomology n X) :=
  ((homogeneousCochains X).sc n).mapHomologyIso
    (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ))

/-- Actual continuous cohomology vanishing implies vanishing of the
corresponding module-valued homology object. -/
theorem continuousModuleComplex_isZero_of_cohomology_eq_zero
    (X : TopRep.{u} ℤ G) (n : ℕ)
    (h : ∀ x : continuousCohomology n X, x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology n) := by
  have hz : IsZero ((forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
      (continuousCohomology n X)) := by
    rw [IsZero.iff_id_eq_zero]
    apply ConcreteCategory.hom_ext
    intro x
    exact h x
  exact IsZero.of_iso hz (continuousModuleHomologyIso G X n)

/-- Vanishing of the module-valued homology kills each original continuous class. -/
theorem cohomology_eq_zero_of_continuousModuleComplex_isZero (X : TopRep.{u} ℤ G) (n : ℕ)
    (h : IsZero (((continuousModuleComplexFunctor G).obj X).homology n))
    (x : continuousCohomology n X) : x = 0 := by
  let e := continuousModuleHomologyIso G X n
  have hx : e.inv x = 0 := ConcreteCategory.congr_hom (h.eq_of_tgt (𝟙 _) 0) (e.inv x)
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  rw [map_zero]
  exact hx

/-- All degrees vanish for a subsingleton coefficient representation. -/
theorem continuousModuleHomology_isZero_of_subsingleton [LocallyCompactSpace G]
    (X : TopRep.{u} ℤ G) [Subsingleton X] (n : ℕ) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology n) := by
  let F := continuousModuleComplexFunctor G ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n
  have h : (𝟙 X : X ⟶ X) = 0 := by
    let : Module ℤ X := X.hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := X.ρ) (π₂ := X.ρ)
    apply ContinuousLinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  have hi : F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id X
  have hz : F.map (0 : X ⟶ X) = 0 := F.map_zero X X
  rw [IsZero.iff_id_eq_zero]
  exact hi.symm.trans ((congrArg (fun f : X ⟶ X => F.map f) h).trans hz)

end TopRep

namespace ContinuousCohomology

open TopRep

/-- A continuous cocycle as a cycle of the underlying module complex. -/
def moduleCycle {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (V : TopRep.{u} ℤ A) (n : ℕ) (z : cocycles V n) :
    ((continuousModuleComplexFunctor A).obj V).cycles n :=
  (((homogeneousCochains V).sc n).mapCyclesIso (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ))).inv z

/-- The module-valued cycle has the same original cochain. -/
theorem moduleCycle_iCycles {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (V : TopRep.{u} ℤ A) (n : ℕ) (z : cocycles V n) :
    ((continuousModuleComplexFunctor A).obj V).iCycles n (moduleCycle V n z) =
      (homogeneousCochains V).iCycles n z := by
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  let S := (homogeneousCochains V).sc n
  let e := S.mapCyclesIso F
  let z₀ : F.obj S.cycles := z
  let c := e.inv z₀
  have h := ConcreteCategory.congr_hom (S.mapCyclesIso_hom_iCycles F) c
  have h₀ : e.hom c = z₀ := Iso.inv_hom_id_apply e z₀
  exact h.symm.trans (congrArg (F.map S.iCycles) h₀)

private theorem mapCycles_homologyπ (S : ShortComplex (TopModuleCat.{u} ℤ)) [S.HasHomology] :
    let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let h := S.homologyData.left
  let eH : (S.map F).homology ≅ F.obj h.H := (h.map F).homologyIso
  let eK : (S.map F).cycles ≅ F.obj h.K := (h.map F).cyclesIso
  have hπ : (S.map F).homologyπ ≫ eH.hom = eK.hom ≫ F.map h.π :=
    (h.map F).homologyπ_comp_homologyIso_hom
  have hm : F.map h.π ≫ F.map h.homologyIso.inv =
      F.map h.cyclesIso.inv ≫ F.map S.homologyπ :=
    (F.map_comp h.π h.homologyIso.inv).symm.trans
      ((congrArg (fun f : h.K ⟶ S.homology => F.map f) h.π_comp_homologyIso_inv).trans
        (F.map_comp h.cyclesIso.inv S.homologyπ))
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  change (S.map F).homologyπ ≫ (eH.hom ≫ F.map h.homologyIso.inv) =
    (eK.hom ≫ F.map h.cyclesIso.inv) ≫ F.map S.homologyπ
  calc
    _ = ((S.map F).homologyπ ≫ eH.hom) ≫ F.map h.homologyIso.inv :=
      (Category.assoc _ _ _).symm
    _ = (eK.hom ≫ F.map h.π) ≫ F.map h.homologyIso.inv := congrArg (· ≫ F.map h.homologyIso.inv) hπ
    _ = eK.hom ≫ (F.map h.π ≫ F.map h.homologyIso.inv) := Category.assoc _ _ _
    _ = eK.hom ≫ (F.map h.cyclesIso.inv ≫ F.map S.homologyπ) := congrArg (eK.hom ≫ ·) hm
    _ = _ := (Category.assoc _ _ _).symm

/-- The homology comparison carries the original cocycle class across. -/
theorem moduleCycle_homologyπ {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (V : TopRep.{u} ℤ A) (n : ℕ) (z : cocycles V n) :
    (continuousModuleHomologyIso A V n).hom
      (((continuousModuleComplexFunctor A).obj V).homologyπ n (moduleCycle V n z)) = π V n z := by
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  let S := (homogeneousCochains V).sc n
  let e := S.mapCyclesIso F
  let z₀ : F.obj S.cycles := z
  let c := e.inv z₀
  have h := ConcreteCategory.congr_hom (mapCycles_homologyπ S) c
  have h₀ : e.hom c = z₀ := Iso.inv_hom_id_apply e z₀
  exact h.trans (congrArg (F.map S.homologyπ) h₀)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The comparison of module homology and continuous cohomology preserves
the original change of coefficients. -/
theorem continuousModuleHomologyIso_map_apply {A B : TopRep.{u} ℤ G}
    (f : A ⟶ B) (i : ℕ) (x : ((continuousModuleComplexFunctor G).obj A).homology i) :
    (continuousModuleHomologyIso G B i).hom
        (HomologicalComplex.homologyMap ((continuousModuleComplexFunctor G).map f) i x) =
      map (ContinuousMonoidHom.id G) f i ((continuousModuleHomologyIso G A i).hom x) := by
  let F := forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)
  let g := cochainsMap (ContinuousMonoidHom.id G) f
  exact ConcreteCategory.congr_hom (ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} ℤ) (ComplexShape.up ℕ) i).map g) F) x

/-- The actual cohomology change-of-coefficients map is additive in its
coefficient homomorphism. -/
theorem continuousCohomology_map_add_apply [LocallyCompactSpace G] {A B : TopRep.{u} ℤ G}
    (f g : A ⟶ B) (i : ℕ) (x : continuousCohomology i A) :
    map (ContinuousMonoidHom.id G) (f + g) i x =
      map (ContinuousMonoidHom.id G) f i x + map (ContinuousMonoidHom.id G) g i x := by
  let F := continuousModuleComplexFunctor G ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  let eA := continuousModuleHomologyIso G A i
  let eB := continuousModuleHomologyIso G B i
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso eA.hom).2 x
  have hf := continuousModuleHomologyIso_map_apply f i z
  have hg := continuousModuleHomologyIso_map_apply g i z
  have hfg := continuousModuleHomologyIso_map_apply (f + g) i z
  have hAdd : F.map (f + g) = F.map f + F.map g := F.map_add
  have heval : F.map (f + g) z = F.map f z + F.map g z := ConcreteCategory.congr_hom hAdd z
  calc
    _ = eB.hom (F.map (f + g) z) := hfg.symm
    _ = eB.hom (F.map f z + F.map g z) := congrArg eB.hom heval
    _ = eB.hom (F.map f z) + eB.hom (F.map g z) := map_add eB.hom.hom _ _
    _ = _ := congrArg₂ (· + ·) hf hg

variable [LocallyCompactSpace G]

/-- The connecting map transported back to the original continuous
cohomology from the short exact sequence of continuous cochains. -/
def discreteCoefficientConnecting (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ) :
    continuousCohomology i S.X₃ →+ continuousCohomology (i + 1) S.X₁ :=
  ((continuousModuleHomologyIso G S.X₃ i).inv ≫ hS.δ i (i + 1) rfl ≫
    (continuousModuleHomologyIso G S.X₁ (i + 1)).hom).hom.toAddMonoidHom

/-- On the original classes the connecting map is computed by taking the
boundary of any lift and using its specified preimage under the first map. -/
theorem discreteCoefficientConnecting_apply_of_lift
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (z : cocycles S.X₃ i) (w : cocycles S.X₁ (i + 1))
    (b : ((continuousModuleComplexFunctor G).obj S.X₂).X i)
    (hb : ((S.map (continuousModuleComplexFunctor G)).g.f i) b =
      (homogeneousCochains S.X₃).iCycles i z)
    (hw : ((S.map (continuousModuleComplexFunctor G)).f.f (i + 1))
      ((homogeneousCochains S.X₁).iCycles (i + 1) w) =
        ((continuousModuleComplexFunctor G).obj S.X₂).d i (i + 1) b) :
    discreteCoefficientConnecting S hS i (π S.X₃ i z) = π S.X₁ (i + 1) w := by
  let T := S.map (continuousModuleComplexFunctor G)
  let c := moduleCycle S.X₃ i z
  let a := moduleCycle S.X₁ (i + 1) w
  let v := T.X₃.iCycles i c
  let u := T.X₁.iCycles (i + 1) a
  have hv : T.X₃.d i (i + 1) v = 0 := by
    exact ConcreteCategory.congr_hom (T.X₃.iCycles_d i (i + 1)) c
  have hb' : T.g.f i b = v := hb.trans (moduleCycle_iCycles S.X₃ i z).symm
  have hw' : T.f.f (i + 1) u = T.X₂.d i (i + 1) b :=
    (congrArg (T.f.f (i + 1)) (moduleCycle_iCycles S.X₁ (i + 1) w)).trans hw
  have hnext : (ComplexShape.up ℕ).next (i + 1) = i + 1 + 1 :=
    (ComplexShape.up ℕ).next_eq' rfl
  let c' := T.X₃.cyclesMk v (i + 1) ((ComplexShape.up ℕ).next_eq' rfl) hv
  let a' := T.X₁.cyclesMk u (i + 1 + 1) hnext
    (hS.d_eq_zero_of_f_eq_d_apply i (i + 1) b u hw' (i + 1 + 1))
  have hsource : c' = c := by
    apply (ModuleCat.mono_iff_injective (T.X₃.iCycles i)).mp inferInstance
    exact T.X₃.i_cyclesMk _ _ _ _
  have htarget : a' = a := by
    apply (ModuleCat.mono_iff_injective (T.X₁.iCycles (i + 1))).mp inferInstance
    exact T.X₁.i_cyclesMk _ _ _ _
  have h : hS.δ i (i + 1) rfl (T.X₃.homologyπ i c') = T.X₁.homologyπ (i + 1) a' :=
    hS.δ_apply i (i + 1) rfl v hv b hb' u hw' (i + 1 + 1) hnext
  have hδ : hS.δ i (i + 1) rfl (T.X₃.homologyπ i c) = T.X₁.homologyπ (i + 1) a :=
    (congrArg (fun x => hS.δ i (i + 1) rfl (T.X₃.homologyπ i x)) hsource).symm.trans
      (h.trans (congrArg (T.X₁.homologyπ (i + 1)) htarget))
  let e := continuousModuleHomologyIso G S.X₃ i
  let e' := continuousModuleHomologyIso G S.X₁ (i + 1)
  have hclass : e.inv (π S.X₃ i z) = T.X₃.homologyπ i c :=
    (congrArg e.inv (moduleCycle_homologyπ S.X₃ i z)).symm.trans
      (Iso.hom_inv_id_apply e (T.X₃.homologyπ i c))
  change e'.hom (hS.δ i (i + 1) rfl (e.inv (π S.X₃ i z))) = _
  calc
    _ = e'.hom (hS.δ i (i + 1) rfl (T.X₃.homologyπ i c)) :=
      congrArg (fun x => e'.hom (hS.δ i (i + 1) rfl x)) hclass
    _ = e'.hom (T.X₁.homologyπ (i + 1) a) := congrArg e'.hom hδ
    _ = _ := moduleCycle_homologyπ S.X₁ (i + 1) w

/-- Degreewise exactness supplies the cochain lifts that compute the
connecting map on every original cocycle. -/
theorem exists_discreteCoefficientConnecting_lift
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (z : cocycles S.X₃ i) :
    ∃ (b : ((continuousModuleComplexFunctor G).obj S.X₂).X i) (w : cocycles S.X₁ (i + 1)),
      ((S.map (continuousModuleComplexFunctor G)).g.f i) b =
        (homogeneousCochains S.X₃).iCycles i z ∧
      ((S.map (continuousModuleComplexFunctor G)).f.f (i + 1))
        ((homogeneousCochains S.X₁).iCycles (i + 1) w) =
          ((continuousModuleComplexFunctor G).obj S.X₂).d i (i + 1) b := by
  let T := S.map (continuousModuleComplexFunctor G)
  let v := T.X₃.iCycles i (moduleCycle S.X₃ i z)
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hS
  have he := (hs i).epi_g
  change Epi (T.g.f i) at he
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective _).mp he v
  have hv : T.X₃.d i (i + 1) v = 0 := by
    exact ConcreteCategory.congr_hom (T.X₃.iCycles_d i (i + 1)) (moduleCycle S.X₃ i z)
  have hd : T.g.f (i + 1) (T.X₂.d i (i + 1) b) = 0 := by
    have h := ConcreteCategory.congr_hom (T.g.comm i (i + 1)) b
    exact h.symm.trans ((congrArg (T.X₃.d i (i + 1)) hb).trans hv)
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hs (i + 1)).exact _ hd
  change T.f.f (i + 1) a = T.X₂.d i (i + 1) b at ha
  let c := T.X₁.cyclesMk a (i + 1 + 1) ((ComplexShape.up ℕ).next_eq' rfl)
    (hS.d_eq_zero_of_f_eq_d_apply i (i + 1) b a ha (i + 1 + 1))
  let F := forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)
  let e := ((homogeneousCochains S.X₁).sc (i + 1)).mapCyclesIso F
  let w : cocycles S.X₁ (i + 1) := e.hom c
  have hw : moduleCycle S.X₁ (i + 1) w = c := Iso.hom_inv_id_apply e c
  have hci : T.X₁.iCycles (i + 1) c = a := T.X₁.i_cyclesMk _ _ _ _
  have hcochain : a = (homogeneousCochains S.X₁).iCycles (i + 1) w :=
    hci.symm.trans ((congrArg (T.X₁.iCycles (i + 1)) hw).symm.trans
      (moduleCycle_iCycles S.X₁ (i + 1) w))
  exact ⟨b, w, hb.trans (moduleCycle_iCycles S.X₃ i z),
    (congrArg (T.f.f (i + 1)) hcochain).symm.trans ha⟩

/-- Exactness at the middle coefficient holds on original continuous classes. -/
theorem exists_continuousCohomology_preimage_of_map_eq_zero
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (y : continuousCohomology i S.X₂) (hy : map (ContinuousMonoidHom.id G) S.g i y = 0) :
    ∃ x : continuousCohomology i S.X₁, map (ContinuousMonoidHom.id G) S.f i x = y := by
  let T := S.map (continuousModuleComplexFunctor G)
  let eA := continuousModuleHomologyIso G S.X₁ i
  let eB := continuousModuleHomologyIso G S.X₂ i
  let eC := continuousModuleHomologyIso G S.X₃ i
  have hz : HomologicalComplex.homologyMap T.g i (eB.inv y) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso eC.hom).1
    have h := continuousModuleHomologyIso_map_apply S.g i (eB.inv y)
    have he : eB.hom (eB.inv y) = y := Iso.inv_hom_id_apply eB y
    exact h.trans ((congrArg (map (ContinuousMonoidHom.id G) S.g i) he).trans
      (hy.trans (map_zero eC.hom.hom).symm))
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ i) _ hz
  refine ⟨eA.hom x, ?_⟩
  have h := continuousModuleHomologyIso_map_apply S.f i x
  exact h.symm.trans ((congrArg eB.hom hx).trans (Iso.inv_hom_id_apply eB y))

/-- A class killed by the first coefficient map is an actual connecting image. -/
theorem exists_discreteCoefficientConnecting_preimage_of_map_eq_zero
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (x : continuousCohomology (i + 1) S.X₁)
    (hx : map (ContinuousMonoidHom.id G) S.f (i + 1) x = 0) :
    ∃ z : continuousCohomology i S.X₃, discreteCoefficientConnecting S hS i z = x := by
  let T := S.map (continuousModuleComplexFunctor G)
  let eA := continuousModuleHomologyIso G S.X₁ (i + 1)
  let eB := continuousModuleHomologyIso G S.X₂ (i + 1)
  let eC := continuousModuleHomologyIso G S.X₃ i
  have hy : HomologicalComplex.homologyMap T.f (i + 1) (eA.inv x) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso eB.hom).1
    have h := continuousModuleHomologyIso_map_apply S.f (i + 1) (eA.inv x)
    have he : eA.hom (eA.inv x) = x := Iso.inv_hom_id_apply eA x
    exact h.trans ((congrArg (map (ContinuousMonoidHom.id G) S.f (i + 1)) he).trans
      (hx.trans (map_zero eB.hom.hom).symm))
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ i (i + 1) rfl) _ hy
  refine ⟨eC.hom z, ?_⟩
  let δ := hS.δ i (i + 1) rfl
  change eA.hom (δ (eC.inv (eC.hom z))) = x
  exact (congrArg (fun b => eA.hom (δ b)) (Iso.hom_inv_id_apply eC z)).trans
    ((congrArg eA.hom hz).trans (Iso.inv_hom_id_apply eA x))

/-- A class killed by the connecting map lifts to a class on the middle
coefficient. -/
theorem exists_continuousCohomology_preimage_of_connecting_eq_zero
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (z : continuousCohomology i S.X₃) (hz : discreteCoefficientConnecting S hS i z = 0) :
    ∃ y : continuousCohomology i S.X₂, map (ContinuousMonoidHom.id G) S.g i y = z := by
  let eA := continuousModuleHomologyIso G S.X₁ (i + 1)
  let eB := continuousModuleHomologyIso G S.X₂ i
  let eC := continuousModuleHomologyIso G S.X₃ i
  have hz' : hS.δ i (i + 1) rfl (eC.inv z) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso eA.hom).1
    exact hz.trans (map_zero eA.hom.hom).symm
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₃ i (i + 1) rfl) _ hz'
  refine ⟨eB.hom y, ?_⟩
  have h := continuousModuleHomologyIso_map_apply S.g i y
  exact h.symm.trans ((congrArg eC.hom hy).trans (Iso.inv_hom_id_apply eC z))

/-- The neighbor after the actual continuous connecting map kills its image. -/
theorem continuousCohomology_map_connecting_eq_zero
    (S : ShortComplex (TopRep.{u} ℤ G))
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ)
    (z : continuousCohomology i S.X₃) :
    map (ContinuousMonoidHom.id G) S.f (i + 1) (discreteCoefficientConnecting S hS i z) = 0 := by
  let T := S.map (continuousModuleComplexFunctor G)
  let eB := continuousModuleHomologyIso G S.X₂ (i + 1)
  let eC := continuousModuleHomologyIso G S.X₃ i
  let x := hS.δ i (i + 1) rfl (eC.inv z)
  have hz : HomologicalComplex.homologyMap T.f (i + 1) x = 0 :=
    ConcreteCategory.congr_hom (hS.δ_comp i (i + 1) rfl) (eC.inv z)
  have h := continuousModuleHomologyIso_map_apply S.f (i + 1) x
  exact h.symm.trans ((congrArg eB.hom hz).trans (map_zero eB.hom.hom))

/-- An exponent of the original coefficients annihilates continuous
cohomology in every degree. -/
theorem nsmul_continuousCohomology_eq_zero_of_coefficients
    (A : TopRep.{u} ℤ G) (n : ℕ) (hA : ∀ a : A, n • a = 0)
    (i : ℕ) (x : continuousCohomology i A) : n • x = 0 := by
  have hEval (m : ℕ) (a : A) : (m • (𝟙 A : A ⟶ A)) a = m • a := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [succ_nsmul, succ_nsmul]
      change (m • (𝟙 A : A ⟶ A)) a + a = m • a + a
      rw [ih]
  have hAnn : n • (𝟙 A : A ⟶ A) = 0 := by
    let : Module ℤ A := A.hV2
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := A.ρ) (π₂ := A.ρ)
    apply ContinuousLinearMap.ext
    intro a
    exact (hEval n a).trans (hA a)
  let H := continuousModuleComplexFunctor G ⋙ HomologicalComplex.homologyFunctor
    (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) i
  have hmap : H.map (n • (𝟙 A : A ⟶ A)) = n • H.map (𝟙 A) := H.map_nsmul
  have hid : H.map (𝟙 A) = 𝟙 (H.obj A) := H.map_id A
  have hzeroMap : H.map (0 : A ⟶ A) = 0 := H.map_zero A A
  have h : n • (𝟙 (H.obj A)) = 0 := (congrArg (n • ·) hid).symm.trans
    (hmap.symm.trans ((congrArg (fun f : A ⟶ A => H.map f) hAnn).trans hzeroMap))
  let e := continuousModuleHomologyIso G A i
  have hzero : n • e.inv x = 0 := ConcreteCategory.congr_hom h (e.inv x)
  calc
    _ = n • e.hom (e.inv x) := congrArg (n • ·) (Iso.inv_hom_id_apply e x).symm
    _ = e.hom (n • e.inv x) := (map_nsmul e.hom.hom n (e.inv x)).symm
    _ = 0 := by rw [hzero, map_zero]

end ContinuousCohomology
