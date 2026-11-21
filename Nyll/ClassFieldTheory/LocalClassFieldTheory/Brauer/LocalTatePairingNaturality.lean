/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteRepresentative
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairing
public import Nyll.GaloisCohomology.Topology.ContinuousDualExactness
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2Naturality
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-! # Coefficient naturality of local Tate pairings -/

@[expose] public section

open CategoryTheory ContinuousCohomology TopRep LocalFieldTheory
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+)

private theorem map_oneCocycle_apply {G H : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {A : TopRep.{u} ℤ G} {B : TopRep.{u} ℤ H} (r : H →ₜ* G)
    (f : TopRep.res r.toMonoidHom A ⟶ B) (z : cocycles A 1) (a b : H) :
    ((homogeneousCochains B).iCycles 1 (cocyclesMap r f 1 z)).val a b =
      f (((homogeneousCochains A).iCycles 1 z).val (r a) (r b)) := by
  have step (i : ℕ) (c : resolutionX A (i + 1)) (x : H) :
      (resolutionMap r f (i + 1) c) x = resolutionMap r f i (c (r x)) := by
    rw [resolutionMap_succ]
    rfl
  have hvalue (c : (homogeneousCochains A).X 1) :
      (((cochainsMap r f).f 1) c).val = resolutionMap r f 2 c.val := by
    rw [cochainsMap_f]
    rfl
  rw [cochainOfMappedCocycle, hvalue, step, step, resolutionMap_zero]

private theorem cupOneOne_maps_of_adjoint
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    {A B D E P : TopRep.{u} ℤ G} (f : A ⟶ B) (g : D ⟶ E)
    (pA : A →ₗ[ℤ] E →ₗ[ℤ] P) (pB : B →ₗ[ℤ] D →ₗ[ℤ] P)
    (hpA : Continuous (fun t : A × E => pA t.1 t.2))
    (hpB : Continuous (fun t : B × D => pB t.1 t.2))
    (heA : ∀ (σ : G) a d, pA (A.ρ σ a) (E.ρ σ d) = P.ρ σ (pA a d))
    (heB : ∀ (σ : G) b d, pB (B.ρ σ b) (D.ρ σ d) = P.ρ σ (pB b d))
    (hfg : ∀ a d, pB (f a) d = pA a (g d))
    (x : continuousCohomology 1 A) (y : continuousCohomology 1 D) :
    cupOneOne pB hpB heB (map (ContinuousMonoidHom.id G) f 1 x) y =
      cupOneOne pA hpA heA x (map (ContinuousMonoidHom.id G) g 1 y) := by
  let i := ContinuousMonoidHom.id G
  let f₁ : TopRep.res i.toMonoidHom A ⟶ B := f
  let g₁ : TopRep.res i.toMonoidHom D ⟶ E := g
  obtain ⟨x₀, rfl⟩ := π_surjective A 1 x
  obtain ⟨y₀, rfl⟩ := π_surjective D 1 y
  have hx : map i f₁ 1 (π A 1 x₀) = π B 1 (cocyclesMap i f₁ 1 x₀) :=
    ConcreteCategory.congr_hom (π_map i f₁ 1) x₀
  have hy : map i g₁ 1 (π D 1 y₀) = π E 1 (cocyclesMap i g₁ 1 y₀) :=
    ConcreteCategory.congr_hom (π_map i g₁ 1) y₀
  change cupOneOne pB hpB heB (map i f₁ 1 (π A 1 x₀)) (π D 1 y₀) =
    cupOneOne pA hpA heA (π A 1 x₀) (map i g₁ 1 (π D 1 y₀))
  rw [hx, hy, cupOneOne_π, cupOneOne_π]
  apply congrArg (π P 2)
  apply cochain_cocycle_injective P 2
  rw [iCycles_cupOneOneCocycle, iCycles_cupOneOneCocycle]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  rw [cupOneOneCochain_apply, cupOneOneCochain_apply, map_oneCocycle_apply, map_oneCocycle_apply]
  exact hfg (((homogeneousCochains A).iCycles 1 x₀).val a b)
    (((homogeneousCochains D).iCycles 1 y₀).val b c)

/-- The connecting map for a dual short exact sequence on the original dual coefficients. -/
def discreteDualCoefficientConnecting
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (Y : TopRep.{u, 0, u} ℤ G) (S : ShortComplex (TopRep.{u, 0, u} ℤ G))
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := G) Y S).map
      (continuousModuleComplexFunctor G)).ShortExact)
    (d : ℕ) :
    continuousCohomology d (discreteLinearDual (R := ℤ) (G := G) S.X₁ Y) →+
      continuousCohomology (d + 1) (discreteLinearDual (R := ℤ) (G := G) S.X₃ Y) := by
  let D : ShortComplex (TopRep.{u, 0, u} ℤ G) := discreteLinearDualShortComplex
    (R := ℤ) (G := G) Y S
  let δ := discreteCoefficientConnecting (G := G) D hD d
  change continuousCohomology d D.X₃ →+ continuousCohomology (d + 1) D.X₁
  exact δ

/-- The dual connecting class is computed by the boundary of a lift. -/
theorem discreteDualCoefficientConnecting_apply_of_lift
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (Y : TopRep.{u, 0, u} ℤ G) (S : ShortComplex (TopRep.{u, 0, u} ℤ G))
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := G) Y S).map
      (continuousModuleComplexFunctor G)).ShortExact) (i : ℕ) :
    let D := discreteLinearDualShortComplex (R := ℤ) (G := G) Y S
    ∀ (z : cocycles D.X₃ i) (w : cocycles D.X₁ (i + 1))
      (b : ((continuousModuleComplexFunctor G).obj D.X₂).X i)
      (_ : ((D.map (continuousModuleComplexFunctor G)).g.f i) b =
        (homogeneousCochains D.X₃).iCycles i z)
      (_ : ((D.map (continuousModuleComplexFunctor G)).f.f (i + 1))
          ((homogeneousCochains D.X₁).iCycles (i + 1) w) =
        ((continuousModuleComplexFunctor G).obj D.X₂).d i (i + 1) b),
      discreteDualCoefficientConnecting Y S hD i (π D.X₃ i z) = π D.X₁ (i + 1) w := by
  intro D z w b hb hw
  exact discreteCoefficientConnecting_apply_of_lift D hD i z w b hb hw

private theorem map_hZero_apply {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {A B : TopRep.{u} ℤ G} (f : A ⟶ B) (x : continuousCohomology 0 A) :
    ((zeroIso B).hom (map (ContinuousMonoidHom.id G) f 0 x)).val = f (((zeroIso A).hom x).val) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (zeroIso_hom_naturality A B f) x)

local notation "Γabs" => Gal(SeparableClosure K/K)
local notation "Mu" => separableMuTopRep K n

/-- On the original degree-one local pairing the map on coefficients is
adjoint to precomposition on the Kummer dual. -/
theorem localTatePairingOne_coefficientMap
    {A B : TopRep.{u} ℤ Γabs} [DiscreteTopology A] [DiscreteTopology B] (f : A ⟶ B)
    (hn : ((n : ℕ) : K) ≠ 0) (x : continuousCohomology 1 A)
    (y : continuousCohomology 1 (discreteLinearDual B Mu)) :
    localTatePairingOne K n B hn (map (ContinuousMonoidHom.id Γabs) f 1 x) y =
      localTatePairingOne K n A hn x
        (map (ContinuousMonoidHom.id Γabs) (discreteLinearDualPullback Mu f) 1 y) := by
  have h := cupOneOne_maps_of_adjoint f (discreteLinearDualPullback Mu f)
    (discreteLinearDualIntEvaluation A Mu) (discreteLinearDualIntEvaluation B Mu)
    (discreteLinearDualIntEvaluation_continuous A Mu)
    (discreteLinearDualIntEvaluation_continuous B Mu)
    (discreteLinearDualIntEvaluation_equivariant A Mu)
    (discreteLinearDualIntEvaluation_equivariant B Mu)
    (fun a d => (discreteLinearDualPullback_apply Mu f d a).symm) x y
  exact congrArg (localKummerTrace K n hn) h

/-- On degree zero, coefficient naturality evaluates the actual invariant
element before taking the opposite degree-two class. -/
theorem localTatePairingZero_coefficientMap
    {A B : TopRep.{u} ℤ Γabs} [DiscreteTopology A] [DiscreteTopology B] (f : A ⟶ B)
    (hn : ((n : ℕ) : K) ≠ 0) (x : continuousCohomology 0 A)
    (y : continuousCohomology 2 (discreteLinearDual B Mu)) :
    localTatePairingZero K n B hn (map (ContinuousMonoidHom.id Γabs) f 0 x) y =
      localTatePairingZero K n A hn x
        (map (ContinuousMonoidHom.id Γabs) (discreteLinearDualPullback Mu f) 2 y) := by
  let D₁ := discreteLinearDual A Mu
  let D₂ := discreteLinearDual B Mu
  let i := ContinuousMonoidHom.id Γabs
  let fD : D₂ ⟶ D₁ := discreteLinearDualPullback Mu f
  let pA := discreteLinearDualIntEvaluation A Mu
  let pB := discreteLinearDualIntEvaluation B Mu
  let a := (zeroIso A).hom x
  let b := (zeroIso B).hom (map i f 0 x)
  let kA : D₁ ⟶ Mu := cupLeftInvariant pA
    (discreteLinearDualIntEvaluation_continuous A Mu)
    (discreteLinearDualIntEvaluation_equivariant A Mu) a
  let kB : D₂ ⟶ Mu := cupLeftInvariant pB
    (discreteLinearDualIntEvaluation_continuous B Mu)
    (discreteLinearDualIntEvaluation_equivariant B Mu) b
  have hb : b.val = f a.val := map_hZero_apply f x
  have hcoeff (z : D₂) : kB z = (fD ≫ kA) z := by
    change pB b.val z = pA a.val (fD z)
    calc
      pB b.val z = pB (f a.val) z := congrArg (fun a' : B => pB a' z) hb
      _ = pA a.val (fD z) := (discreteLinearDualPullback_apply Mu f z a.val).symm
  have h := ConcreteCategory.congr_hom
    (map_eq_of_values 2 (r := i) (s := i) kB (fD ≫ kA) (fun _ => rfl) hcoeff) y
  have hcomp := map_id_comp_apply D₂ D₁ fD kA 2 y
  exact congrArg (localKummerTrace K n hn) (h.trans hcomp.symm)

/-- Coefficient naturality in degree two is evaluation against the
actual invariant dual coefficient. -/
theorem localTatePairingTwo_coefficientMap
    {A B : TopRep.{u} ℤ Γabs} [DiscreteTopology A] [DiscreteTopology B] (f : A ⟶ B)
    (hn : ((n : ℕ) : K) ≠ 0) (x : continuousCohomology 2 A)
    (y : continuousCohomology 0 (discreteLinearDual B Mu)) :
    localTatePairingTwo K n B hn (map (ContinuousMonoidHom.id Γabs) f 2 x) y =
      localTatePairingTwo K n A hn x
        (map (ContinuousMonoidHom.id Γabs) (discreteLinearDualPullback Mu f) 0 y) := by
  let D₁ := discreteLinearDual A Mu
  let D₂ := discreteLinearDual B Mu
  let i := ContinuousMonoidHom.id Γabs
  let fD : D₂ ⟶ D₁ := discreteLinearDualPullback Mu f
  let pA := discreteLinearDualIntEvaluation A Mu
  let pB := discreteLinearDualIntEvaluation B Mu
  let b := (zeroIso D₂).hom y
  let a := (zeroIso D₁).hom (map i fD 0 y)
  let kA : A ⟶ Mu := rightInvariantCoefficientMap pA
    (discreteLinearDualIntEvaluation_continuous A Mu)
    (discreteLinearDualIntEvaluation_equivariant A Mu) a
  let kB : B ⟶ Mu := rightInvariantCoefficientMap pB
    (discreteLinearDualIntEvaluation_continuous B Mu)
    (discreteLinearDualIntEvaluation_equivariant B Mu) b
  have ha : a.val = fD b.val := map_hZero_apply fD y
  have hcoeff (z : A) : (f ≫ kB) z = kA z := by
    change pB (f z) b.val = pA z a.val
    calc
      pB (f z) b.val = pA z (fD b.val) := (discreteLinearDualPullback_apply Mu f b.val z).symm
      _ = pA z a.val := congrArg (pA z) ha.symm
  have h := ConcreteCategory.congr_hom
    (map_eq_of_values 2 (r := i) (s := i) (f ≫ kB) kA (fun _ => rfl) hcoeff) x
  have hcomp := map_id_comp_apply A B f kB 2 x
  exact congrArg (localKummerTrace K n hn) (hcomp.trans h)

private theorem cup_connectingZero
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (Y : TopRep.{u} ℤ G) (S : ShortComplex (TopRep.{u} ℤ G))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact)
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := G) Y S).map
      (continuousModuleComplexFunctor G)).ShortExact)
    (x : continuousCohomology 0 S.X₃) (y : continuousCohomology 1 (discreteLinearDual S.X₁ Y)) :
    let p := fun A : TopRep.{u} ℤ G => discreteLinearDualIntEvaluation A Y
    let hp := fun (A : TopRep.{u} ℤ G) [DiscreteTopology A] =>
      discreteLinearDualIntEvaluation_continuous A Y
    let he := fun A : TopRep.{u} ℤ G => discreteLinearDualIntEvaluation_equivariant A Y
    cupOneOne (p S.X₁) (hp S.X₁) (he S.X₁) (discreteCoefficientConnecting S hS 0 x) y =
      -cupZeroTwo (p S.X₃) (hp S.X₃) (he S.X₃) x
        (discreteDualCoefficientConnecting Y S hD 1 y) := by
  intro p hp he
  let A := S.X₁
  let B := S.X₂
  let C := S.X₃
  let DA := discreteLinearDual A Y
  let DB := discreteLinearDual B Y
  let DC := discreteLinearDual C Y
  let T := discreteLinearDualShortComplex (R := ℤ) (G := G) Y S
  obtain ⟨x₀, rfl⟩ := π_surjective C 0 x
  obtain ⟨y₀, rfl⟩ := π_surjective DA 1 y
  obtain ⟨b₀, w₀, hb, hw⟩ := exists_discreteCoefficientConnecting_lift S hS 0 x₀
  obtain ⟨d₀, t₀, hd, ht⟩ := exists_discreteCoefficientConnecting_lift T hD 1 y₀
  let b : (homogeneousCochains B).X 0 := b₀
  let w : cocycles A 1 := w₀
  let d : (homogeneousCochains DB).X 1 := d₀
  let t : cocycles DC 2 := t₀
  have hDualClass :
      discreteDualCoefficientConnecting (G := G) Y S hD 1 (π DA 1 y₀) =
        π DC 2 t :=
    discreteDualCoefficientConnecting_apply_of_lift (G := G) Y S hD 1 y₀ t d hd ht
  rw [discreteCoefficientConnecting_apply_of_lift S hS 0 x₀ w b hb hw]
  refine Eq.trans ?_ (congrArg (fun z : continuousCohomology 2 DC =>
    -cupZeroTwo (p C) (hp C) (he C) (π C 0 x₀) z) hDualClass).symm
  rw [eq_neg_iff_add_eq_zero]
  let u := cupOneOneCocycle (discreteLinearDualIntEvaluation A Y)
    (discreteLinearDualIntEvaluation_continuous A Y)
    (discreteLinearDualIntEvaluation_equivariant A Y) w y₀
  obtain ⟨v, hv, hve⟩ := exists_cupZeroTwo_cocycle (discreteLinearDualIntEvaluation C Y)
    (discreteLinearDualIntEvaluation_continuous C Y)
    (discreteLinearDualIntEvaluation_equivariant C Y) x₀ t
  let q := cupZeroOneCochain (discreteLinearDualIntEvaluation B Y)
    (discreteLinearDualIntEvaluation_continuous B Y)
    (discreteLinearDualIntEvaluation_equivariant B Y) b d
  have hboundary : (homogeneousCochains Y).d 1 2 q = (homogeneousCochains Y).iCycles 2 (u + v) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro r
    apply ContinuousMap.ext
    intro s
    apply ContinuousMap.ext
    intro t'
    have hb₀ := congrArg (fun z : (homogeneousCochains C).X 0 => z.1 r) hb
    change S.g (b.1 r) = ((homogeneousCochains C).iCycles 0 x₀).1 r at hb₀
    have hw₁ := congrArg (fun z : (homogeneousCochains B).X 1 => z.1 r s) hw
    change S.f (((homogeneousCochains A).iCycles 1 w).1 r s) =
      ((homogeneousCochains B).d 0 1 b).1 r s at hw₁
    have hd₁ := congrArg (fun z : (homogeneousCochains DA).X 1 => z.1 s t') hd
    change discreteLinearDualPullback Y S.f (d.1 s t') =
      ((homogeneousCochains DA).iCycles 1 y₀).1 s t' at hd₁
    have ht₂ := congrArg (fun z : (homogeneousCochains DB).X 2 => z.1 r s t') ht
    change discreteLinearDualPullback Y S.g (((homogeneousCochains DC).iCycles 2 t).1 r s t') =
      ((homogeneousCochains DB).d 1 2 d).1 r s t' at ht₂
    have hq := d_cupZeroOneCochain_apply (discreteLinearDualIntEvaluation B Y)
      (discreteLinearDualIntEvaluation_continuous B Y)
      (discreteLinearDualIntEvaluation_equivariant B Y) b d r s t'
    change ((homogeneousCochains Y).d 1 2
      (cupZeroOneCochain (discreteLinearDualIntEvaluation B Y)
        (discreteLinearDualIntEvaluation_continuous B Y)
        (discreteLinearDualIntEvaluation_equivariant B Y) b d)).1 r s t' = _
    rw [hq, ← hw₁, ← ht₂]
    let j := ((homogeneousCochains Y).iCycles 2).hom
    have hsum : (j (u + v)).1 r s t' = (j u).1 r s t' + (j v).1 r s t' :=
      congrArg (fun z : (homogeneousCochains Y).X 2 => z.1 r s t') (map_add j u v)
    rw [hsum]
    rw [show u = cupOneOneCocycle (discreteLinearDualIntEvaluation A Y)
      (discreteLinearDualIntEvaluation_continuous A Y)
      (discreteLinearDualIntEvaluation_equivariant A Y) w y₀ from rfl,
      iCycles_cupOneOneCocycle, cupOneOneCochain_apply, hve r s t', ← hd₁, ← hb₀]
    simp only [discreteLinearDualIntEvaluation_apply, discreteLinearDualPullback_apply]
    rfl
  have hz := class_zero_of_degreeTwo_boundary (u + v) q hboundary
  rw [map_add, hv] at hz
  rw [cupOneOne_π]
  exact hz

private theorem cup_connectingOne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (Y : TopRep.{u} ℤ G) (S : ShortComplex (TopRep.{u} ℤ G))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor G)).ShortExact)
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := G) Y S).map
      (continuousModuleComplexFunctor G)).ShortExact)
    (x : continuousCohomology 1 S.X₃) (y : continuousCohomology 0 (discreteLinearDual S.X₁ Y)) :
    let p := fun A : TopRep.{u} ℤ G => discreteLinearDualIntEvaluation A Y
    let hp := fun (A : TopRep.{u} ℤ G) [DiscreteTopology A] =>
      discreteLinearDualIntEvaluation_continuous A Y
    let he := fun A : TopRep.{u} ℤ G => discreteLinearDualIntEvaluation_equivariant A Y
    cupTwoZero (p S.X₁) (hp S.X₁) (he S.X₁) (discreteCoefficientConnecting S hS 1 x) y =
      cupOneOne (p S.X₃) (hp S.X₃) (he S.X₃) x (discreteDualCoefficientConnecting Y S hD 0 y) := by
  intro p hp he
  let A := S.X₁
  let B := S.X₂
  let C := S.X₃
  let DA := discreteLinearDual A Y
  let DB := discreteLinearDual B Y
  let DC := discreteLinearDual C Y
  let T := discreteLinearDualShortComplex (R := ℤ) (G := G) Y S
  obtain ⟨x₀, rfl⟩ := π_surjective C 1 x
  obtain ⟨y₀, rfl⟩ := π_surjective DA 0 y
  obtain ⟨b₀, w₀, hb, hw⟩ := exists_discreteCoefficientConnecting_lift S hS 1 x₀
  obtain ⟨d₀, t₀, hd, ht⟩ := exists_discreteCoefficientConnecting_lift T hD 0 y₀
  let b : (homogeneousCochains B).X 1 := b₀
  let w : cocycles A 2 := w₀
  let d : (homogeneousCochains DB).X 0 := d₀
  let t : cocycles DC 1 := t₀
  have hDualClass :
      discreteDualCoefficientConnecting (G := G) Y S hD 0 (π DA 0 y₀) =
        π DC 1 t :=
    discreteDualCoefficientConnecting_apply_of_lift (G := G) Y S hD 0 y₀ t d hd ht
  rw [discreteCoefficientConnecting_apply_of_lift S hS 1 x₀ w b hb hw]
  refine Eq.trans ?_ (congrArg (fun z : continuousCohomology 1 DC =>
    cupOneOne (p C) (hp C) (he C) (π C 1 x₀) z) hDualClass).symm
  obtain ⟨u, hu, hue⟩ := exists_cupTwoZero_cocycle (discreteLinearDualIntEvaluation A Y)
    (discreteLinearDualIntEvaluation_continuous A Y)
    (discreteLinearDualIntEvaluation_equivariant A Y) w y₀
  let v := cupOneOneCocycle (discreteLinearDualIntEvaluation C Y)
    (discreteLinearDualIntEvaluation_continuous C Y)
    (discreteLinearDualIntEvaluation_equivariant C Y) x₀ t
  let q := cupOneZeroCochain (discreteLinearDualIntEvaluation B Y)
    (discreteLinearDualIntEvaluation_continuous B Y)
    (discreteLinearDualIntEvaluation_equivariant B Y) b d
  have hboundary : (homogeneousCochains Y).d 1 2 q = (homogeneousCochains Y).iCycles 2 (u - v) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro r
    apply ContinuousMap.ext
    intro s
    apply ContinuousMap.ext
    intro t'
    have hb₁ := congrArg (fun z : (homogeneousCochains C).X 1 => z.1 r s) hb
    change S.g (b.1 r s) = ((homogeneousCochains C).iCycles 1 x₀).1 r s at hb₁
    have hw₂ := congrArg (fun z : (homogeneousCochains B).X 2 => z.1 r s t') hw
    change S.f (((homogeneousCochains A).iCycles 2 w).1 r s t') =
      ((homogeneousCochains B).d 1 2 b).1 r s t' at hw₂
    have hd₀ := congrArg (fun z : (homogeneousCochains DA).X 0 => z.1 t') hd
    change discreteLinearDualPullback Y S.f (d.1 t') =
      ((homogeneousCochains DA).iCycles 0 y₀).1 t' at hd₀
    have ht₁ := congrArg (fun z : (homogeneousCochains DB).X 1 => z.1 s t') ht
    change discreteLinearDualPullback Y S.g (((homogeneousCochains DC).iCycles 1 t).1 s t') =
      ((homogeneousCochains DB).d 0 1 d).1 s t' at ht₁
    have hq := d_cupOneZeroCochain_apply (discreteLinearDualIntEvaluation B Y)
      (discreteLinearDualIntEvaluation_continuous B Y)
      (discreteLinearDualIntEvaluation_equivariant B Y) b d r s t'
    change ((homogeneousCochains Y).d 1 2
      (cupOneZeroCochain (discreteLinearDualIntEvaluation B Y)
        (discreteLinearDualIntEvaluation_continuous B Y)
        (discreteLinearDualIntEvaluation_equivariant B Y) b d)).1 r s t' = _
    rw [hq, ← hw₂, ← ht₁]
    let j := ((homogeneousCochains Y).iCycles 2).hom
    have hsum : (j (u - v)).1 r s t' = (j u).1 r s t' - (j v).1 r s t' :=
      congrArg (fun z : (homogeneousCochains Y).X 2 => z.1 r s t') (map_sub j u v)
    rw [hsum]
    rw [show v = cupOneOneCocycle (discreteLinearDualIntEvaluation C Y)
      (discreteLinearDualIntEvaluation_continuous C Y)
      (discreteLinearDualIntEvaluation_equivariant C Y) x₀ t from rfl,
      iCycles_cupOneOneCocycle, cupOneOneCochain_apply, hue r s t', ← hd₀, ← hb₁]
    simp only [discreteLinearDualIntEvaluation_apply, discreteLinearDualPullback_apply]
    rfl
  have hz := class_zero_of_degreeTwo_boundary (u - v) q hboundary
  rw [map_sub, hu] at hz
  rw [cupOneOne_π]
  exact sub_eq_zero.mp hz

/-- The degree-zero coefficient boundary is adjoint to the opposite
degree-one boundary with the negative Alexander–Whitney sign. -/
theorem localTatePairing_connectingZero
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := Γabs) Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (x : continuousCohomology 0 S.X₃) (y : continuousCohomology 1 (discreteLinearDual S.X₁ Mu)) :
    localTatePairingOne K n S.X₁ hn (discreteCoefficientConnecting S hS 0 x) y =
      -localTatePairingZero K n S.X₃ hn x
        (discreteDualCoefficientConnecting (G := Γabs) Mu S hD 1 y) := by
  unfold localTatePairingOne localTatePairingZero
  rw [← map_neg]
  exact congrArg (localKummerTrace K n hn) (cup_connectingZero Mu S hS hD x y)

/-- The degree-one coefficient boundary is adjoint to the opposite
degree-zero boundary with the positive sign. -/
theorem localTatePairing_connectingOne
    (hn : ((n : ℕ) : K) ≠ 0) (S : ShortComplex (TopRep.{u} ℤ Γabs))
    [DiscreteTopology S.X₁] [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hS : (S.map (continuousModuleComplexFunctor Γabs)).ShortExact)
    (hD : ((discreteLinearDualShortComplex (R := ℤ) (G := Γabs) Mu S).map
      (continuousModuleComplexFunctor Γabs)).ShortExact)
    (x : continuousCohomology 1 S.X₃) (y : continuousCohomology 0 (discreteLinearDual S.X₁ Mu)) :
    localTatePairingTwo K n S.X₁ hn (discreteCoefficientConnecting S hS 1 x) y =
      localTatePairingOne K n S.X₃ hn x
        (discreteDualCoefficientConnecting (G := Γabs) Mu S hD 0 y) := by
  unfold localTatePairingTwo localTatePairingOne
  exact congrArg (localKummerTrace K n hn) (cup_connectingOne Mu S hS hD x y)

end ClassFieldTheory.Brauer
