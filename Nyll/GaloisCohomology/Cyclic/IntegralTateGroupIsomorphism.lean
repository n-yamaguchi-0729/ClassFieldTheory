/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Data.Finsupp.Ext
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation
public import Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison

/-!
# Reindexing and conjugation on integral Tate cohomology

The comparison reindexes actual chains and cochains along the indicated
group equivalence. For subgroup conjugation it applies the ambient action
of the conjugating element to the original coefficients.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G H : Type u} [Group G] [Group H]

/-- A group equivalence on the same lifted group carriers as the Tate complex. -/
def nativeGroupEquiv (e : G ≃* H) : ULift.{v} G ≃* ULift.{v} H :=
  (MulEquiv.ulift : ULift.{v} G ≃* G).trans (e.trans MulEquiv.ulift.symm)

variable [Fintype G] [Fintype H]

omit [Fintype G] [Fintype H] in
/-- Group reindexing on the native Tate complex keeps the same coefficient. -/
theorem nativeTateReindex_refl_comm (e : G ≃* H) (A : Rep.{v} ℤ G) (g : ULift.{v} G) :
    let X := (nativeFunctor G).obj A
    let Y := (nativeFunctor H).obj (Rep.res e.symm.toMonoidHom A)
    let l : X.V ≃ₗ[ULift.{max u v} ℤ] Y.V := LinearEquiv.refl _ _
    l.toLinearMap ∘ₗ X.ρ g = Y.ρ (nativeGroupEquiv e g) ∘ₗ l.toLinearMap := by
  apply LinearMap.ext
  intro x
  change ULift.up (A.ρ g.down x.down) = ULift.up (A.ρ (e.symm (e g.down)) x.down)
  rw [e.symm_apply_apply]

/-- The actual Tate complex isomorphism under the given group reindexing. -/
def nativeTateReindexComplexIso (e : G ≃* H) (A : Rep.{v} ℤ G) :
    tateComplex ((nativeFunctor G).obj A) ≅
      tateComplex ((nativeFunctor H).obj (Rep.res e.symm.toMonoidHom A)) :=
  TateCohomology.groupEquivComplexIso (nativeGroupEquiv e) (LinearEquiv.refl _ _)
    (nativeTateReindex_refl_comm e A)

/-- The reindexing of the original Tate complex is natural in the coefficient. -/
def nativeTateReindexNatIso (e : G ≃* H) :
    nativeFunctor.{u, v} G ⋙ tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} G) ≅
      Rep.resFunctor e.symm.toMonoidHom ⋙ nativeFunctor.{u, v} H ⋙
        tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} H) :=
  NatIso.ofComponents (nativeTateReindexComplexIso e) (by
    intro A B f
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | ofNat n =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    | negSucc n =>
      let A' := (nativeFunctor G).obj A
      let B' := (nativeFunctor G).obj B
      let A'' := (nativeFunctor H).obj (Rep.res e.symm.toMonoidHom A)
      let B'' := (nativeFunctor H).obj (Rep.res e.symm.toMonoidHom B)
      let idG := MonoidHom.id (ULift.{v} G)
      let idH := MonoidHom.id (ULift.{v} H)
      let q := (nativeGroupEquiv.{u, v} e).toMonoidHom
      let fG : A' ⟶ Rep.res idG B' := (nativeFunctor G).map f
      let fH : A'' ⟶ Rep.res idH B'' :=
        (nativeFunctor H).map ((Rep.resFunctor e.symm.toMonoidHom).map f)
      let aA : A' ⟶ Rep.res q A'' := Rep.ofHom
        ⟨(LinearEquiv.refl _ _).toLinearMap, nativeTateReindex_refl_comm e A⟩
      let aB : B' ⟶ Rep.res q B'' := Rep.ofHom
        ⟨(LinearEquiv.refl _ _).toLinearMap, nativeTateReindex_refl_comm e B⟩
      have hcoef : fG ≫ (Rep.resFunctor idG).map aB = aA ≫ (Rep.resFunctor q).map fH := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.toLinearMap_injective
        exact LinearMap.ext (fun _ => rfl)
      have hc : groupHomology.chainsMap idG fG ≫ groupHomology.chainsMap q aB =
          groupHomology.chainsMap q aA ≫ groupHomology.chainsMap idH fH :=
        (groupHomology.chainsMap_comp idG q fG aB).symm.trans
          ((congrArg (groupHomology.chainsMap q) hcoef).trans
            (groupHomology.chainsMap_comp q idH aA fH))
      exact congrArg (fun f => f.f n) hc)

/-- An isomorphism of acting groups reindexes the original integral Tate
groups in every integer degree and preserves the underlying coefficient. -/
def tateReindexIso (e : G ≃* H) (A : Rep.{v} ℤ G) (n : ℤ) :
    tate A n ≅ tate (Rep.res e.symm.toMonoidHom A) n :=
  IntegralGroupCohomology.integerScalars.mapIso
    ((HomologicalComplex.homologyFunctor (ModuleCat (ULift.{max u v} ℤ))
      (ComplexShape.up ℤ) n).mapIso
      (nativeTateReindexComplexIso e A))

omit [Fintype G] [Fintype H] in
/-- The original short exact sequence retains exactness after reindexing the acting group. -/
theorem reindex_shortExact {S : ShortComplex (Rep.{v} ℤ G)} (e : G ≃* H) (hS : S.ShortExact) :
    (S.map (Rep.resFunctor e.symm.toMonoidHom)).ShortExact := by
  let F := forget₂ (Rep.{v} ℤ G) (ModuleCat.{v} ℤ)
  let F' := forget₂ (Rep.{v} ℤ H) (ModuleCat.{v} ℤ)
  let S' := S.map (Rep.resFunctor e.symm.toMonoidHom)
  have hS' : (S'.map F').ShortExact := hS.map_of_exact F
  exact {
    exact := F'.reflects_exact_of_faithful S' hS'.exact
    mono_f := F'.mono_of_mono_map hS'.mono_f
    epi_g := F'.epi_of_epi_map hS'.epi_g }

/-- Reindexing the acting group commutes with the original Tate connecting maps. -/
theorem tateReindexIso_δ {S : ShortComplex (Rep.{v} ℤ G)} (e : G ≃* H)
    (hS : S.ShortExact) (n : ℤ) :
    tateδ hS n ≫ (tateReindexIso e S.X₁ (n + 1)).hom =
      (tateReindexIso e S.X₃ n).hom ≫ tateδ (reindex_shortExact e hS) n := by
  let X := S.map (nativeFunctor G)
  let Y := (S.map (Rep.resFunctor e.symm.toMonoidHom)).map (nativeFunctor H)
  let E : X.map (tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} G)) ≅
      Y.map (tateComplexFunctor (ULift.{max u v} ℤ) (ULift.{v} H)) :=
    S.mapNatIso (nativeTateReindexNatIso e)
  have hX : X.ShortExact := native_shortExact hS
  have hY : Y.ShortExact := native_shortExact (reindex_shortExact e hS)
  let dX : tateCohomology X.X₃ n ⟶ tateCohomology X.X₁ (n + 1) := TateCohomology.δ hX n
  let dY : tateCohomology Y.X₃ n ⟶ tateCohomology Y.X₁ (n + 1) := TateCohomology.δ hY n
  let c₁ : tateCohomology X.X₁ (n + 1) ⟶ tateCohomology Y.X₁ (n + 1) :=
    HomologicalComplex.homologyMap E.hom.τ₁ (n + 1)
  let c₃ : tateCohomology X.X₃ n ⟶ tateCohomology Y.X₃ n :=
    HomologicalComplex.homologyMap E.hom.τ₃ n
  have h : dX ≫ c₁ = c₃ ≫ dY :=
    HomologicalComplex.HomologySequence.δ_naturality E.hom
      (TateCohomology.map_tateComplexFunctor_shortExact hX)
      (TateCohomology.map_tateComplexFunctor_shortExact hY) n (n + 1) rfl
  change integerScalars.map dX ≫ integerScalars.map c₁ =
    integerScalars.map c₃ ≫ integerScalars.map dY
  exact (integerScalars.map_comp dX c₁).symm.trans
    ((congrArg (fun f : tateCohomology X.X₃ n ⟶ tateCohomology Y.X₁ (n + 1) =>
        integerScalars.map f) h).trans (integerScalars.map_comp c₃ dY))

/-- Reindexing at degree zero preserves the original fixed representative. -/
theorem tateReindexIso_fixedClass (e : G ≃* H) (A : Rep.{v} ℤ G) (a : A.ρ.invariants) :
    (tateReindexIso e A 0).hom (fixedClass A a) =
      fixedClass (Rep.res e.symm.toMonoidHom A) ⟨a.val, fun h => a.property (e.symm h)⟩ := by
  let B := Rep.res e.symm.toMonoidHom A
  let b : B.ρ.invariants := ⟨a.val, fun h => a.property (e.symm h)⟩
  let KA := tateComplex ((nativeFunctor G).obj A)
  let KB := tateComplex ((nativeFunctor H).obj B)
  let f := (nativeTateReindexComplexIso e A).hom
  change (KA.homologyπ 0 ≫ HomologicalComplex.homologyMap f 0) (fixedCycle A a) =
    KB.homologyπ 0 (fixedCycle B b)
  rw [HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply (ModuleCat.mono_iff_injective (KB.iCycles 0)).mp inferInstance
  change (HomologicalComplex.cyclesMap f 0 ≫ KB.iCycles 0) (fixedCycle A a) =
    KB.iCycles 0 (fixedCycle B b)
  rw [HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, fixedCycle_iCycles, fixedCycle_iCycles]
  funext h
  rfl

/-- In positive degrees the reindexing is the actual pullback along the
inverse group equivalence on the original ordinary cochains. -/
theorem tateReindexIso_hom_positive (e : G ≃* H) (A : Rep.{v} ℤ G) (n : ℕ) [NeZero n] :
    (tateReindexIso e A n).hom =
      tatePositiveMapAlong e.symm.toMonoidHom (𝟙 (Rep.res e.symm.toMonoidHom A)) n := by
  let B := Rep.res e.symm.toMonoidHom A
  let A' := (nativeFunctor G).obj A
  let B' := (nativeFunctor H).obj B
  let f := groupCohomology.cochainsMap (nativeGroupHom.{u, v} e.symm.toMonoidHom)
    (nativeCohomologyCoefficientMap e.symm.toMonoidHom (𝟙 B))
  let K := tateComplexConnectData A'
  let L := tateComplexConnectData B'
  let e' := nativeGroupEquiv.{u, v} e
  let l : A'.V ≃ₗ[ULift.{max u v} ℤ] B'.V := LinearEquiv.refl _ _
  have hl : ∀ g, l.toLinearMap ∘ₗ A'.ρ g = B'.ρ (e' g) ∘ₗ l.toLinearMap :=
    nativeTateReindex_refl_comm e A
  let k := (groupHomology.groupEquivComplexIso e' l hl).hom
  have hf : (groupCohomology.groupEquivComplexIso e' l hl).hom = f := by
    apply HomologicalComplex.hom_ext
    intro i
    apply ConcreteCategory.hom_ext
    intro x
    rfl
  have hsplice : k.f 0 ≫ L.d₀ = K.d₀ ≫ f.f 0 := by
    rw [← hf]
    exact TateCohomology.groupEquiv_tateNorm e' l hl
  have hmap : (nativeTateReindexComplexIso e A).hom = K.map L k f hsplice := by
    apply HomologicalComplex.hom_ext
    intro i
    cases i with
    | ofNat i => exact congrArg (fun t => t.f i) hf
    | negSucc i => rfl
  change IntegralGroupCohomology.integerScalars.map
      (HomologicalComplex.homologyMap (nativeTateReindexComplexIso e A).hom n) = _
  rw [hmap, CochainComplex.ConnectData.homologyMap_map_of_eq_succ K L k f hsplice n n rfl]
  let a := (K.homologyIsoPos n (n : ℤ) rfl).hom
  let b := HomologicalComplex.homologyMap f n
  let c := (L.homologyIsoPos n (n : ℤ) rfl).inv
  change integerScalars.map (a ≫ b ≫ c) =
    integerScalars.map a ≫ integerScalars.map b ≫ integerScalars.map c
  exact (integerScalars.map_comp a (b ≫ c)).trans
    (congrArg (fun m => integerScalars.map a ≫ m) (integerScalars.map_comp b c))

/-- The group isomorphism from a subgroup to its conjugate. -/
def subgroupConjugationEquiv (S : Subgroup G) (g : G) : S ≃* S.map (MulAut.conj g).toMonoidHom :=
  S.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

/-- The original ambient coefficient action intertwines a subgroup and its conjugate. -/
def conjugateCoefficientIso (S : Subgroup G) (g : G) (A : Rep.{v} ℤ G) :
    Rep.res (subgroupConjugationEquiv S g).symm.toMonoidHom (Rep.res S.subtype A) ≅
      Rep.res (S.map (MulAut.conj g).toMonoidHom).subtype A := by
  let e := subgroupConjugationEquiv S g
  let l : A.V ≃ₗ[ℤ] A.V :=
    { toLinearMap := A.ρ g
      invFun := A.ρ g⁻¹
      left_inv := fun x => by
        have h := congrArg (fun f : Module.End ℤ A => f x) (map_mul A.ρ g⁻¹ g)
        rw [inv_mul_cancel, map_one] at h
        exact h.symm
      right_inv := fun x => by
        have h := congrArg (fun f : Module.End ℤ A => f x) (map_mul A.ρ g g⁻¹)
        rw [mul_inv_cancel, map_one] at h
        exact h.symm }
  refine Rep.mkIso (Representation.Equiv.mk l ?_)
  intro k
  apply LinearMap.ext
  intro x
  change A.ρ g (A.ρ ((e.symm k : S) : G) x) = A.ρ (k : G) (A.ρ g x)
  have hk : (k : G) = g * ((e.symm k : S) : G) * g⁻¹ :=
    (congrArg Subtype.val (e.apply_symm_apply k)).symm
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hk,
    mul_assoc (g * _), inv_mul_cancel, mul_one]

/-- Conjugation on the original integral Tate groups uses the actual ambient
coefficient action and the original subgroup conjugation map. -/
def tateConjugation (S : Subgroup G) (g : G) [Fintype S]
    [Fintype (S.map (MulAut.conj g).toMonoidHom)] (A : Rep.{v} ℤ G) (n : ℤ) :
    tate (Rep.res S.subtype A) n ≅
      tate (Rep.res (S.map (MulAut.conj g).toMonoidHom).subtype A) n :=
  tateReindexIso (subgroupConjugationEquiv S g) (Rep.res S.subtype A) n ≪≫
    (tateFunctor (S.map (MulAut.conj g).toMonoidHom) n).mapIso (conjugateCoefficientIso S g A)

omit [Fintype G] [Fintype H] in
/-- The degree-zero conjugation formula acts by the original group action
on the original fixed vector. -/
theorem tateConjugation_fixedClass (S : Subgroup G) (g : G) [Fintype S]
    [Fintype (S.map (MulAut.conj g).toMonoidHom)] (A : Rep.{v} ℤ G)
    (a : (Rep.res S.subtype A).ρ.invariants) :
    (tateConjugation S g A 0).hom (fixedClass (Rep.res S.subtype A) a) =
      fixedClass (Rep.res (S.map (MulAut.conj g).toMonoidHom).subtype A)
        ⟨A.ρ g a.val, fun h => by
          have hm := Rep.hom_comm_apply (conjugateCoefficientIso S g A).hom (a := a.val) h
          change A.ρ g (A.ρ ((subgroupConjugationEquiv S g).symm h : S) a.val) =
            A.ρ (h : G) (A.ρ g a.val) at hm
          have ha : A.ρ ((subgroupConjugationEquiv S g).symm h : S) a.val = a.val :=
            a.property ((subgroupConjugationEquiv S g).symm h)
          rw [ha] at hm
          exact hm.symm⟩ := by
  simp only [tateConjugation, Iso.trans_hom, Functor.mapIso_hom, ModuleCat.comp_apply,
    tateReindexIso_fixedClass, fixedClass_map]
  rfl

end IntegralGroupCohomology.Universe
