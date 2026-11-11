/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedArtinTransfer
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.GeometricRestrictedRayTransitions

/-!
# Original native transfer in the geometric constant-stage system

Each actual stage inclusion embeds the upper field in the lower native
separable closure through the original common ambient field. Its native
absolute transfer and reduced ray transfer are therefore the transfers
already proved compatible with original reciprocity.

The only subsequent transport is the literal equality of iterated and
direct boundary moduli. Every original absolute-abelian representative
and every original restricted-product transition retains its exact value.
-/

@[expose] public section

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

section ModulusCongruence

variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [HasPrincipalDivisors k F]

/-- Literal equality of moduli identifies the actual native ray quotients
without changing any original absolute-abelian representative. -/
def rayAbelianModulusCongr {m n : Modulus k F} (h : m = n) :
    (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup m) ≃ₜ*
      (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup n) := by
  subst n
  exact ContinuousMulEquiv.refl _

/-- The native modulus comparison keeps the literal original representative. -/
theorem rayAbelianModulusCongr_mk {m n : Modulus k F} (h : m = n)
    (a : localAbsoluteAbelianProfinite F) :
    rayAbelianModulusCongr h (QuotientGroup.mk' (artinRaySubgroup m) a) =
      QuotientGroup.mk' (artinRaySubgroup n) a := by
  subst n
  rfl

/-- The same literal modulus transport commutes with original reciprocity. -/
theorem rayAbelianModulusCongr_artin {m n : Modulus k F} (h : m = n)
    (a : RayRestrictedProduct m) :
    rayAbelianModulusCongr h (restrictedProductAbsoluteArtin m a) =
      restrictedProductAbsoluteArtin n (rayModulusCongr h a) := by
  subst n
  rfl

end ModulusCongruence

section EmbeddedModulusTransition

variable (k F G : Type*) [Field k] [Finite k] [Field F] [Field G]
  [Algebra k F] [Algebra k G] [Algebra F G] [IsScalarTower k F G]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  [Algebra (RatFunc k) G] [IsScalarTower k (RatFunc k) G] [FunctionField k G]
  [FiniteDimensional F G] [IsGalois F G]
  [HasPrincipalDivisors k F] [HasPrincipalDivisors k G]
  (ι : G →ₐ[F] SeparableClosure F)
  (m : Modulus k F) (hm : ∀ v, m v ≤ 1)
  (n : Modulus k G) (h : rayModulusBaseChange G m = n)

/-- The embedded native transfer followed by its literal target-modulus comparison. -/
def embeddedRayTransferModulusCongr :
    (localAbsoluteAbelianProfinite F ⧸ artinRaySubgroup m) →ₜ*
      (localAbsoluteAbelianProfinite G ⧸ artinRaySubgroup n) :=
  (ContinuousMonoidHom.toContinuousMonoidHom (rayAbelianModulusCongr h)).comp
    (nativeRayTransferOfEmbedding F G ι k m hm)

/-- The two component formulas keep the original absolute transfer representative. -/
theorem embeddedRayTransferModulusCongr_mk (a : localAbsoluteAbelianProfinite F) :
    embeddedRayTransferModulusCongr k F G ι m hm n h
        (QuotientGroup.mk' (artinRaySubgroup m) a) =
      QuotientGroup.mk' (artinRaySubgroup n)
        (nativeAbsoluteTransferOfEmbedding F G ι a) :=
  (congrArg (rayAbelianModulusCongr h)
    (nativeRayTransferOfEmbedding_mk F G ι k m hm a)).trans
      (rayAbelianModulusCongr_mk h (nativeAbsoluteTransferOfEmbedding F G ι a))

/-- Reciprocity and the modulus comparison compose before choosing concrete stage fields. -/
theorem embeddedRayTransferModulusCongr_artin (a : RayRestrictedProduct m) :
    restrictedProductAbsoluteArtin n
        (rayModulusCongr h (restrictedRayBaseChange (L := G) m hm a)) =
      embeddedRayTransferModulusCongr k F G ι m hm n h
        (restrictedProductAbsoluteArtin m a) :=
  (rayAbelianModulusCongr_artin h (restrictedRayBaseChange (L := G) m hm a)).symm.trans
    (congrArg (rayAbelianModulusCongr h)
      (restrictedProductAbsoluteArtin_baseChange_transferOfEmbedding F G ι k m hm a))

end EmbeddedModulusTransition

/-- The literal inclusion of intermediate fields is compatible with their
unchanged actions on the common ambient field. -/
theorem intermediateFieldInclusion_ambientScalarTower
    {B A : Type*} [Field B] [Field A] [Algebra B A]
    (F G : IntermediateField B A) (hFG : F ≤ G) :
    let : Algebra F G := (IntermediateField.inclusion hFG).toRingHom.toAlgebra
    IsScalarTower F G A := by
  intro aFG
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance]
  stageRatFuncAlgebra stageRatFuncTower stageFunctionField stagePrincipalDivisors

variable (k K Ω : Type*) [Field k] [Finite k] [Field K] [Field Ω]
  [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] [Algebra K Ω] [IsSepClosure K Ω] [IsSepClosed Ω]
  [Algebra k Ω] [IsScalarTower k K Ω]

local notation "I" => GeometricArtinIndex k K Ω
local notation "E" => geometricArtinStageField k K Ω

/-- A stage uses the canonical algebra of its own native separable closure. -/
local instance stageNativeSeparableClosureAlgebra (i : I) :
    Algebra (E i) (SeparableClosure (E i)) :=
  (separableClosure (E i) (AlgebraicClosure (E i))).toSubalgebra.algebra

/-- The closure action is the projection of that same canonical stage algebra. -/
local instance stageNativeSeparableClosureSMul (i : I) :
    SMul (E i) (SeparableClosure (E i)) :=
  (stageNativeSeparableClosureAlgebra k K Ω i).toSMul

/-- The original ambient closure is a separable closure of each finite stage. -/
local instance stageSuppliedSepClosure (i : I) : IsSepClosure (E i) Ω :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable K (E i) Ω⟩

/-- The actual closure equivalence used by every stage transfer. -/
def geometricNativeStageClosureEquiv (i : I) : SeparableClosure (E i) ≃ₐ[E i] Ω := by
  have : IsSepClosure (E i) Ω := stageSuppliedSepClosure k K Ω i
  exact IsSepClosure.equiv (E i) (SeparableClosure (E i)) Ω

/-- The original upper-field inclusion inside the lower stage's native
separable closure, through the fixed original ambient field. -/
def geometricNativeStageEmbedding (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    (E j) →ₐ[E i] SeparableClosure (E i) := by
  intro aij
  have : IsScalarTower (E i) (E j) Ω :=
    intermediateFieldInclusion_ambientScalarTower
      (B := K) (A := Ω) (E i).toIntermediateField (E j).toIntermediateField hij
  exact (geometricNativeStageClosureEquiv k K Ω i).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom (E i) (E j) Ω)

/-- Native original absolute transfer along an actual constant-stage inclusion. -/
def geometricNativeAbsoluteTransition (i j : I) (hij : i ≤ j) :
    localAbsoluteAbelianProfinite (E i) →ₜ* localAbsoluteAbelianProfinite (E j) := by
  let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  have : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
  exact nativeAbsoluteTransferOfEmbedding (E i) (E j)
    (geometricNativeStageEmbedding k K Ω i j hij)

/-- The actual native ray transfer between two original geometric stages,
retaining the direct pullback of the original modulus. -/
def geometricNativeRayTransition (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) :
    (localAbsoluteAbelianProfinite (E i) ⧸ artinRaySubgroup (rayModulusBaseChange (E i) m)) →ₜ*
      (localAbsoluteAbelianProfinite (E j) ⧸ artinRaySubgroup (rayModulusBaseChange (E j) m)) := by
  let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
  have : IsScalarTower K (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : IsScalarTower k (E i) (E j) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  have : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
  have : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
  exact embeddedRayTransferModulusCongr k (E i) (E j)
    (geometricNativeStageEmbedding k K Ω i j hij)
    (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
    (rayModulusBaseChange (E j) m)
    (rayModulusBaseChange_trans (L := E i) (M := E j) m)

-- Check each concrete definition boundary separately before composing the laws.
omit [Algebra k Ω] [IsScalarTower k K Ω] in
private theorem geometricNativeAbsoluteTransition_apply
    (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    let : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
    ∀ a : localAbsoluteAbelianProfinite (E i),
      geometricNativeAbsoluteTransition k K Ω i j hij a =
        nativeAbsoluteTransferOfEmbedding (E i) (E j)
          (geometricNativeStageEmbedding k K Ω i j hij) a := by
  intro aij hKij hfinite hgalois a
  rfl

private theorem geometricNativeRayTransition_eq
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : IsScalarTower k (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    let : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
    geometricNativeRayTransition k K Ω m hm i j hij =
      embeddedRayTransferModulusCongr k (E i) (E j)
        (geometricNativeStageEmbedding k K Ω i j hij)
        (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
        (rayModulusBaseChange (E j) m)
        (rayModulusBaseChange_trans (L := E i) (M := E j) m) := by
  intro aij hKij hkij hfinite hgalois
  rfl

omit [IsSepClosure K Ω] in
private theorem geometricRestrictedRayTransition_apply
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : IsScalarTower k (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    ∀ a : RayRestrictedProduct (rayModulusBaseChange (E i) m),
      geometricRestrictedRayTransition k K Ω m hm i j hij a =
        rayModulusCongr (rayModulusBaseChange_trans (L := E i) (M := E j) m)
          (restrictedRayBaseChange (L := E j) (rayModulusBaseChange (E i) m)
            (rayModulusBaseChange_reduced m hm) a) := by
  intro aij hKij hkij hfinite a
  rfl

private theorem geometricNativeRayTransition_apply
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : IsScalarTower k (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    let : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
    ∀ a : localAbsoluteAbelianProfinite (E i) ⧸
        artinRaySubgroup (rayModulusBaseChange (E i) m),
      geometricNativeRayTransition k K Ω m hm i j hij a =
        (embeddedRayTransferModulusCongr k (E i) (E j)
        (geometricNativeStageEmbedding k K Ω i j hij)
        (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
        (rayModulusBaseChange (E j) m)
        (rayModulusBaseChange_trans (L := E i) (M := E j) m)) a := by
  intro aij hKij hkij hfinite hgalois a
  exact DFunLike.congr_fun (geometricNativeRayTransition_eq k K Ω m hm i j hij) a

private theorem geometricEmbeddedRayTransfer_mk
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : IsScalarTower k (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    let : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
    ∀ a : localAbsoluteAbelianProfinite (E i),
      (embeddedRayTransferModulusCongr k (E i) (E j)
        (geometricNativeStageEmbedding k K Ω i j hij)
        (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
        (rayModulusBaseChange (E j) m)
        (rayModulusBaseChange_trans (L := E i) (M := E j) m))
          (QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E i) m)) a) =
        QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E j) m))
          (nativeAbsoluteTransferOfEmbedding (E i) (E j)
            (geometricNativeStageEmbedding k K Ω i j hij) a) := by
  intro aij hKij hkij hfinite hgalois a
  exact embeddedRayTransferModulusCongr_mk k (E i) (E j)
    (geometricNativeStageEmbedding k K Ω i j hij)
    (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
    (rayModulusBaseChange (E j) m)
    (rayModulusBaseChange_trans (L := E i) (M := E j) m) a

private theorem geometricEmbeddedRayTransfer_artin
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (i j : I) (hij : i ≤ j) :
    let : Algebra (E i) (E j) := stageInclusionAlgebra k K Ω i j hij
    let : IsScalarTower K (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : IsScalarTower k (E i) (E j) :=
      IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
    let : FiniteDimensional (E i) (E j) := FiniteDimensional.right K (E i) (E j)
    let : IsGalois (E i) (E j) := IsGalois.tower_top_of_isGalois K (E i) (E j)
    ∀ a : RayRestrictedProduct (rayModulusBaseChange (E i) m),
      restrictedProductAbsoluteArtin (rayModulusBaseChange (E j) m)
          (rayModulusCongr (rayModulusBaseChange_trans (L := E i) (M := E j) m)
            (restrictedRayBaseChange (L := E j) (rayModulusBaseChange (E i) m)
              (rayModulusBaseChange_reduced m hm) a)) =
        (embeddedRayTransferModulusCongr k (E i) (E j)
        (geometricNativeStageEmbedding k K Ω i j hij)
        (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
        (rayModulusBaseChange (E j) m)
        (rayModulusBaseChange_trans (L := E i) (M := E j) m))
          (restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m) a) := by
  intro aij hKij hkij hfinite hgalois a
  exact embeddedRayTransferModulusCongr_artin k (E i) (E j)
    (geometricNativeStageEmbedding k K Ω i j hij)
    (rayModulusBaseChange (E i) m) (rayModulusBaseChange_reduced m hm)
    (rayModulusBaseChange (E j) m)
    (rayModulusBaseChange_trans (L := E i) (M := E j) m) a

/-- The actual ray transition keeps every original native absolute
transfer representative unchanged. -/
theorem geometricNativeRayTransition_mk
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) (a : localAbsoluteAbelianProfinite (E i)) :
    geometricNativeRayTransition k K Ω m hm i j hij
        (QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E i) m)) a) =
      QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E j) m))
        (geometricNativeAbsoluteTransition k K Ω i j hij a) := by
  have hRay := geometricNativeRayTransition_apply k K Ω m hm i j hij
    (QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E i) m)) a)
  have hNative := geometricEmbeddedRayTransfer_mk k K Ω m hm i j hij a
  have hAbsolute := geometricNativeAbsoluteTransition_apply k K Ω i j hij a
  exact hRay.trans (hNative.trans
    (congrArg (QuotientGroup.mk' (artinRaySubgroup (rayModulusBaseChange (E j) m)))
      hAbsolute.symm))

omit [IsSepClosure K Ω] in
/-- The original Artin map with the geometric stage's fixed field presentation. -/
noncomputable def geometricNativeArtin (m : Modulus k K) (i : I) :
    RayRestrictedProduct (rayModulusBaseChange (E i) m) →*
      (localAbsoluteAbelianProfinite (E i) ⧸ artinRaySubgroup (rayModulusBaseChange (E i) m)) :=
  restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m)

omit [IsSepClosure K Ω] in
/-- Evaluating the shared geometric Artin map retains the original Artin value. -/
theorem geometricNativeArtin_apply (m : Modulus k K) (i : I)
    (a : RayRestrictedProduct (rayModulusBaseChange (E i) m)) :
    geometricNativeArtin k K Ω m i a =
      restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m) a :=
  rfl

/-- Every actual restricted-product stage inclusion satisfies the same
original native reciprocity square. -/
theorem geometricNativeRayTransition_artin
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) (a : RayRestrictedProduct (rayModulusBaseChange (E i) m)) :
    restrictedProductAbsoluteArtin (rayModulusBaseChange (E j) m)
        (geometricRestrictedRayTransition k K Ω m hm i j hij a) =
      geometricNativeRayTransition k K Ω m hm i j hij
        (restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m) a) := by
  have hRestricted := geometricRestrictedRayTransition_apply k K Ω m hm i j hij a
  have hNative := geometricEmbeddedRayTransfer_artin k K Ω m hm i j hij a
  have hRay := geometricNativeRayTransition_apply k K Ω m hm i j hij
    (restrictedProductAbsoluteArtin (rayModulusBaseChange (E i) m) a)
  exact (congrArg (restrictedProductAbsoluteArtin (rayModulusBaseChange (E j) m))
    hRestricted).trans (hNative.trans hRay.symm)

/-- The shared original Artin maps satisfy the native transition formula. -/
theorem geometricNativeArtin_transfer
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (i j : I) (hij : i ≤ j) (a : RayRestrictedProduct (rayModulusBaseChange (E i) m)) :
    geometricNativeArtin k K Ω m j
        (geometricRestrictedRayTransition k K Ω m hm i j hij a) =
      geometricNativeRayTransition k K Ω m hm i j hij
        (geometricNativeArtin k K Ω m i a) := by
  exact (geometricNativeArtin_apply k K Ω m j
    (geometricRestrictedRayTransition k K Ω m hm i j hij a)).trans
      ((geometricNativeRayTransition_artin k K Ω m hm i j hij a).trans
        (congrArg
          (fun x : localAbsoluteAbelianProfinite (E i) ⧸
              artinRaySubgroup (rayModulusBaseChange (E i) m) =>
            geometricNativeRayTransition k K Ω m hm i j hij x)
          (geometricNativeArtin_apply k K Ω m i a).symm))

end FunctionField.RayClass
