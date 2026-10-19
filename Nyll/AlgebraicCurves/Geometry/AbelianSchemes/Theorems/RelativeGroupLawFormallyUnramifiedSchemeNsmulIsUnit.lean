/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Kernel
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFormallyUnramifiedSchemeNsmulSqZero

/-!
# Relative Group Law formally Unramified scheme Nsmul of is Unit of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open scoped TensorProduct

universe u

noncomputable section

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem schemeHomOverComp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t f) :
    schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id x.1)

theorem nsmul_coe_eq_comp_schemeNsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [schemeHomOverComp_idPoint] at h
  exact (congrArg Subtype.val h).symm

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.one_coe_eq_comp_one (G :
  RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h : schemeHomOverComp t (Category.comp_id t) (G.one (𝟙 _)) = G.one t :=
    G.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

open _root_.GoodReductionJacobian.RelativeGroupLaw
theorem pointGroup_pow_eq_nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (letI := G.pointGroup t; x ^ n) = G.nsmul t n x := by
  let := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, G.nsmul_succ]; rfl

/-- Every positive multiplication map has trivial kernel on points reducing to the identity
across a square-zero ring quotient. -/
abbrev SquareZeroKernelTorsionFree (G : RelativeGroupLaw R f) : Prop :=
  ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
    RingHom.ker φ.hom ^ 2 = ⊥ →
    ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
      schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
      ∀ n : ℕ, 0 < n → G.nsmul t n k = G.one t → k = G.one t

/-- The fixed multiplication map has trivial kernel on points reducing to the identity across a
square-zero ring quotient. -/
abbrev SquareZeroKernelNTorsionFree (G : RelativeGroupLaw R f) (n : ℕ) : Prop :=
  ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
    RingHom.ker φ.hom ^ 2 = ⊥ →
    ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
      schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
      G.nsmul t n k = G.one t → k = G.one t

end RelativeGroupLaw
end GoodReductionJacobian

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

private def _root_.GoodReductionJacobian.RelativeGroupLaw.squareZeroUnitSection
    (G : RelativeGroupLaw R f) : Spec (CommRingCat.of R) ⟶ A :=
  (G.one (𝟙 (Spec (CommRingCat.of R)))).1

open _root_.GoodReductionJacobian.RelativeGroupLaw

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.squareZeroUnitSection_comp (G :
  RelativeGroupLaw R f) :
    G.squareZeroUnitSection ≫ f = 𝟙 (Spec (CommRingCat.of R)) :=
  (G.one (𝟙 (Spec (CommRingCat.of R)))).2

open _root_.GoodReductionJacobian.RelativeGroupLaw

theorem specMap_surjective_of_surjective_of_squareZero_kernel
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ).base := by
  intro p
  have hkerp : RingHom.ker φ.hom ≤ p.asIdeal := fun x hx =>
    p.isPrime.mem_of_pow_mem 2 (by
      have h2 : x ^ 2 ∈ RingHom.ker φ.hom ^ 2 := Ideal.pow_mem_pow hx 2
      rw [hker, Ideal.mem_bot] at h2
      exact h2 ▸ p.asIdeal.zero_mem)
  have : p.asIdeal.IsPrime := p.isPrime
  refine ⟨⟨p.asIdeal.map φ.hom, Ideal.map_isPrime_of_surjective hsurj hkerp⟩,
    PrimeSpectrum.ext ?_⟩
  change Ideal.comap φ.hom (Ideal.map φ.hom p.asIdeal) = p.asIdeal
  exact (Ideal.comap_map_of_surjective φ.hom hsurj p.asIdeal).trans (sup_eq_left.mpr hkerp)

theorem range_subset_unitSection_of_reduces_to_one (G : RelativeGroupLaw R f)
    {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hkred : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t)) :
    Set.range k.1.base ⊆ Set.range G.squareZeroUnitSection.base := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, rfl⟩ := specMap_surjective_of_surjective_of_squareZero_kernel φ hsurj hker p
  have hcoe : (Spec.map φ ≫ k.1).base q = ((Spec.map φ ≫ t) ≫ G.squareZeroUnitSection).base q := by
    have h1 : Spec.map φ ≫ k.1 = (G.one (Spec.map φ ≫ t)).1 :=
      (_root_.GoodReductionJacobian.schemeHomOverComp_coe (Spec.map φ) rfl k).symm.trans (congrArg
        Subtype.val hkred)
    rw [h1, G.one_coe_eq_comp_one]; rfl
  refine ⟨(Spec.map φ ≫ t).base q, ?_⟩
  exact hcoe.symm.trans rfl

section RingTheory

variable {B R' S' : Type*} [CommRing B] [CommRing R'] [CommRing S']
variable [Algebra R B] [Algebra R R']
variable (ε₀ : B →ₐ[R] R) (φ : R' →+* S')

/-- The algebra map obtained by following the augmentation with the algebra map to the target
ring. -/
def augmentationLift : B →ₐ[R] R' := (Algebra.ofId R R').comp (ε₀.restrictScalars R)

theorem augmentationLift_apply (x : B) :
    augmentationLift ε₀ x = algebraMap R R' (ε₀ x) := by
  rfl

theorem map_mem_kernel_of_mem_augmentationIdeal (kR : B →ₐ[R] R')
    (hk : ∀ x, φ (kR x) = φ (augmentationLift ε₀ x))
    {a : B} (ha : a ∈ RingHom.ker ε₀) : kR a ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, hk a, augmentationLift_apply]
  rw [RingHom.mem_ker] at ha
  rw [ha, map_zero, map_zero]

theorem map_eq_zero_of_mem_augmentationIdeal_sq (hkerφ : RingHom.ker φ ^ 2 = ⊥)
    (kR : B →ₐ[R] R') (hk : ∀ x, φ (kR x) = φ (augmentationLift ε₀ x))
    {a : B} (ha : a ∈ (RingHom.ker ε₀) ^ 2) : kR a = 0 := by
  rw [pow_two] at ha
  refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · have : kR x * kR y ∈ RingHom.ker φ ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (map_mem_kernel_of_mem_augmentationIdeal ε₀ φ kR hk hx)
        (map_mem_kernel_of_mem_augmentationIdeal ε₀ φ kR hk hy)
    rw [hkerφ, Ideal.mem_bot] at this
    rwa [map_mul]
  · rw [map_add, hx, hy, add_zero]

theorem sub_algebraMap_augmentation_mem_kernel (x : B) :
    x - algebraMap R B (ε₀ x) ∈ RingHom.ker ε₀ := by
  simp [RingHom.mem_ker, map_sub, AlgHom.commutes]

theorem eq_augmentationLift_of_vanishes_on_augmentationIdeal (kR : B →ₐ[R] R')
    (h0 : ∀ a ∈ RingHom.ker ε₀, kR a = 0) : kR = augmentationLift ε₀ := by
  ext x
  have key : kR (x - algebraMap R B (ε₀ x)) = 0 :=
    h0 _ (sub_algebraMap_augmentation_mem_kernel ε₀ x)
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at key
  rw [key, augmentationLift_apply]

end RingTheory

open CategoryTheory.Limits

/-- The structure morphism of the self fiber product used to evaluate the relative group
multiplication. -/
abbrev squareZeroProductStructure : Limits.pullback f f ⟶ Spec (CommRingCat.of R) :=
  Limits.pullback.fst f f ≫ f

/-- The first fiber-product projection viewed as a point over its structure morphism. -/
abbrev squareZeroProductFirstPoint : SchemeHomOver (squareZeroProductStructure (f := f)) f :=
  ⟨Limits.pullback.fst f f, rfl⟩

/-- The second fiber-product projection viewed as a point over its structure morphism. -/
abbrev squareZeroProductSecondPoint : SchemeHomOver (squareZeroProductStructure (f := f)) f :=
  ⟨Limits.pullback.snd f f, Limits.pullback.condition.symm⟩

private def _root_.GoodReductionJacobian.RelativeGroupLaw.squareZeroSchemeMul
    (G : RelativeGroupLaw R f) : Limits.pullback f f ⟶ A :=
  (G.mul squareZeroProductStructure squareZeroProductFirstPoint squareZeroProductSecondPoint).1

open _root_.GoodReductionJacobian.RelativeGroupLaw

theorem squareZeroSchemeMul_over (G : RelativeGroupLaw R f) :
    G.squareZeroSchemeMul ≫ f = squareZeroProductStructure (f := f) :=
  (G.mul squareZeroProductStructure squareZeroProductFirstPoint squareZeroProductSecondPoint).2

theorem mul_coe_eq_pullbackLift_comp_squareZeroSchemeMul (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver t f) :
    (G.mul t x y).1 =
      Limits.pullback.lift x.1 y.1 (x.2.trans y.2.symm) ≫ G.squareZeroSchemeMul := by
  let ψ := Limits.pullback.lift x.1 y.1 (x.2.trans y.2.symm)
  have hψ : ψ ≫ squareZeroProductStructure (f := f) = t := by
    simp only [squareZeroProductStructure, ψ, ← Category.assoc, Limits.pullback.lift_fst]; exact x.2
  have h := G.mul_natural squareZeroProductStructure t ψ hψ
    squareZeroProductFirstPoint squareZeroProductSecondPoint
  have hfst : schemeHomOverComp ψ hψ squareZeroProductFirstPoint = x :=
    Subtype.ext (by
      rw [_root_.GoodReductionJacobian.schemeHomOverComp_coe]
      exact Limits.pullback.lift_fst _ _ _)
  have hsnd : schemeHomOverComp ψ hψ squareZeroProductSecondPoint = y :=
    Subtype.ext (by
      rw [_root_.GoodReductionJacobian.schemeHomOverComp_coe]
      exact Limits.pullback.lift_snd _ _ _)
  rw [hfst, hsnd] at h
  exact (congrArg Subtype.val h).symm

theorem squareZeroSchemeMul_unitPair (G : RelativeGroupLaw R f) :
    Limits.pullback.lift G.squareZeroUnitSection G.squareZeroUnitSection rfl ≫ G.squareZeroSchemeMul
      = G.squareZeroUnitSection := by
  have h := mul_coe_eq_pullbackLift_comp_squareZeroSchemeMul G
    (G.one (𝟙 _)) (G.one (𝟙 _))
  rw [G.one_mul] at h
  exact h.symm

end RelativeGroupLaw

end GoodReductionJacobian

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

section FourTerm

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]

/-- The algebra map on the tensor product extending the two given algebra maps. -/
abbrev augmentationTensorPair (p q : B →ₐ[R] C) : (B ⊗[R] B) →ₐ[R] C :=
  Algebra.TensorProduct.lift p q (fun _ _ => Commute.all _ _)

theorem augmentationTensorPair_four_term_eq_zero (ε₀ : B →ₐ[R] R) {J : Ideal C} (hJ2 : J ^ 2 = ⊥)
    (p q : B →ₐ[R] C) (hp : ∀ a ∈ RingHom.ker ε₀, p a ∈ J)
    (hq : ∀ a ∈ RingHom.ker ε₀, q a ∈ J) (z : B ⊗[R] B) :
    augmentationTensorPair p q z - augmentationTensorPair p (augmentationLift ε₀) z
      - augmentationTensorPair (augmentationLift ε₀) q z
      + augmentationTensorPair (augmentationLift ε₀) (augmentationLift ε₀) z = 0 := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add]; linear_combination hx + hy
  | tmul b c =>
    simp only [augmentationTensorPair, Algebra.TensorProduct.lift_tmul]
    have key : (p b - augmentationLift ε₀ b) * (q c - augmentationLift ε₀ c) = 0 := by
      have hmem : (p b - augmentationLift ε₀ b) * (q c - augmentationLift ε₀ c) ∈ J ^ 2 := by
        rw [pow_two]
        refine Ideal.mul_mem_mul ?_ ?_
        · rw [augmentationLift_apply]
          have := hp _ (sub_algebraMap_augmentation_mem_kernel ε₀ b)
          rwa [map_sub, AlgHom.commutes] at this
        · rw [augmentationLift_apply]
          have := hq _ (sub_algebraMap_augmentation_mem_kernel ε₀ c)
          rwa [map_sub, AlgHom.commutes] at this
      rwa [hJ2, Ideal.mem_bot] at hmem
    linear_combination key

theorem augmentationTensorPair_reduces_to_augmentationLift
    (ε₀ : B →ₐ[R] R) {S' : Type*} [CommRing S']
    (φ : C →+* S') (p q : B →ₐ[R] C)
    (hp : ∀ b, φ (p b) = φ (augmentationLift ε₀ b)) (hq : ∀ b, φ (q b) = φ (augmentationLift ε₀ b))
    (z : B ⊗[R] B) :
    φ (augmentationTensorPair p q z)
      = φ (augmentationLift (augmentationTensorPair ε₀ ε₀) z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    simp only [augmentationTensorPair, Algebra.TensorProduct.lift_tmul, augmentationLift_apply,
      map_mul, hp b, hq c, map_mul]

end FourTerm

section AffineBridge

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιe : Set.range G.squareZeroUnitSection.base ⊆ Set.range ι.base)

variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))

/-- A relative point belongs to the reduction kernel when its reduction is the identity point. -/
def ReducesToIdentity (k : SchemeHomOver t f) : Prop :=
  schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t)

theorem reducesToIdentity_one : ReducesToIdentity G φ t (G.one t) :=
  G.one_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl

theorem reducesToIdentity_mul {x y : SchemeHomOver t f}
    (hx : ReducesToIdentity G φ t x) (hy : ReducesToIdentity G φ t y) :
    ReducesToIdentity G φ t (G.mul t x y) := by
  unfold ReducesToIdentity at hx hy ⊢
  rw [G.mul_natural t (Spec.map φ ≫ t) (Spec.map φ) rfl x y, hx, hy, G.one_mul]

theorem reducesToIdentity_nsmul {k : SchemeHomOver t f} (hk : ReducesToIdentity G φ t k)
    (m : ℕ) : ReducesToIdentity G φ t (G.nsmul t m k) := by
  induction m with
  | zero => exact reducesToIdentity_one G φ t
  | succ m ih => rw [G.nsmul_succ]; exact reducesToIdentity_mul G φ t ih hk

/-- The ring map representing a reduction-kernel point in the chosen affine open chart. -/
def identityReductionRingHom (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k) : B₁ ⟶ R' :=
  Spec.preimage (IsOpenImmersion.lift ι k.1
    ((range_subset_unitSection_of_reduces_to_one G φ hsurj hker t k hk).trans hιe))

theorem specMap_identityReductionRingHom (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k) :
    Spec.map (identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk) ≫ ι = k.1 := by
  rw [identityReductionRingHom, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

theorem eq_of_identityReductionRingHom_eq {k k' : SchemeHomOver t f}
    (hk : ReducesToIdentity G φ t k) (hk' : ReducesToIdentity G φ t k')
    (h : identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk
      = identityReductionRingHom G B₁ ι hιe φ hsurj hker t k' hk') : k = k' :=
  Subtype.ext <| by
    rw [← specMap_identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk,
      ← specMap_identityReductionRingHom G B₁ ι hιe φ hsurj hker t k' hk', h]

theorem identityReductionRingHom_reduces (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k) :
    ∀ b, φ.hom ((identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk).hom b)
      = φ.hom ((identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.one t)
          (reducesToIdentity_one G φ t)).hom b) := by
  intro b
  have heq : Spec.map φ ≫ Spec.map (identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk)
      = Spec.map φ ≫ Spec.map (identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.one t)
          (reducesToIdentity_one G φ t)) := by
    rw [← cancel_mono ι, Category.assoc, Category.assoc,
      specMap_identityReductionRingHom, specMap_identityReductionRingHom,
      ← _root_.GoodReductionJacobian.schemeHomOverComp_coe (Spec.map φ) rfl k, hk,
      ← _root_.GoodReductionJacobian.schemeHomOverComp_coe (Spec.map φ) rfl (G.one t),
        reducesToIdentity_one]
  simp only [← Spec.map_comp] at heq
  have := Spec.map_injective heq
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) b

end AffineBridge

section TensorArgument

open Algebra.TensorProduct

variable (G : RelativeGroupLaw R f)
variable (B₁ : CommRingCat.{u}) [Algebra R B₁]
variable (ι : Spec B₁ ⟶ A) [IsOpenImmersion ι]
variable (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
variable (hιe : Set.range G.squareZeroUnitSection.base ⊆ Set.range ι.base)

include hιf

theorem preimage_openImmersionLift_algebraMap {T : CommRingCat.{u}}
    (g : Spec T ⟶ A) (hrange : Set.range g.base ⊆ Set.range ι.base)
    (algT : CommRingCat.of R ⟶ T) (hg : g ≫ f = Spec.map algT) (r : R) :
    (Spec.preimage (IsOpenImmersion.lift ι g hrange)).hom (algebraMap R B₁ r)
      = algT.hom r := by
  have h2 : IsOpenImmersion.lift ι g hrange
      ≫ Spec.map (CommRingCat.ofHom (algebraMap R B₁)) = Spec.map algT := by
    rw [← hιf, ← Category.assoc, IsOpenImmersion.lift_fac, hg]
  have h3 := Spec.preimage_comp (IsOpenImmersion.lift ι g hrange)
    (Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
  rw [h2, Spec.preimage_map, Spec.preimage_map] at h3
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h3.symm) r

/-- The augmentation of the affine chart obtained by evaluating at the relative identity section. -/
def affineUnitAugmentation : (B₁ : Type u) →ₐ[R] R :=
  { (Spec.preimage (IsOpenImmersion.lift ι G.squareZeroUnitSection hιe)).hom with
    commutes' := fun r => preimage_openImmersionLift_algebraMap B₁ ι hιf
      G.squareZeroUnitSection hιe (𝟙 (CommRingCat.of R)) (G.squareZeroUnitSection_comp.trans
        (Spec.map_id _).symm) r }

theorem specMap_affineUnitAugmentation :
    Spec.map (CommRingCat.ofHom (affineUnitAugmentation G B₁ ι hιf hιe).toRingHom) ≫ ι
      = G.squareZeroUnitSection := by
  have : (CommRingCat.ofHom (affineUnitAugmentation G B₁ ι hιf hιe).toRingHom)
      = Spec.preimage (IsOpenImmersion.lift ι G.squareZeroUnitSection hιe) := by
    apply CommRingCat.hom_ext; rfl
  rw [this, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

omit hιf in
/-- The structure morphism of the spectrum of the tensor product of the affine chart rings. -/
def augmentationTensorStructure : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁))
    ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R ((B₁ : Type u) ⊗[R] B₁)))

/-- An algebra map from the chart ring defines a relative point over the tensor-product spectrum. -/
def augmentationTensorPoint (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) :
    SchemeHomOver (augmentationTensorStructure (R := R) B₁) f :=
  ⟨Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ ι, by
    rw [Category.assoc, hιf, ← Spec.map_comp]; congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    change ρ.toRingHom (algebraMap R B₁ r) = algebraMap R ((B₁ : Type u) ⊗[R] B₁) r
    exact ρ.commutes r⟩

/-- The product of the two universal affine-chart points over the tensor-product spectrum. -/
def augmentationTensorMul : Spec (CommRingCat.of ((B₁ : Type u) ⊗[R] B₁)) ⟶ A :=
  (G.mul (augmentationTensorStructure (R := R) B₁)
    (augmentationTensorPoint B₁ ι hιf includeLeft)
    (augmentationTensorPoint B₁ ι hιf includeRight)).1

/-- The tensor-product augmentation extending the affine-chart augmentation in both factors. -/
abbrev tensorAugmentation : ((B₁ : Type u) ⊗[R] B₁) →ₐ[R] R :=
  augmentationTensorPair (affineUnitAugmentation G B₁ ι hιf hιe)
    (affineUnitAugmentation G B₁ ι hιf hιe)

theorem tensorAugmentation_surjective :
    Function.Surjective (tensorAugmentation G B₁ ι hιf hιe) := fun r =>
  ⟨algebraMap R _ r, (tensorAugmentation G B₁ ι hιf hιe).commutes r⟩

theorem augmentationTensorMul_augmentation :
    Spec.map (CommRingCat.ofHom (tensorAugmentation G B₁ ι hιf hιe).toRingHom)
      ≫ augmentationTensorMul G B₁ ι hιf = G.squareZeroUnitSection := by
  set εε := tensorAugmentation G B₁ ι hιf hιe
  have hτ0 : Spec.map (CommRingCat.ofHom εε.toRingHom) ≫ augmentationTensorStructure (R := R) B₁
      = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [augmentationTensorStructure, ← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext εε.commutes))
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)),
      εε.comp ρ = affineUnitAugmentation G B₁ ι hιf hιe →
      schemeHomOverComp (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0
        (augmentationTensorPoint B₁ ι hιf ρ) = G.one (𝟙 _) := fun ρ hρ => Subtype.ext <| by
    simp only [_root_.GoodReductionJacobian.schemeHomOverComp_coe, augmentationTensorPoint,
      ← Category.assoc,
      ← Spec.map_comp]
    rw [show (G.one (𝟙 _)).1 = G.squareZeroUnitSection from rfl,
      ← specMap_affineUnitAugmentation G B₁ ι hιf hιe]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom hρ) b :))
  have h := G.mul_natural (augmentationTensorStructure (R := R) B₁) (𝟙 _)
    (Spec.map (CommRingCat.ofHom εε.toRingHom)) hτ0
    (augmentationTensorPoint B₁ ι hιf includeLeft) (augmentationTensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight (Algebra.TensorProduct.lift_comp_includeRight' _ _ _), G.one_mul] at h
  exact congrArg Subtype.val h

theorem range_squareZeroTensorMul_subset_chart :
    Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (RingHom.ker (tensorAugmentation G B₁ ι hιf hιe).toRingHom ^ 2)))
      ≫ augmentationTensorMul G B₁ ι hιf).base ⊆ Set.range ι.base := by
  set εε := tensorAugmentation G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  rintro _ ⟨p, rfl⟩
  set P := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (𝔐 ^ 2)))).base p with hPdef
  have h𝔐P : 𝔐 ≤ P.asIdeal := by
    intro x hx
    refine P.isPrime.mem_of_pow_mem 2 ?_
    have hx2 : Ideal.Quotient.mk (𝔐 ^ 2) (x ^ 2) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hx 2)
    change Ideal.Quotient.mk (𝔐 ^ 2) (x ^ 2) ∈ p.asIdeal
    rw [hx2]; exact p.asIdeal.zero_mem
  have : P.asIdeal.IsPrime := P.isPrime
  let q : PrimeSpectrum R := ⟨P.asIdeal.map εε.toRingHom,
    Ideal.map_isPrime_of_surjective (tensorAugmentation_surjective G B₁ ι hιf hιe) h𝔐P⟩
  have hqP : (Spec.map (CommRingCat.ofHom εε.toRingHom)).base q = P := PrimeSpectrum.ext <| by
    change Ideal.comap εε.toRingHom (P.asIdeal.map εε.toRingHom) = P.asIdeal
    exact (Ideal.comap_map_of_surjective _
      (tensorAugmentation_surjective G B₁ ι hιf hιe) P.asIdeal).trans (sup_eq_left.mpr h𝔐P)
  refine hιe ⟨q, ?_⟩
  change G.squareZeroUnitSection.base q = (augmentationTensorMul G B₁ ι hιf).base P
  rw [← hqP, ← augmentationTensorMul_augmentation G B₁ ι hιf hιe]
  rfl

/-- The chart ring map for universal multiplication after quotienting by the square of the
tensor-product augmentation ideal. -/
def squareZeroComultiplication : B₁ ⟶ CommRingCat.of
    (((B₁ : Type u) ⊗[R] B₁) ⧸ RingHom.ker (tensorAugmentation G B₁ ι hιf hιe).toRingHom ^ 2) :=
  Spec.preimage (IsOpenImmersion.lift ι _ (range_squareZeroTensorMul_subset_chart G B₁ ι hιf hιe))

theorem specMap_squareZeroComultiplication :
    Spec.map (squareZeroComultiplication G B₁ ι hιf hιe) ≫ ι
      = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (RingHom.ker (tensorAugmentation G B₁ ι hιf hιe).toRingHom ^ 2)))
        ≫ augmentationTensorMul G B₁ ι hιf := by
  rw [squareZeroComultiplication, Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _

variable {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
variable (hsurj : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
variable (t : Spec R' ⟶ Spec (CommRingCat.of R))

variable [Algebra R R'] (htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom)

include hιe htR' in
/-- The chart ring map of a reduction-kernel point, viewed as an algebra map using the base
compatibility equation. -/
def identityReductionAlgHom (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k) :
    (B₁ : Type u) →ₐ[R] R' :=
  { (identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk).hom with
    commutes' := fun r => (preimage_openImmersionLift_algebraMap B₁ ι hιf k.1 _
      (Spec.preimage t) (k.2.trans (Spec.map_preimage t).symm) r).trans
      (DFunLike.congr_fun htR'.symm r) }

include htR' in
theorem identityReductionAlgHom_apply (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k)
    (b : B₁) :
    identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = (identityReductionRingHom G B₁ ι hιe φ hsurj hker t k hk).hom b := by
  have _ := hιf; have _ := htR'; rfl

include htR' in
theorem identityReductionAlgHom_one :
    identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
        (reducesToIdentity_one G φ t) =
      augmentationLift (affineUnitAugmentation G B₁ ι hιf hιe) := by
  apply AlgHom.ext; intro b
  rw [identityReductionAlgHom_apply, augmentationLift_apply]
  have heq : Spec.map (identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.one t)
      (reducesToIdentity_one G φ t))
      = t ≫ Spec.map (CommRingCat.ofHom (affineUnitAugmentation G B₁ ι hιf hιe).toRingHom) := by
    rw [← cancel_mono ι, specMap_identityReductionRingHom, Category.assoc,
      specMap_affineUnitAugmentation,
      G.one_coe_eq_comp_one]; rfl
  have hmap : identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.one t)
      (reducesToIdentity_one G φ t)
      = CommRingCat.ofHom (affineUnitAugmentation G B₁ ι hιf hιe).toRingHom ≫ Spec.preimage t :=
    Spec.map_injective (heq.trans (by rw [Spec.map_comp, Spec.map_preimage]))
  refine (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap) b).trans ?_
  exact DFunLike.congr_fun htR'.symm _

include htR' in
theorem mul_eq_tensorPair_comp_augmentationTensorMul
    (x y : SchemeHomOver t f) (hx : ReducesToIdentity G φ t x) (hy : ReducesToIdentity G φ t y) :
    (G.mul t x y).1
      = Spec.map (CommRingCat.ofHom (augmentationTensorPair
          (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
          (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' y hy)).toRingHom)
        ≫ augmentationTensorMul G B₁ ι hιf := by
  set ψ := augmentationTensorPair (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' x hx)
    (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' y hy)
  have hτ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
      augmentationTensorStructure (R := R) B₁ = t := by
    rw [augmentationTensorStructure, ← Spec.map_comp, ← Spec.map_preimage t]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    exact (ψ.commutes r).trans (DFunLike.congr_fun htR' r)
  have hξ : ∀ (ρ : (B₁ : Type u) →ₐ[R] ((B₁ : Type u) ⊗[R] B₁)) (z : SchemeHomOver t f)
      (hz : ReducesToIdentity G φ t z),
      ψ.comp ρ = identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' z hz →
      schemeHomOverComp (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ
        (augmentationTensorPoint B₁ ι hιf ρ) = z := fun ρ z hz hρ => by
    apply Subtype.ext
    simp only [_root_.GoodReductionJacobian.schemeHomOverComp_coe, augmentationTensorPoint,
      ← Category.assoc,
      ← Spec.map_comp]
    rw [← specMap_identityReductionRingHom G B₁ ι hιe φ hsurj hker t z hz]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun b =>
      (DFunLike.congr_fun hρ b).trans rfl)
  have h := G.mul_natural (augmentationTensorStructure (R := R) B₁) t
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hτ
    (augmentationTensorPoint B₁ ι hιf includeLeft) (augmentationTensorPoint B₁ ι hιf includeRight)
  rw [hξ includeLeft x hx (Algebra.TensorProduct.lift_comp_includeLeft _ _ _),
    hξ includeRight y hy (Algebra.TensorProduct.lift_comp_includeRight' _ _ _)] at h
  exact (congrArg Subtype.val h).symm

include htR' in
theorem identityReductionAlgHom_congr {k k' : SchemeHomOver t f}
    (hk : ReducesToIdentity G φ t k) (hk' : ReducesToIdentity G φ t k') (h : k = k') (b : B₁) :
    identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k' hk' b := by
  subst h; rfl

include htR' in
theorem identityReductionAlgHom_reduces (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k)
    (b : B₁) :
    φ.hom (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k hk b)
      = φ.hom (augmentationLift (affineUnitAugmentation G B₁ ι hιf hιe) b) := by
  rw [identityReductionAlgHom_apply,
    identityReductionRingHom_reduces G B₁ ι hιe φ hsurj hker t k hk,
    ← identityReductionAlgHom_apply G B₁ ι hιf hιe φ hsurj hker t htR',
    identityReductionAlgHom_one]

include htR' in
theorem identityReductionAlgHom_mul_four_term (x y : SchemeHomOver t f)
    (hx : ReducesToIdentity G φ t x) (hy : ReducesToIdentity G φ t y) (b : B₁) :
    identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t x y)
        (reducesToIdentity_mul G φ t hx hy) b
      - identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' x hx b
      - identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' y hy b
      + identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (reducesToIdentity_one G φ t) b = 0 := by
  set ε₀ := affineUnitAugmentation G B₁ ι hιf hιe
  set εε := tensorAugmentation G B₁ ι hιf hιe
  set 𝔐 := RingHom.ker εε.toRingHom
  have he := reducesToIdentity_one G φ t
  have hψ2 : ∀ (p q : SchemeHomOver t f) (hp : ReducesToIdentity G φ t p)
      (hq : ReducesToIdentity G φ t q), ∀ a ∈ 𝔐 ^ 2,
      (augmentationTensorPair (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom a = 0 :=
    fun p q hp hq a ha => map_eq_zero_of_mem_augmentationIdeal_sq εε φ.hom hker _
      (augmentationTensorPair_reduces_to_augmentationLift ε₀ φ.hom _ _
        (identityReductionAlgHom_reduces G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
        (identityReductionAlgHom_reduces G B₁ ι hιf hιe φ hsurj hker t htR' q hq)) ha
  have hfac : ∀ (p q : SchemeHomOver t f) (hp : ReducesToIdentity G φ t p)
      (hq : ReducesToIdentity G φ t q),
      identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.mul t p q)
          (reducesToIdentity_mul G φ t hp hq)
        = squareZeroComultiplication G B₁ ι hιf hιe ≫ CommRingCat.ofHom (Ideal.Quotient.lift (𝔐 ^ 2)
            (augmentationTensorPair
              (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
              (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' q hq)).toRingHom
            (hψ2 p q hp hq)) := fun p q hp hq => by
    apply Spec.map_injective
    rw [← cancel_mono ι, specMap_identityReductionRingHom, Spec.map_comp, Category.assoc,
      specMap_squareZeroComultiplication, ← Category.assoc, ← Spec.map_comp,
      mul_eq_tensorPair_comp_augmentationTensorMul G B₁ ι hιf hιe φ hsurj hker t htR' p q hp hq]
    exact congrArg (· ≫ augmentationTensorMul G B₁ ι hιf) (congrArg Spec.map
      (CommRingCat.hom_ext (RingHom.ext fun a =>
        (Ideal.Quotient.lift_mk (𝔐 ^ 2) _ (hψ2 p q hp hq) (a := a)).symm)))
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((squareZeroComultiplication G B₁ ι hιf hιe).hom b)
  have h4 : ∀ (p q : SchemeHomOver t f) (hp : ReducesToIdentity G φ t p)
      (hq : ReducesToIdentity G φ t q),
      identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.mul t p q)
          (reducesToIdentity_mul G φ t hp hq) b
        = augmentationTensorPair (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' p hp)
            (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' q hq) z := by
    intro p q hp hq
    have step : (identityReductionRingHom G B₁ ι hιe φ hsurj hker t (G.mul t p q)
          (reducesToIdentity_mul G φ t hp hq)).hom b
        = Ideal.Quotient.lift (𝔐 ^ 2) _ (hψ2 p q hp hq)
            ((squareZeroComultiplication G B₁ ι hιf hιe).hom b) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hfac p q hp hq)) b
    rw [identityReductionAlgHom_apply, step, ← hz]
    exact Ideal.Quotient.lift_mk _ _ _
  rw [h4 x y hx hy,
    identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR' hx
      (reducesToIdentity_mul G φ t hx he) (G.mul_one t x).symm b,
    h4 x (G.one t) hx he,
    identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR' hy
      (reducesToIdentity_mul G φ t he hy) (G.one_mul t y).symm b,
    h4 (G.one t) y he hy,
    identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR' he
      (reducesToIdentity_mul G φ t he he) (G.one_mul t (G.one t)).symm b,
    h4 (G.one t) (G.one t) he he, identityReductionAlgHom_one]
  exact augmentationTensorPair_four_term_eq_zero ε₀ hker _ _
    (fun a ha => map_mem_kernel_of_mem_augmentationIdeal ε₀ φ.hom _
      (identityReductionAlgHom_reduces G B₁ ι hιf hιe φ hsurj hker t htR' x hx) ha)
    (fun a ha => map_mem_kernel_of_mem_augmentationIdeal ε₀ φ.hom _
      (identityReductionAlgHom_reduces G B₁ ι hιf hιe φ hsurj hker t htR' y hy) ha) z

include htR' in
theorem identityReductionAlgHom_nsmul_sub (k : SchemeHomOver t f) (hk : ReducesToIdentity G φ t k)
    (m : ℕ) (b : B₁) :
    identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.nsmul t m k)
        (reducesToIdentity_nsmul G φ t hk m) b
      - identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (reducesToIdentity_one G φ t) b
    = m • (identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      - identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (reducesToIdentity_one G φ t) b) := by
  induction m with
  | zero =>
    rw [zero_smul,
      identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR'
        (reducesToIdentity_nsmul G φ t hk 0) (reducesToIdentity_one G φ t)
        (G.nsmul_zero t k) b,
      sub_self]
  | succ m ih =>
    have h4 := identityReductionAlgHom_mul_four_term G B₁ ι hιf hιe φ hsurj hker t htR'
      (G.nsmul t m k) k (reducesToIdentity_nsmul G φ t hk m) hk b
    rw [identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR'
        (reducesToIdentity_nsmul G φ t hk (m + 1))
        (reducesToIdentity_mul G φ t (reducesToIdentity_nsmul G φ t hk m) hk)
        (G.nsmul_succ t m k) b,
      succ_nsmul, ← ih]
    linear_combination h4

end TensorArgument

end RelativeGroupLaw

end GoodReductionJacobian

section IsUnitDischarge

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian

namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem squareZeroKernelNTorsionFree_of_isUnit (G : RelativeGroupLaw R f)
    {n : ℕ} (hn : IsUnit (n : R)) :
    SquareZeroKernelNTorsionFree G n := by
  intro R' S' φ hsurj hker t k hk hnk
  let pt : (Spec (CommRingCat.of R) : Scheme.{u}) := IsLocalRing.closedPoint R
  let j := A.affineCover.idx (G.squareZeroUnitSection.base pt)
  let B₁ : CommRingCat.{u} := CommRingCat.of Γ(A.affineCover.X j, ⊤)
  have : IsAffine (A.affineCover.X j) := inferInstance
  let ι : Spec B₁ ⟶ A := (A.affineCover.X j).isoSpec.inv ≫ A.affineCover.f j
  have : IsOpenImmersion ι := inferInstance
  let : Algebra R B₁ := (Spec.preimage (ι ≫ f)).hom.toAlgebra
  have hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B₁)) :=
    (Spec.map_preimage (ι ≫ f)).symm.trans (congrArg Spec.map (CommRingCat.hom_ext rfl))
  have hιe : Set.range G.squareZeroUnitSection.base ⊆ Set.range ι.base := by
    have hpt : G.squareZeroUnitSection.base pt ∈ Set.range ι.base := by
      obtain ⟨q, hq⟩ := A.affineCover.covers (G.squareZeroUnitSection.base pt)
      exact ⟨(A.affineCover.X j).isoSpec.hom.base q, by
        change (((A.affineCover.X j).isoSpec.hom ≫ (A.affineCover.X j).isoSpec.inv)
          ≫ A.affineCover.f j).base q = _
        rw [Iso.hom_inv_id, Category.id_comp]; exact hq⟩
    have hopen : IsOpen (G.squareZeroUnitSection.base ⁻¹' Set.range ι.base) :=
      ι.isOpenEmbedding.isOpen_range.preimage G.squareZeroUnitSection.base.hom.continuous
    rintro _ ⟨p, rfl⟩
    exact (IsLocalRing.specializes_closedPoint p).mem_open hopen hpt
  let : Algebra R R' := (Spec.preimage t).hom.toAlgebra
  have htR' : (algebraMap R R' : R →+* R') = (Spec.preimage t).hom := rfl
  have hδ := identityReductionAlgHom_nsmul_sub G B₁ ι hιf hιe φ hsurj hker t htR' k hk n
  simp only [identityReductionAlgHom_congr G B₁ ι hιf hιe φ hsurj hker t htR'
    (reducesToIdentity_nsmul G φ t hk n) (reducesToIdentity_one G φ t) hnk,
    sub_self, nsmul_eq_mul] at hδ
  have hun : IsUnit (n : R') := by
    have := hn.map (algebraMap R R'); rwa [map_natCast] at this
  have hkR0 : ∀ b, identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' k hk b
      = identityReductionAlgHom G B₁ ι hιf hιe φ hsurj hker t htR' (G.one t)
          (reducesToIdentity_one G φ t) b := fun b =>
    sub_eq_zero.mp (hun.mul_left_cancel ((hδ b).symm.trans (mul_zero _).symm))
  refine eq_of_identityReductionRingHom_eq G B₁ ι hιe φ hsurj hker t hk
    (reducesToIdentity_one G φ t) (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  exact (identityReductionAlgHom_apply G B₁ ι hιf hιe φ hsurj hker t htR' k hk b).symm.trans
    ((hkR0 b).trans (identityReductionAlgHom_apply G B₁ ι hιf hιe φ hsurj hker t htR'
      (G.one t) (reducesToIdentity_one G φ t) b))

end RelativeGroupLaw

end GoodReductionJacobian

end IsUnitDischarge

end

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace RelativeGroupLaw
open _root_.GoodReductionJacobian.RelativeGroupLaw
end GoodReductionJacobian.RelativeGroupLaw
open scoped _root_.GoodReductionJacobian _root_.GoodReductionJacobian.RelativeGroupLaw in
open CategoryTheory AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian in
open GoodReductionJacobian in
theorem
  GoodReductionJacobian.RelativeGroupLaw.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) (hn : IsUnit (n : R))
    (R' S' : CommRingCat.{u}) (φ : R' ⟶ S') (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hk : schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t :=
  GoodReductionJacobian.RelativeGroupLaw.squareZeroKernelNTorsionFree_of_isUnit G hn R' S' φ
    hφ hker t k hk hnk

end RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
open GoodReductionJacobian.RelativeGroupLaw
theorem formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero G hcomm n
    (fun R' S' φ hφ hker t k hk hnk ↦
      eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit_of_isLocalRing
        G n hn R' S' φ hφ hker t k hk hnk)
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation
