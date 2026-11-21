/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex), The Tau Ceti contributors

The degree-shifting construction follows Tau Ceti's
`RepresentationTheory/Homological/TateCohomology/Cup/Product.lean`.
-/

module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Nyll.GaloisCohomology.Cyclic.IntegralTateAbelianization
public import Nyll.GaloisCohomology.Cyclic.IntegralTateDimensionShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateDimensionShiftNaturality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInducedShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInducedShiftNaturality
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorNorm
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorShift
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorUnit
public import Nyll.GaloisCohomology.GroupTheory.RepresentationUniverseLift

/-!
# Integral Tate cup products in all bidegrees

The cup product starts from the actual tensor map on a fixed representative
in degree zero. The induced and coinduced sequences then shift in the right
variable. The sign in each step is the sign of the left degree.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped RepTensor TensorProduct

namespace Rep

/-- Lifting the original tensor representation is equivalent to tensoring
the two lifts. The comparison sends an elementary tensor to its lift. -/
def universeLiftIntegerTensorIso {G : Type u} [Group G] (A B : Rep.{v} ℤ G) :
    (universeLiftFunctor ℤ G).obj A ⊗ᵣ (universeLiftFunctor ℤ G).obj B ≅
      (universeLiftFunctor ℤ G).obj (A ⊗ᵣ B) := by
  let F := universeLiftFunctor ℤ G
  let A' := F.obj A
  let B' := F.obj B
  let : Module ℤ (A' ⊗ᵣ B') := (A' ⊗ᵣ B').hV2
  let : Module ℤ (F.obj (A ⊗ᵣ B)) := (F.obj (A ⊗ᵣ B)).hV2
  let lower (X : Rep.{v} ℤ G) : F.obj X ≃ₗ[ℤ] X :=
    { toFun := ULift.down
      invFun := ULift.up
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e : (A' ⊗ᵣ B' : Rep.{max u v} ℤ (ULift.{v} G)) ≃ₗ[ℤ] F.obj (A ⊗ᵣ B) :=
    (TensorProduct.congr (lower A) (lower B)).trans (lower (A ⊗ᵣ B)).symm
  let iso {P Q : Rep.{max u v} ℤ (ULift.{v} G)} (b : P ≃ₗ[ℤ] Q)
      (h : ∀ σ, b.toLinearMap.comp (P.ρ σ) = (Q.ρ σ).comp b.toLinearMap) : P ≅ Q :=
    Rep.mkIso (Representation.Equiv.mk b h)
  refine iso e ?_
  intro g
  apply TensorProduct.ext'
  intro a b
  change e (TensorProduct.map (A'.ρ g) (B'.ρ g) (a ⊗ₜ[ℤ] b)) =
    (F.obj (A ⊗ᵣ B)).ρ g (e (a ⊗ₜ[ℤ] b))
  rw [TensorProduct.map_tmul]
  change ULift.up (A.ρ g.down a.down ⊗ₜ[ℤ] B.ρ g.down b.down) =
    ULift.up (TensorProduct.map (A.ρ g.down) (B.ρ g.down) (a.down ⊗ₜ[ℤ] b.down))
  exact congrArg ULift.up (TensorProduct.map_tmul (A.ρ g.down) (B.ρ g.down) a.down b.down).symm

end Rep

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- An additive map over the original integer modules is linear for their
given scalar actions. -/
def integerModuleLinearMap {A B : ModuleCat.{u} ℤ} (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' z x := (congrArg f (int_smul_eq_zsmul A.isModule z x)).trans
    ((map_zsmul f z x).trans (int_smul_eq_zsmul B.isModule z (f x)).symm)

/-- Precompose the arguments and postcompose the value of an integer
bilinear map using the original bundled modules. -/
def integerBilinearMapAlong {A A' B B' C C' : ModuleCat.{u} ℤ}
    (f : A →ₗ[ℤ] B →ₗ[ℤ] C) (a : A' →ₗ[ℤ] A) (b : B' →ₗ[ℤ] B) (c : C →ₗ[ℤ] C') :
    A' →ₗ[ℤ] B' →ₗ[ℤ] C' := by
  let p : A' →+ (B' →ₗ[ℤ] C') :=
    { toFun := fun x => c.comp ((f (a x)).comp b)
      map_zero' := by
        apply LinearMap.ext
        intro y
        change c (f (a 0) (b y)) = 0
        simp only [map_zero, LinearMap.zero_apply]
      map_add' := fun x x' => by
        apply LinearMap.ext
        intro y
        change c (f (a (x + x')) (b y)) = c (f (a x) (b y)) + c (f (a x') (b y))
        simp only [map_add, LinearMap.add_apply] }
  exact
    { toFun := p
      map_add' := p.map_add
      map_smul' := fun z x =>
        (congrArg p (int_smul_eq_zsmul A'.isModule z x)).trans (map_zsmul p z x) }

theorem integerBilinearMapAlong_apply {A A' B B' C C' : ModuleCat.{u} ℤ}
    (f : A →ₗ[ℤ] B →ₗ[ℤ] C) (a : A' →ₗ[ℤ] A) (b : B' →ₗ[ℤ] B) (c : C →ₗ[ℤ] C')
    (x : A') (y : B') : integerBilinearMapAlong f a b c x y = c (f (a x) (b y)) := rfl

/-- The linear transport between two equal Tate degrees of the same coefficient. -/
def tateDegreeEquiv (A : Rep.{u} ℤ G) {i j : ℤ} (h : i = j) :
    tate A i ≃ₗ[ℤ] tate A j :=
  (eqToIso (congrArg (tate A) h)).toLinearEquiv

/-- A representation map commutes with a transport of the degree. -/
theorem tateDegreeEquiv_naturality {A B : Rep.{u} ℤ G} (f : A ⟶ B)
    {i j : ℤ} (h : i = j) (x : tate A i) :
    (tateFunctor G j).map f (tateDegreeEquiv A h x) =
      tateDegreeEquiv B h ((tateFunctor G i).map f x) := by
  subst j
  rfl

/-- The total degree with a nonnegative increment, computed by right shifts. -/
def cupNonnegativeDegree (p : ℤ) : ℕ → ℤ
  | 0 => p
  | n + 1 => cupNonnegativeDegree p n + 1

/-- The shifted total degree is the sum of the input degrees. -/
theorem cupNonnegativeDegree_eq (p : ℤ) (n : ℕ) : cupNonnegativeDegree p n = p + n := by
  induction n with
  | zero => exact (add_zero p).symm
  | succ n ih =>
    change cupNonnegativeDegree p n + 1 = p + (n + 1 : ℕ)
    rw [ih, Nat.cast_succ, add_assoc]

/-- Cup product with a class in a nonnegative right degree. -/
def tateCupNonnegative (A : Rep.{u} ℤ G) (p : ℤ) :
    (n : ℕ) → (B : Rep.{u} ℤ G) →
      tate A p →ₗ[ℤ] tate B n →ₗ[ℤ] tate (A ⊗ᵣ B) (cupNonnegativeDegree p n)
  | 0, B => tensorCupZeroRight A B p
  | n + 1, B => integerBilinearMapAlong (tateCupNonnegative A p n (Rep.coindShiftUp B))
    LinearMap.id (coindShiftUpEquiv B n).symm.toLinearMap
    ((p.negOnePow : ℤ) • (tensorCoindShiftEquiv A B (cupNonnegativeDegree p n)).toLinearMap)

/-- Cup product with a class in a negative right degree. -/
def tateCupNegative (A : Rep.{u} ℤ G) (p : ℤ) :
    (n : ℕ) → (B : Rep.{u} ℤ G) →
      tate A p →ₗ[ℤ] tate B (Int.negSucc n) →ₗ[ℤ] tate (A ⊗ᵣ B) (p - (n + 1 : ℕ))
  | 0, B =>
    let e := tensorIndShiftEquiv A B (p - (0 + 1 : ℕ))
    let c := tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (show p = p - (0 + 1 : ℕ) + 1 by omega)
    integerBilinearMapAlong (tensorCupZeroRight A (Rep.indShiftDown B) p) LinearMap.id
      (indShiftDownEquiv B (Int.negSucc 0)).toLinearMap
      ((p.negOnePow : ℤ) • (c.trans e.symm).toLinearMap)
  | n + 1, B =>
    let e := tensorIndShiftEquiv A B (p - (n + 1 + 1 : ℕ))
    let c := tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B)
      (show p - (n + 1 : ℕ) = p - (n + 1 + 1 : ℕ) + 1 by omega)
    integerBilinearMapAlong (tateCupNegative A p n (Rep.indShiftDown B)) LinearMap.id
      (indShiftDownEquiv B (Int.negSucc (n + 1))).toLinearMap
      ((p.negOnePow : ℤ) • (c.trans e.symm).toLinearMap)

/-- The bilinear cup product on the original integral Tate groups in all
integer degrees. It uses the original tensor representation. -/
def tateCup (A B : Rep.{u} ℤ G) (p q r : ℤ) (h : p + q = r) :
    tate A p →ₗ[ℤ] tate B q →ₗ[ℤ] tate (A ⊗ᵣ B) r :=
  match q, h with
  | .ofNat n, h => integerBilinearMapAlong (tateCupNonnegative A p n B) LinearMap.id LinearMap.id
    (tateDegreeEquiv (A ⊗ᵣ B) ((cupNonnegativeDegree_eq p n).trans h)).toLinearMap
  | .negSucc n, h =>
    let e := tateDegreeEquiv (A ⊗ᵣ B) ((show p - (n + 1 : ℕ) = p + Int.negSucc n by omega).trans h)
    integerBilinearMapAlong (tateCupNegative A p n B) LinearMap.id LinearMap.id e.toLinearMap

/-- The cup product with a degree-zero right factor is the actual tensor pairing. -/
theorem tateCup_zero_right (A B : Rep.{u} ℤ G) (p : ℤ) (h : p + 0 = p) :
    tateCup A B p 0 p h = tensorCupZeroRight A B p := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

/-- The upward recursion uses the canonical tensor connecting map and the
sign of the left degree. -/
theorem tateCupNonnegative_succ_apply (A B : Rep.{u} ℤ G) (p : ℤ) (n : ℕ)
    (x : tate A p) (y : tate B (n + 1 : ℕ)) :
    tateCupNonnegative A p (n + 1) B x y = p.negOnePow •
      tensorCoindShiftEquiv A B (cupNonnegativeDegree p n)
        (tateCupNonnegative A p n (Rep.coindShiftUp B) x ((coindShiftUpEquiv B n).symm y)) := rfl

/-- The downward step from degree zero uses the specified inverse connecting map. -/
theorem tateCupNegative_zero_apply (A B : Rep.{u} ℤ G) (p : ℤ) (x : tate A p)
    (y : tate B (Int.negSucc 0)) :
    tateCupNegative A p 0 B x y = p.negOnePow •
      (tensorIndShiftEquiv A B (p - (0 + 1 : ℕ))).symm
        (tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
          (tensorCupZeroRight A (Rep.indShiftDown B) p x
            (indShiftDownEquiv B (Int.negSucc 0) y))) := by
  rw [tateCupNegative]
  rfl

/-- The downward recursion uses the same tensor connecting map in each lower degree. -/
theorem tateCupNegative_succ_apply (A B : Rep.{u} ℤ G) (p : ℤ) (n : ℕ)
    (x : tate A p) (y : tate B (Int.negSucc (n + 1))) :
    tateCupNegative A p (n + 1) B x y = p.negOnePow •
      (tensorIndShiftEquiv A B (p - (n + 1 + 1 : ℕ))).symm
        (tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
          (tateCupNegative A p n (Rep.indShiftDown B) x
            (indShiftDownEquiv B (Int.negSucc (n + 1)) y))) := rfl

/-- In nonnegative degrees the defining cup identity is the signed
connecting-map identity for the actual coinduced sequence. -/
theorem tateCupNonnegative_connecting (A B : Rep.{u} ℤ G) (p : ℤ) (n : ℕ)
    (x : tate A p) (y : tate (Rep.coindShiftUp B) n) :
    tateCupNonnegative A p (n + 1) B x (coindShiftUpEquiv B n y) = p.negOnePow •
      tensorCoindShiftEquiv A B (cupNonnegativeDegree p n)
        (tateCupNonnegative A p n (Rep.coindShiftUp B) x y) := by
  rw [tateCupNonnegative_succ_apply, LinearEquiv.symm_apply_apply]

/-- The negative recursion satisfies the signed connecting-map identity at
the transition from degree minus one to degree zero. -/
theorem tateCupNegative_zero_connecting (A B : Rep.{u} ℤ G) (p : ℤ)
    (x : tate A p) (y : tate B (Int.negSucc 0)) :
    tensorIndShiftEquiv A B (p - (0 + 1 : ℕ)) (tateCupNegative A p 0 B x y) =
      p.negOnePow • tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
        (tensorCupZeroRight A (Rep.indShiftDown B) p x
          (indShiftDownEquiv B (Int.negSucc 0) y)) := by
  rw [tateCupNegative_zero_apply]
  simp only [Units.smul_def]
  let e := tensorIndShiftEquiv A B (p - (0 + 1 : ℕ))
  exact (map_zsmul e.toLinearMap.toAddMonoidHom (p.negOnePow : ℤ) _).trans
    (congrArg ((p.negOnePow : ℤ) • ·) (e.apply_symm_apply _))

/-- Below degree minus one, applying the actual tensor connecting map
recovers the previous product with the prescribed sign. -/
theorem tateCupNegative_succ_connecting (A B : Rep.{u} ℤ G) (p : ℤ) (n : ℕ)
    (x : tate A p) (y : tate B (Int.negSucc (n + 1))) :
    tensorIndShiftEquiv A B (p - (n + 1 + 1 : ℕ)) (tateCupNegative A p (n + 1) B x y) =
      p.negOnePow • tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
        (tateCupNegative A p n (Rep.indShiftDown B) x
          (indShiftDownEquiv B (Int.negSucc (n + 1)) y)) := by
  rw [tateCupNegative_succ_apply]
  simp only [Units.smul_def]
  let e := tensorIndShiftEquiv A B (p - (n + 1 + 1 : ℕ))
  exact (map_zsmul e.toLinearMap.toAddMonoidHom (p.negOnePow : ℤ) _).trans
    (congrArg ((p.negOnePow : ℤ) • ·) (e.apply_symm_apply _))

/-- The signed coinduction connecting rule in the original integer-degree indexing. -/
theorem tateCup_coindShift_connecting (A B : Rep.{u} ℤ G) {p q r : ℤ}
    (hq : 0 ≤ q) (h : p + q = r) (x : tate A p) (y : tate (Rep.coindShiftUp B) q) :
    tateCup A B p (q + 1) (r + 1) (by omega) x (coindShiftUpEquiv B q y) =
      p.negOnePow • tensorCoindShiftEquiv A B r
        (tateCup A (Rep.coindShiftUp B) p q r h x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain rfl : r = cupNonnegativeDegree p n := h.symm.trans (cupNonnegativeDegree_eq p n).symm
  change tateCupNonnegative A p (n + 1) B x (coindShiftUpEquiv B n y) =
    p.negOnePow • tensorCoindShiftEquiv A B (cupNonnegativeDegree p n)
      (tateCupNonnegative A p n (Rep.coindShiftUp B) x y)
  exact tateCupNonnegative_connecting A B p n x y

/-- The signed induction connecting rule in the original integer-degree indexing. -/
theorem tateCup_indShift_connecting (A B : Rep.{u} ℤ G) {p q r : ℤ}
    (hq : q < 0) (h : p + q = r) (x : tate A p) (y : tate B q) :
    tateCup A (Rep.indShiftDown B) p (q + 1) (r + 1) (by omega) x (indShiftDownEquiv B q y) =
      p.negOnePow • tensorIndShiftEquiv A B r (tateCup A B p q r h x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
  obtain rfl : r = p - (n + 1 : ℕ) := by omega
  cases n with
  | zero =>
    change tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
        (tensorCupZeroRight A (Rep.indShiftDown B) p x (indShiftDownEquiv B (-1) y)) =
      p.negOnePow • tensorIndShiftEquiv A B (p - (0 + 1 : ℕ)) (tateCupNegative A p 0 B x y)
    rw [tateCupNegative_zero_connecting, smul_smul, Int.units_mul_self, one_smul]
    rfl
  | succ n =>
    change tateDegreeEquiv (A ⊗ᵣ Rep.indShiftDown B) (by omega)
        (tateCupNegative A p n (Rep.indShiftDown B) x
          (indShiftDownEquiv B (Int.negSucc (n + 1)) y)) =
      p.negOnePow • tensorIndShiftEquiv A B (p - (n + 1 + 1 : ℕ))
        (tateCupNegative A p (n + 1) B x y)
    rw [tateCupNegative_succ_connecting, smul_smul, Int.units_mul_self, one_smul]

private theorem tateMap_smul {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n c : ℤ) (x : tate A n) :
    (tateFunctor G n).map f (c • x) = c • (tateFunctor G n).map f x :=
  map_zsmul ((tateFunctor G n).map f).hom.toAddMonoidHom c x

private theorem tateCupNonnegative_naturality {A C : Rep.{u} ℤ G}
    (f : A ⟶ C) (p : ℤ) (x : tate A p) (n : ℕ) :
    ∀ {B D : Rep.{u} ℤ G} (g : B ⟶ D) (y : tate B n),
      (tateFunctor G (cupNonnegativeDegree p n)).map (f ⊗ᵣₘ g)
        (tateCupNonnegative A p n B x y) =
      tateCupNonnegative C p n D ((tateFunctor G p).map f x) ((tateFunctor G n).map g y) := by
  induction n with
  | zero =>
    intro B D g y
    exact tensorCupZeroRight_natural f g p x y
  | succ n ih =>
    intro B D g y
    have hpre : (tateFunctor G n).map (Rep.coindShiftUpMap g) ((coindShiftUpEquiv B n).symm y) =
        (coindShiftUpEquiv D n).symm ((tateFunctor G (n + 1 : ℕ)).map g y) := by
      apply (coindShiftUpEquiv D n).injective
      rw [LinearEquiv.apply_symm_apply, ← coindShiftUpEquiv_naturality_apply,
        LinearEquiv.apply_symm_apply]
      rfl
    simp only [tateCupNonnegative_succ_apply, Units.smul_def]
    have hsmul := tateMap_smul (f ⊗ᵣₘ g) (cupNonnegativeDegree p n + 1)
      (p.negOnePow : ℤ) (tensorCoindShiftEquiv A B (cupNonnegativeDegree p n)
        (tateCupNonnegative A p n (Rep.coindShiftUp B) x ((coindShiftUpEquiv B n).symm y)))
    refine hsmul.trans ?_
    rw [tensorCoindShiftEquiv_naturality, ih, hpre]

private theorem tateCupNegative_naturality {A C : Rep.{u} ℤ G}
    (f : A ⟶ C) (p : ℤ) (x : tate A p) (n : ℕ) :
    ∀ {B D : Rep.{u} ℤ G} (g : B ⟶ D) (y : tate B (Int.negSucc n)),
      (tateFunctor G (p - (n + 1 : ℕ))).map (f ⊗ᵣₘ g) (tateCupNegative A p n B x y) =
      tateCupNegative C p n D ((tateFunctor G p).map f x)
        ((tateFunctor G (Int.negSucc n)).map g y) := by
  induction n with
  | zero =>
    intro B D g y
    simp only [tateCupNegative_zero_apply, Units.smul_def, tateMap_smul]
    rw [tensorIndShiftEquiv_symm_naturality, tateDegreeEquiv_naturality,
      tensorCupZeroRight_natural]
    let e := tensorIndShiftEquiv C D (p - (0 + 1 : ℕ))
    let t := tateDegreeEquiv (C ⊗ᵣ Rep.indShiftDown D) (show p = p - (0 + 1 : ℕ) + 1 by omega)
    let z := (tateFunctor G p).map f x
    exact congrArg (fun b => (p.negOnePow : ℤ) • e.symm (t (tensorCupZeroRight C _ p z b)))
      (indShiftDownEquiv_naturality_apply g (Int.negSucc 0) y)
  | succ n ih =>
    intro B D g y
    simp only [tateCupNegative_succ_apply, Units.smul_def, tateMap_smul]
    rw [tensorIndShiftEquiv_symm_naturality, tateDegreeEquiv_naturality, ih]
    let e := tensorIndShiftEquiv C D (p - (n + 1 + 1 : ℕ))
    let t := tateDegreeEquiv (C ⊗ᵣ Rep.indShiftDown D)
      (show p - (n + 1 : ℕ) = p - (n + 1 + 1 : ℕ) + 1 by omega)
    let z := (tateFunctor G p).map f x
    exact congrArg (fun b => (p.negOnePow : ℤ) • e.symm (t (tateCupNegative C p n _ z b)))
      (indShiftDownEquiv_naturality_apply g (Int.negSucc (n + 1)) y)

/-- Cup products in every bidegree commute with the original equivariant
maps of both coefficients. -/
theorem tateCup_naturality {A B C D : Rep.{u} ℤ G} (f : A ⟶ C) (g : B ⟶ D)
    (p q r : ℤ) (h : p + q = r) (x : tate A p) (y : tate B q) :
    (tateFunctor G r).map (f ⊗ᵣₘ g) (tateCup A B p q r h x y) =
      tateCup C D p q r h ((tateFunctor G p).map f x) ((tateFunctor G q).map g y) := by
  cases q with
  | ofNat n =>
    simp only [tateCup, integerBilinearMapAlong_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      tateDegreeEquiv_naturality, tateCupNonnegative_naturality]
    rfl
  | negSucc n =>
    simp only [tateCup, integerBilinearMapAlong_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      tateDegreeEquiv_naturality, tateCupNegative_naturality]

/-- The same cup construction with independently sized groups and coefficient
carriers uses the established native Tate comparisons, and the original tensor. -/
def tateCupIndependent (A B : Rep.{v} ℤ G) (p q r : ℤ) (h : p + q = r) :
    tate A p →ₗ[ℤ] tate B q →ₗ[ℤ] tate (A ⊗ᵣ B) r := by
  let F := Rep.universeLiftFunctor ℤ G
  let eA := tateIsoCommon (F.obj A) p
  let eB := tateIsoCommon (F.obj B) q
  let eT := (tateFunctor (ULift.{v} G) r).mapIso (Rep.universeLiftIntegerTensorIso A B) ≪≫
    tateIsoCommon (F.obj (A ⊗ᵣ B)) r
  exact integerBilinearMapAlong (tateCup (F.obj A) (F.obj B) p q r h)
    eA.inv.hom eB.inv.hom eT.hom.hom

/-- Cup product from trivial integer coefficients, followed by the original
tensor unitor. In degree two this is the map used for a fundamental class. -/
def tateCupTrivialInteger (A : Rep.{v} ℤ G) (p q r : ℤ) (h : p + q = r) (y : tate A q) :
    tate (integralTrivialInteger.{u, v} G) p →ₗ[ℤ] tate A r := by
  let Z := integralTrivialInteger.{u, v} G
  let cup := tateCupIndependent Z A p q r h
  let unit := (tateFunctor G r).map (integerTensorLeftUnitIso A).hom
  let eval : (tate A q →ₗ[ℤ] tate (Z ⊗ᵣ A) r) →+ tate (Z ⊗ᵣ A) r :=
    { toFun := fun f => f y, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact unit.hom.comp (integerModuleLinearMap (eval.comp cup.toAddMonoidHom))

/-- In degree minus two, cup with the supplied degree-two class starts at the
actual abelianization. The forward map is the positive bar-chain convention. -/
def tateNegTwoCupMap (A : Rep.{v} ℤ G) (y : tate A 2) :
    Additive (Group.Abelianization G) →ₗ[ℤ] tate A 0 :=
  (tateCupTrivialInteger A (-2) 2 0 (by decide) y).comp
    (tateNegTwoUnitAbelianizationEquiv G).symm.toIntLinearEquiv.toLinearMap

/-- On an abelianization generator this is exactly cup product of the original bar chain. -/
theorem tateNegTwoCupMap_of (A : Rep.{v} ℤ G) (y : tate A 2) (g : G) :
    tateNegTwoCupMap A y (Additive.ofMul (Group.Abelianization.of g)) =
      tateCupTrivialInteger A (-2) 2 0 (by decide) y
        (tateNegTwoUnitClass G g : tate (integralTrivialInteger.{u, v} G) (-2)) := by
  have h := tateNegTwoUnitAbelianizationEquiv_class.{u, v} G g
  change tateCupTrivialInteger A (-2) 2 0 (by decide) y
      ((tateNegTwoUnitAbelianizationEquiv G).symm (Additive.ofMul (Group.Abelianization.of g))) = _
  rw [← h, AddEquiv.symm_apply_apply]

/-- Using the negative bar chain instead negates the output of the cup map. -/
theorem tateNegTwoCupMap_neg_of (A : Rep.{v} ℤ G) (y : tate A 2) (g : G) :
    tateNegTwoCupMap A y (-Additive.ofMul (Group.Abelianization.of g)) =
      -tateCupTrivialInteger A (-2) 2 0 (by decide) y
        (tateNegTwoUnitClass G g : tate (integralTrivialInteger.{u, v} G) (-2)) := by
  rw [map_neg, tateNegTwoCupMap_of]

end IntegralGroupCohomology.Universe
