/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.GaloisCohomology.Topology.ContinuousRepresentationUniverseLift
public import Nyll.GaloisCohomology.Topology.ContinuousDual
public import Nyll.GaloisCohomology.Topology.ContinuousNormalSubgroupH1

/-! # Transposition of continuous characters through the actual coefficient dual -/

@[expose] public section

open Function TopRep

noncomputable section

namespace ContinuousCohomology

universe u

variable {G H : Type u} [Group G] [Group H] [TopologicalSpace H]
  (A B : TopRep.{u} ℤ G) [Finite A] [Finite B] [DiscreteTopology A] [DiscreteTopology B]

attribute [local instance] TopRep.integralModuleOfRepresentation

/-- Evaluation of a continuous character at an original group element. -/
def continuousCharacterEval (X : TopRep.{u} ℤ G) (h : H) :
    Additive (H →ₜ* Multiplicative X) →ₗ[ℤ] X := by
  let ev : Additive (H →ₜ* Multiplicative X) →+ X :=
    { toFun := fun x => (x.toMul h).toAdd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact
    { toFun := ev
      map_add' := ev.map_add
      map_smul' := fun i χ => by
        change ev (i • χ) = X.hV2.smul i (ev χ)
        rw [int_smul_eq_zsmul X.hV2, map_zsmul] }

/-- Postcomposition of the original character by a coefficient map. -/
def continuousCharacterPostcomp (χ : H →ₜ* Multiplicative A) (f : A →ₗ[ℤ] B) :
    H →ₜ* Multiplicative B where
  toMonoidHom := f.toAddMonoidHom.toMultiplicative.comp χ.toMonoidHom
  continuous_toFun := by
    have hf : Continuous (fun x : Multiplicative A => Multiplicative.ofAdd (f x.toAdd)) :=
      continuous_of_discreteTopology
    exact hf.comp χ.continuous

/-- Transpose a character by postcomposing it with each actual coefficient
linear map into the dualizing module. -/
def continuousCharacterTranspose (χ : Additive (H →ₜ* Multiplicative A)) :
    discreteLinearDual A B →ₗ[ℤ] Additive (H →ₜ* Multiplicative B) := by
  let t : discreteLinearDual A B →+ Additive (H →ₜ* Multiplicative B) :=
    { toFun := fun f => Additive.ofMul
        (continuousCharacterPostcomp A B χ.toMul (discreteLinearDualMap A B f))
      map_zero' := ContinuousMonoidHom.ext fun _ => rfl
      map_add' := fun _ _ => ContinuousMonoidHom.ext fun _ => rfl }
  exact
    { toFun := t
      map_add' := t.map_add
      map_smul' := fun i f => by
        change t ((A.discreteLinearDual B).hV2.smul i f) = i • t f
        rw [int_smul_eq_zsmul (A.discreteLinearDual B).hV2, map_zsmul] }

omit [Finite A] [Finite B] [DiscreteTopology B] in
theorem continuousCharacterTranspose_eval (χ : Additive (H →ₜ* Multiplicative A))
    (l : discreteLinearDual A B) (h : H) :
    ((continuousCharacterTranspose A B χ l).toMul h).toAdd =
      discreteLinearDualMap A B l ((χ.toMul h).toAdd) := rfl

variable (hbid : Bijective (discreteLinearDualBidualMap A B))

/-- The inverse transpose obtained by the actual bidual evaluation. -/
def dualCharacterTransposeBack
    (f : discreteLinearDual A B →ₗ[ℤ] Additive (H →ₜ* Multiplicative B)) :
    H →ₜ* Multiplicative A := by
  let d := (discreteLinearDualBidualMap A B).hom.toContinuousLinearMap.toLinearMap
  let E := LinearEquiv.ofBijective d hbid
  let v (h : H) : (discreteLinearDual A B) →ₗ[ℤ] B := (continuousCharacterEval B h).comp f
  let u (h : H) : A := E.symm (v h)
  have hu (h : H) (l : discreteLinearDual A B) :
      discreteLinearDualMap A B l (u h) = ((f l).toMul h).toAdd :=
    LinearMap.congr_fun (E.apply_symm_apply (v h)) l
  have hdet : Injective (fun a : A => fun l : discreteLinearDual A B =>
      discreteLinearDualMap A B l a) := by
    intro a b hab
    apply hbid.1
    exact LinearMap.ext fun l => congrFun hab l
  refine
    ⟨{ toFun := fun h => Multiplicative.ofAdd (u h)
       map_one' := ?_
       map_mul' := ?_ }, ?_⟩
  · apply Multiplicative.toAdd.injective
    apply hdet
    funext l
    change discreteLinearDualMap A B l (u 1) = discreteLinearDualMap A B l 0
    rw [hu, map_one, map_zero]
    rfl
  · intro h k
    apply Multiplicative.toAdd.injective
    apply hdet
    funext l
    change discreteLinearDualMap A B l (u (h * k)) = discreteLinearDualMap A B l (u h + u k)
    simp only [hu, map_add, map_mul, toAdd_mul]
  · let : Finite (discreteLinearDual A B) := discreteLinearDual_finite A B
    let F (a : A) (l : (discreteLinearDual A B)) := discreteLinearDualMap A B l a
    let C₀ (h : H) (l : (discreteLinearDual A B)) := ((f l).toMul h).toAdd
    have hf : Continuous C₀ := continuous_pi fun l => (f l).toMul.continuous
    have hC : Continuous ((fun v : (discreteLinearDual A B) → B => Function.invFun F v) ∘ C₀) :=
      continuous_of_discreteTopology.comp hf
    have hU : (fun h => Function.invFun F (C₀ h)) = u := by
      funext h
      have hF : F (u h) = C₀ h := funext (hu h)
      rw [← hF, Function.leftInverse_invFun hdet]
    change Continuous u
    exact hU ▸ hC

/-- The inverse transpose is characterized by evaluation on each original functional. -/
theorem dualCharacterTransposeBack_eval
    (f : discreteLinearDual A B →ₗ[ℤ] Additive (H →ₜ* Multiplicative B))
    (h : H) (l : discreteLinearDual A B) :
    discreteLinearDualMap A B l ((dualCharacterTransposeBack A B hbid f h).toAdd) =
      ((f l).toMul h).toAdd := by
  let d := (discreteLinearDualBidualMap A B).hom.toContinuousLinearMap.toLinearMap
  let E := LinearEquiv.ofBijective d hbid
  exact LinearMap.congr_fun (E.apply_symm_apply ((continuousCharacterEval B h).comp f)) l

/-- Actual continuous characters are the linear maps out of the twisted dual
into the continuous characters with values in the dualizing module. -/
def continuousCharacterTransposeEquiv :
    Additive (H →ₜ* Multiplicative A) ≃
      (discreteLinearDual A B →ₗ[ℤ] Additive (H →ₜ* Multiplicative B)) where
  toFun := continuousCharacterTranspose A B
  invFun f := Additive.ofMul (dualCharacterTransposeBack A B hbid f)
  left_inv χ := by
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro h
    apply Multiplicative.toAdd.injective
    apply hbid.1
    apply LinearMap.ext
    intro l
    exact (dualCharacterTransposeBack_eval A B hbid _ h l).trans
      (continuousCharacterTranspose_eval A B χ l h)
  right_inv f := by
    apply LinearMap.ext
    intro l
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro h
    apply Multiplicative.toAdd.injective
    exact dualCharacterTransposeBack_eval A B hbid f h l

section NormalSubgroup

variable [TopologicalSpace G] [IsTopologicalGroup G]
    (S : OpenSubgroup G) [(S : Subgroup G).Normal]

/-- Linear maps into the actual characters of the subgroup that are
equivariant for conjugation and the original coefficient actions. -/
def normalOpenDualCharacterMaps :
    Set (discreteLinearDual A B →ₗ[ℤ] Additive (↥S.toSubgroup →ₜ* Multiplicative B)) :=
  {f | ∀ (g : G) (l : discreteLinearDual A B) (h : ↥S.toSubgroup),
    ((f ((discreteLinearDual A B).ρ g l)).toMul (normalOpenConjugate S g h)).toAdd =
      B.ρ g ((f l).toMul h).toAdd}

/-- The original invariant characters transpose to the actual equivariant
linear maps into dualizing characters. -/
def normalOpenInvariantCharacterTransposeEquiv :
    normalOpenInvariantCharacters A S ≃ normalOpenDualCharacterMaps A B S := by
  refine (continuousCharacterTransposeEquiv (H := ↥S.toSubgroup) A B hbid).subtypeEquiv
    (fun χ => ?_)
  change χ ∈ normalOpenInvariantCharacters A S ↔
    continuousCharacterTranspose A B χ ∈ normalOpenDualCharacterMaps A B S
  constructor
  · intro hχ g l h
    change ((continuousCharacterTranspose A B χ ((discreteLinearDual A B).ρ g l)).toMul
      (normalOpenConjugate S g h)).toAdd =
        B.ρ g (((continuousCharacterTranspose A B χ l).toMul h).toAdd)
    rw [continuousCharacterTranspose_eval, continuousCharacterTranspose_eval]
    have hx : (χ.toMul (normalOpenConjugate S g h)).toAdd = A.ρ g (χ.toMul h).toAdd := hχ g h
    rw [hx]
    exact discreteLinearDualEvaluation_equivariant A B g (χ.toMul h).toAdd l
  · intro hχ g h
    apply hbid.1
    apply LinearMap.ext
    intro l
    let b := (discreteLinearDual A B).ρ g⁻¹ l
    have hb : (discreteLinearDual A B).ρ g b = l := by
      have h₁ := DFunLike.congr_fun (map_mul (discreteLinearDual A B).ρ g g⁻¹).symm l
      rw [mul_inv_cancel, map_one] at h₁
      exact h₁
    have hx := hχ g b h
    change ((continuousCharacterTranspose A B χ ((discreteLinearDual A B).ρ g b)).toMul
      (normalOpenConjugate S g h)).toAdd =
        B.ρ g (((continuousCharacterTranspose A B χ b).toMul h).toAdd) at hx
    rw [continuousCharacterTranspose_eval, continuousCharacterTranspose_eval, hb] at hx
    have he := discreteLinearDualEvaluation_equivariant A B g (χ.toMul h).toAdd b
    change discreteLinearDualMap A B ((discreteLinearDual A B).ρ g b) (A.ρ g (χ.toMul h).toAdd) =
      B.ρ g (discreteLinearDualMap A B b (χ.toMul h).toAdd) at he
    rw [hb] at he
    exact hx.trans he.symm

/-- Degree-one cohomology at a coprime open subgroup is the actual module
of dual-linear Galois-equivariant continuous characters. -/
def normalOpenH1DualCharacterEquiv [CompactSpace G] (p : ℕ) [Fact p.Prime]
    (hA : ∀ a : A, p • a = 0) (hS : ¬p ∣ S.toSubgroup.index)
    (htriv : ∀ (h : (↥S.toSubgroup)) (a : A), A.ρ (h : G) a = a) :
    continuousCohomology 1 A ≃ normalOpenDualCharacterMaps A B S :=
  (normalOpenH1RestrictionEquiv A S htriv p hA hS).toEquiv.trans
    (normalOpenInvariantCharacterTransposeEquiv A B hbid S)

end NormalSubgroup

section TrivialCoefficients

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

local instance openTopNormal : ((⊤ : OpenSubgroup G).toSubgroup).Normal := by
  change (⊤ : Subgroup G).Normal
  infer_instance

/-- The canonical continuous identification with the top open subgroup. -/
def openTopCharacterEmbedding : G →ₜ* (↥(⊤ : OpenSubgroup G).toSubgroup) :=
  { toMonoidHom := Subgroup.topEquiv.symm.toMonoidHom
    continuous_toFun := continuous_id.subtype_mk (fun _ => Subgroup.mem_top _) }

/-- Trivial actions identify top-subgroup invariant characters with ambient characters. -/
def normalTopInvariantCharacterEquiv (hA : ∀ g : G, ∀ a : A, A.ρ g a = a) :
    normalOpenInvariantCharacters A (⊤ : OpenSubgroup G) ≃+ Additive (G →ₜ* Multiplicative A) where
  toFun χ := Additive.ofMul (χ.val.toMul.comp openTopCharacterEmbedding)
  invFun χ := ⟨Additive.ofMul (χ.toMul.comp
      (ProCGroups.ContinuousMonoidHom.subtype (⊤ : OpenSubgroup G).toSubgroup)), by
    intro g h
    change (χ.toMul (g * (h : G) * g⁻¹)).toAdd = A.ρ g (χ.toMul h).toAdd
    rw [hA]
    apply congrArg Multiplicative.toAdd
    rw [map_mul, map_mul, map_inv]
    calc
      χ.toMul g * χ.toMul h * (χ.toMul g)⁻¹ =
          χ.toMul h * (χ.toMul g * (χ.toMul g)⁻¹) := by ac_rfl
      _ = χ.toMul h := by rw [mul_inv_cancel, mul_one]⟩
  left_inv χ := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro h
    exact congrArg χ.val.toMul (Subtype.ext rfl : openTopCharacterEmbedding (h : G) = h)
  right_inv χ := by
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro g
    rfl
  map_add' _ _ := by
    apply Additive.toMul.injective
    apply ContinuousMonoidHom.ext
    intro g
    rfl

/-- For a trivial prime-annihilated coefficient, first cohomology consists
of its original continuous characters. -/
def trivialH1ContinuousCharacterEquiv (hA : ∀ g : G, ∀ a : A, A.ρ g a = a)
    (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0) :
    continuousCohomology 1 A ≃+ Additive (G →ₜ* Multiplicative A) :=
  (normalOpenH1RestrictionEquiv (G := G) A (⊤ : OpenSubgroup G) (fun h => hA h) p hpA (by
    change ¬p ∣ (⊤ : Subgroup G).index
    rw [Subgroup.index_top]
    exact (Fact.out : p.Prime).not_dvd_one)).trans
      (normalTopInvariantCharacterEquiv A hA)

omit [Finite A] [DiscreteTopology A] in
theorem trivialH1ContinuousCharacterEquiv_π_apply
    (hA : ∀ g : G, ∀ a : A, A.ρ g a = a)
    (p : ℕ) [Fact p.Prime] (hpA : ∀ a : A, p • a = 0) (z : cocycles A 1) (g : G) :
    ((trivialH1ContinuousCharacterEquiv A hA p hpA (π A 1 z)).toMul g).toAdd =
      (crossedHomOfCocycle A z).toFun g :=
  normalOpenH1RestrictionEquiv_π_apply (G := G) A (⊤ : OpenSubgroup G) (fun h => hA h) p hpA
    (by
      change ¬p ∣ (⊤ : Subgroup G).index
      rw [Subgroup.index_top]
      exact (Fact.out : p.Prime).not_dvd_one)
    z (openTopCharacterEmbedding g)

end TrivialCoefficients

end ContinuousCohomology
