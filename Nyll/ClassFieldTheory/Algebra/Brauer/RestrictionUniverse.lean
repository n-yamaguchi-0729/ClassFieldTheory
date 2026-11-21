/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.GaloisCohomology.Topology.ContinuousH2UniverseMap

/-! # Actual Brauer restriction between fields in different universes -/

public section

noncomputable section

open CategoryTheory ContinuousCohomology Field.absoluteGaloisGroup

namespace ClassFieldTheory.Brauer

universe u v w

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Field M]

private def closureUnitsMap (a : SeparableClosure K →+* SeparableClosure L) :
    unitsRep K →+ unitsRep L :=
  (Units.map a.toMonoidHom).toAdditive

private theorem closureUnitsMap_equivariant
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x))
    (σ : Gal(SeparableClosure L/L)) (x : unitsRep K) :
    closureUnitsMap a ((unitsRep K).ρ (r σ) x) = (unitsRep L).ρ σ (closureUnitsMap a x) := by
  apply Units.ext
  exact h σ ((show Additive (SeparableClosure K)ˣ from x).toMul : SeparableClosure K)

private def restrictOfEmbeddingAcross
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x)) :
    Br K →+ Br L :=
  universeMapH2 r (closureUnitsMap a) continuous_of_discreteTopology
    (closureUnitsMap_equivariant r a h)

/-- Restrict along the original field embedding using the original
separable-closure maps, with independent source and target universes. -/
def restrictAcross (f : K →+* L) : Br K →+ Br L :=
  restrictOfEmbeddingAcross (separableMap f) (separableClosureLift f) (separableMap_commutes f)

private theorem restrictOfEmbeddingAcross_same {L : Type u} [Field L]
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x)) :
    restrictOfEmbeddingAcross r a h = restrictOfEmbedding r a h := by
  apply AddMonoidHom.ext
  intro x
  exact universeMapH2_eq_map r (galoisUnitsMap r a h) (closureUnitsMap a)
    continuous_of_discreteTopology (closureUnitsMap_equivariant r a h) (fun _ => rfl) x

/-- The independent-universe construction agrees with the original restriction. -/
theorem restrictAcross_same {L : Type u} [Field L] (f : K →+* L) : restrictAcross f = restrict f :=
  restrictOfEmbeddingAcross_same (separableMap f) (separableClosureLift f) (separableMap_commutes f)

private theorem restrictOfEmbeddingAcross_comp
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x))
    (s : Gal(SeparableClosure M/M) →ₜ* Gal(SeparableClosure L/L))
    (b : SeparableClosure L →+* SeparableClosure M)
    (k : ∀ (σ : Gal(SeparableClosure M/M)) (x : SeparableClosure L), b (s σ x) = σ (b x)) :
    (restrictOfEmbeddingAcross s b k).comp (restrictOfEmbeddingAcross r a h) =
      restrictOfEmbeddingAcross (r.comp s) (b.comp a)
        (fun σ x => (congrArg b (h (s σ) x)).trans (k σ (a x))) :=
  universeMapH2_comp
    r (closureUnitsMap a) continuous_of_discreteTopology (closureUnitsMap_equivariant r a h)
    s (closureUnitsMap b) continuous_of_discreteTopology (closureUnitsMap_equivariant s b k)

private theorem restrictOfEmbeddingAcross_eq_of_extends (f : K →+* L)
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (f x))
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x)) :
    restrictOfEmbeddingAcross r a h = restrictAcross f := by
  let Ω := SeparableClosure L
  let : Algebra K Ω := ((algebraMap L Ω).comp f).toAlgebra
  let i : SeparableClosure K →ₐ[K] Ω := { __ := a, commutes' := ha }
  let j : SeparableClosure K →ₐ[K] Ω :=
    { __ := separableClosureLift f, commutes' := separableClosureLift_algebraMap f }
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal i j
  have hcomp : (separableClosureLift f).comp τ.toRingHom = a := RingHom.ext hτ
  subst a
  let c : Gal(SeparableClosure K/K) →ₜ* Gal(SeparableClosure K/K) :=
    { toFun := fun σ => τ⁻¹ * σ * τ
      map_one' := by group
      map_mul' := fun σ ρ => by group
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hc (σ : Gal(SeparableClosure K/K)) (x : SeparableClosure K) : τ (c σ x) = σ (τ x) := by
    have he : τ * c σ = σ * τ := by change τ * (τ⁻¹ * σ * τ) = σ * τ; group
    exact congrArg (fun g : Gal(SeparableClosure K/K) => g x) he
  have hgroup : c.comp (separableMap f) = r := by
    apply ContinuousMonoidHom.ext
    intro σ
    apply AlgEquiv.ext
    intro x
    apply ((separableClosureLift f).comp τ.toRingHom).injective
    change separableClosureLift f (τ (c (separableMap f σ) x)) =
      ((separableClosureLift f).comp τ.toRingHom) (r σ x)
    rw [hc, separableMap_commutes f, h]
    rfl
  have hid : restrictOfEmbeddingAcross c τ.toRingHom hc = AddMonoidHom.id (Br K) := by
    refine (restrictOfEmbeddingAcross_same c τ.toRingHom hc).trans ?_
    let α := galoisUnitsMap c τ.toRingHom hc
    have hα (x : unitsRep K) : α x = (unitsRep K).ρ τ x := by
      apply Additive.toMul.injective
      apply Units.ext
      rfl
    have hm := map_inner_eq_id_two (unitsRep K) τ c α (fun _ => rfl) hα
    apply AddMonoidHom.ext
    intro x
    change ContinuousCohomology.map c α 2 x = x
    exact ConcreteCategory.congr_hom hm x
  subst r
  calc
    _ = (restrictAcross f).comp (restrictOfEmbeddingAcross c τ.toRingHom hc) :=
      (restrictOfEmbeddingAcross_comp c τ.toRingHom hc (separableMap f) (separableClosureLift f)
        (separableMap_commutes f)).symm
    _ = _ := by rw [hid, AddMonoidHom.comp_id]

/-- The actual restrictions compose across independent universe levels. -/
theorem restrictAcross_comp (f : K →+* L) (g : L →+* M) :
    (restrictAcross g).comp (restrictAcross f) = restrictAcross (g.comp f) := by
  let r := separableMap f
  let s := separableMap g
  let a := separableClosureLift f
  let b := separableClosureLift g
  let h := separableMap_commutes f
  let k := separableMap_commutes g
  have hbase (x : K) : (b.comp a) (algebraMap K (SeparableClosure K) x) =
      algebraMap M (SeparableClosure M) ((g.comp f) x) := by
    change separableClosureLift g (separableClosureLift f (algebraMap K (SeparableClosure K) x)) = _
    rw [separableClosureLift_algebraMap, separableClosureLift_algebraMap]
    rfl
  exact (restrictOfEmbeddingAcross_comp r a h s b k).trans
    (restrictOfEmbeddingAcross_eq_of_extends (g.comp f) (r.comp s) (b.comp a) hbase
      (fun σ x => (congrArg b (h (s σ) x)).trans (k σ (a x))))

/-- A field isomorphism gives an injective restriction across universes. -/
theorem restrictAcross_injective_of_ringEquiv (e : K ≃+* L) :
    Function.Injective (restrictAcross e.toRingHom) := by
  have h := restrictAcross_comp e.toRingHom e.symm.toRingHom
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id K := RingHom.ext e.symm_apply_apply
  rw [he, restrictAcross_same, restrict_id] at h
  exact Function.LeftInverse.injective (fun x => DFunLike.congr_fun h x)

end ClassFieldTheory.Brauer
