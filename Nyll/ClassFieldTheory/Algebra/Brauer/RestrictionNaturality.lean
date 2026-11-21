/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.Algebra.NormalEmbeddingRange

/-! # Functoriality of the actual cohomological Brauer restriction -/

@[expose] public section

noncomputable section

open CategoryTheory ContRepresentation

namespace ClassFieldTheory.Brauer

universe u

open Field.absoluteGaloisGroup

variable {K L M : Type u} [Field K] [Field L] [Field M]

/-- Any actual extension of the same base embedding induces the same Brauer restriction. -/
theorem restrictOfEmbedding_eq_of_extends (f : K →+* L)
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (a : SeparableClosure K →+* SeparableClosure L)
    (ha : ∀ x : K, a (algebraMap K (SeparableClosure K) x) =
      algebraMap L (SeparableClosure L) (f x))
    (h : ∀ (σ : Gal(SeparableClosure L/L)) (x : SeparableClosure K), a (r σ x) = σ (a x)) :
    restrictOfEmbedding r a h = restrict f := by
  let Ω := SeparableClosure L
  let : Algebra K Ω := ((algebraMap L Ω).comp f).toAlgebra
  let i : SeparableClosure K →ₐ[K] Ω := { __ := a, commutes' := ha }
  let j : SeparableClosure K →ₐ[K] Ω :=
    { __ := separableClosureLift f, commutes' := separableClosureLift_algebraMap f }
  obtain ⟨τ, hτ⟩ := ClassFieldTheory.exists_embedding_comp_aut_eq_of_normal i j
  have hcomp : (separableClosureLift f).comp τ.toRingHom = a := RingHom.ext hτ
  subst a
  have hm := relativeCohomologyMap_comp_aut τ (separableClosureLift f) (separableMap f) r
    (separableMap_commutes f) h
  apply AddMonoidHom.ext
  intro x
  exact ConcreteCategory.congr_hom hm x

private theorem composedEmbedding_commutes
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (s : Gal(SeparableClosure M/M) →ₜ* Gal(SeparableClosure L/L))
    (a : SeparableClosure K →+* SeparableClosure L) (b : SeparableClosure L →+* SeparableClosure M)
    (ha : ∀ (σ : Gal(SeparableClosure L/L)) x, a (r σ x) = σ (a x))
    (hb : ∀ (σ : Gal(SeparableClosure M/M)) x, b (s σ x) = σ (b x))
    (σ : Gal(SeparableClosure M/M)) (x : SeparableClosure K) :
    (b.comp a) ((r.comp s) σ x) = σ ((b.comp a) x) :=
  (congrArg b (ha (s σ) x)).trans (hb σ (a x))

private theorem restrictOfEmbedding_comp_apply
    (r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K))
    (s : Gal(SeparableClosure M/M) →ₜ* Gal(SeparableClosure L/L))
    (a : SeparableClosure K →+* SeparableClosure L) (b : SeparableClosure L →+* SeparableClosure M)
    (ha : ∀ (σ : Gal(SeparableClosure L/L)) x, a (r σ x) = σ (a x))
    (hb : ∀ (σ : Gal(SeparableClosure M/M)) x, b (s σ x) = σ (b x)) (x : Br K) :
    restrictOfEmbedding s b hb (restrictOfEmbedding r a ha x) =
      restrictOfEmbedding (r.comp s) (b.comp a) (composedEmbedding_commutes r s a b ha hb) x := by
  let α := galoisUnitsMap r a ha
  let β := galoisUnitsMap s b hb
  let γ := galoisUnitsMap (r.comp s) (b.comp a) (composedEmbedding_commutes r s a b ha hb)
  have hmap := galoisUnitsCohomologyMap_comp r s (r.comp s) a b (b.comp a) ha hb
    (composedEmbedding_commutes r s a b ha hb) (fun _ => rfl) (fun _ => rfl)
  change ContinuousCohomology.map s β 2 (ContinuousCohomology.map r α 2 x) =
    ContinuousCohomology.map (r.comp s) γ 2 x
  exact (ConcreteCategory.congr_hom hmap x).symm

/-- Restriction for the two original field maps agrees with restriction for their composite. -/
theorem restrict_comp (f : K →+* L) (g : L →+* M) :
    (restrict g).comp (restrict f) = restrict (g.comp f) := by
  let r := separableMap f
  let s := separableMap g
  let a := separableClosureLift f
  let b := separableClosureLift g
  let ha := separableMap_commutes f
  let hb := separableMap_commutes g
  have hbase (x : K) :
      (b.comp a) (algebraMap K (SeparableClosure K) x) =
        algebraMap M (SeparableClosure M) ((g.comp f) x) := by
    change separableClosureLift g (separableClosureLift f (algebraMap K (SeparableClosure K) x)) = _
    rw [separableClosureLift_algebraMap, separableClosureLift_algebraMap]
    rfl
  have hcomp := restrictOfEmbedding_eq_of_extends (g.comp f) (r.comp s) (b.comp a) hbase
    (composedEmbedding_commutes r s a b ha hb)
  apply AddMonoidHom.ext
  intro x
  exact (restrictOfEmbedding_comp_apply r s a b ha hb x).trans (DFunLike.congr_fun hcomp x)

/-- Restriction along the identity field map retains the original class. -/
theorem restrict_id : restrict (RingHom.id K) = AddMonoidHom.id (Br K) := by
  let r := ContinuousMonoidHom.id Gal(SeparableClosure K/K)
  let a := RingHom.id (SeparableClosure K)
  let h (σ : Gal(SeparableClosure K/K)) (x : SeparableClosure K) : a (r σ x) = σ (a x) := rfl
  have he := restrictOfEmbedding_eq_of_extends (RingHom.id K) r a (fun _ => rfl) h
  have hφ : galoisUnitsMap r a h = 𝟙 (unitsRep K) := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  rw [← he]
  apply AddMonoidHom.ext
  intro x
  change ContinuousCohomology.map r (galoisUnitsMap r a h) 2 x = x
  rw [hφ, ContinuousCohomology.map_id, ConcreteCategory.id_apply]

/-- Restriction along a field isomorphism has the original inverse restriction. -/
def restrictEquiv (e : K ≃+* L) : Br K ≃+ Br L := by
  refine
    { toFun := restrict e.toRingHom
      invFun := restrict e.symm.toRingHom
      left_inv := ?_
      right_inv := ?_
      map_add' := map_add (restrict e.toRingHom) }
  · intro x
    have h := restrict_comp e.toRingHom e.symm.toRingHom
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id K := RingHom.ext e.symm_apply_apply
    rw [he, restrict_id] at h
    exact DFunLike.congr_fun h x
  · intro x
    have h := restrict_comp e.symm.toRingHom e.toRingHom
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id L := RingHom.ext e.apply_symm_apply
    rw [he, restrict_id] at h
    exact DFunLike.congr_fun h x

/-- Restriction along an actual field isomorphism is injective. -/
theorem restrict_injective_of_ringEquiv (e : K ≃+* L) :
    Function.Injective (restrict e.toRingHom) := by
  exact (restrictEquiv e).injective

end ClassFieldTheory.Brauer
