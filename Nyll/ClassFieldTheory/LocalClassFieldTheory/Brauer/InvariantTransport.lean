/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.AbelianGaloisEquiv
public import Nyll.ClassFieldTheory.Algebra.Brauer.RestrictionNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MathlibAbsoluteGaloisBaseEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.IntegralClassBaseChange

/-! # Transport of the arithmetic Brauer invariant under local field equivalences -/

@[expose] public section

noncomputable section

open ClassFieldTower.Cohomology LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open RamificationTheory.Field.absoluteGaloisGroup
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

variable {K L : Type u} [Field K] [Field L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

section Transport

variable (e : K ≃+* L) (j : SeparableClosure K ≃+* SeparableClosure L)
    (hj : ∀ a : K, j (algebraMap K (SeparableClosure K) a) =
      algebraMap L (SeparableClosure L) (e a))

include hj

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem exists_semilinearAbelianStage
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsAbelianGalois K E] :
    ∃ (F : FiniteGaloisIntermediateField L (SeparableClosure L)) (b : E ≃+* F),
      IsAbelianGalois L F ∧
      (∀ z : K, b (algebraMap K E z) = algebraMap L F (e z)) ∧
      (∀ z : E, F.toIntermediateField.val (b z) = j (E.toIntermediateField.val z)) := by
  let hj' := semilinear_symm_algebraMap e j hj
  let T := semilinearRingEquivPreimageIntermediateField e.symm j.symm hj' E.toIntermediateField
  let b : E ≃+* T :=
    { toFun := fun z => ⟨j z.1,
        semilinearRingEquivPreimageIntermediateField_symm_mem e.symm j.symm hj' _ z.2⟩
      invFun := fun z => ⟨j.symm z.1, z.2⟩
      left_inv := fun z => Subtype.ext (j.symm_apply_apply z.1)
      right_inv := fun z => Subtype.ext (j.apply_symm_apply z.1)
      map_mul' := fun z w => Subtype.ext (map_mul j z.1 w.1)
      map_add' := fun z w => Subtype.ext (map_add j z.1 w.1) }
  have hb (z : K) : b (algebraMap K E z) = algebraMap L T (e z) := Subtype.ext (hj z)
  let : FiniteDimensional L T := finiteDimensional_semilinearRingEquivPreimageIntermediateField
    e.symm j.symm hj' E.toIntermediateField
  let : IsAbelianGalois L T := isAbelianGalois_of_equiv_equiv e b (RingHom.ext fun z => (hb z).symm)
  let F : FiniteGaloisIntermediateField L (SeparableClosure L) := { toIntermediateField := T }
  refine ⟨F, b, inferInstanceAs (IsAbelianGalois L T), hb, ?_⟩
  intro z
  rfl

private theorem localBrauerInvariant_cyclic_ringEquiv
    (hv : SemilinearValuationCompatible K L e)
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (F : FiniteGaloisIntermediateField L (SeparableClosure L))
    [IsAbelianGalois K E] [IsAbelianGalois L F] [IsCyclic Gal(E/K)]
    (b : E ≃+* F) (hb : ∀ z : K, b (algebraMap K E z) = algebraMap L F (e z))
    (hclosure : ∀ z : E, F.toIntermediateField.val (b z) = j (E.toIntermediateField.val z))
    (g : Gal(E/K)) (hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g) (a : Kˣ) :
    localBrauerInvariant L (restrict e.toRingHom (cyclicBrauerClass E g hg a)) =
      localBrauerInvariant K (cyclicBrauerClass E g hg a) := by
  let r : Gal(SeparableClosure L/L) →ₜ* Gal(SeparableClosure K/K) :=
    (semilinearGaloisContinuousEquiv e j hj).symm
  have hr (σ : Gal(SeparableClosure L/L)) (a : SeparableClosure K) : j (r σ a) = σ (j a) :=
    j.apply_symm_apply _
  have hrestrict := restrictOfEmbedding_eq_of_extends e.toRingHom r j.toRingHom hj hr
  let s := semilinearGaloisGroupCongr K L E F e b hb
  let h := s g
  have hh (σ : Gal(F/L)) : σ ∈ Subgroup.zpowers h := by
    obtain ⟨n, hn⟩ := hg (s.symm σ)
    refine ⟨n, s.symm.injective ?_⟩
    rw [map_zpow, show s.symm h = g from s.symm_apply_apply g]
    exact hn
  let : IsCyclic Gal(F/L) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨h, (Subgroup.eq_top_iff' _).2 hh⟩
  have hgroup (σ : Gal(SeparableClosure L/L)) :
      finiteGaloisRestriction E (r σ) = s.symm (finiteGaloisRestriction F σ) := by
    apply s.injective
    rw [s.apply_symm_apply]
    apply AlgEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := b.surjective z
    change semilinearGaloisGroupCongr K L E F e b hb
      (finiteGaloisRestriction E (r σ)) (b w) = finiteGaloisRestriction F σ (b w)
    rw [semilinearGaloisGroupCongr_apply_equiv]
    apply Subtype.ext
    change F.toIntermediateField.val (b (finiteGaloisRestriction E (r σ) w)) =
      F.toIntermediateField.val (finiteGaloisRestriction F σ (b w))
    calc
      _ = j (E.toIntermediateField.val (finiteGaloisRestriction E (r σ) w)) := hclosure _
      _ = j (r σ (E.toIntermediateField.val w)) :=
        congrArg j (finiteGaloisRestriction_commutes E (r σ) w)
      _ = σ (j (E.toIntermediateField.val w)) := hr σ w.1
      _ = σ (F.toIntermediateField.val (b w)) := congrArg σ (hclosure w).symm
      _ = _ := (finiteGaloisRestriction_commutes F σ (b w)).symm
  have hcarry : integralRestriction r
        (integralRestriction (finiteGaloisRestriction E) (finiteIntegralCarry g hg)) =
      integralRestriction (finiteGaloisRestriction F) (finiteIntegralCarry h hh) := by
    rw [integralRestriction_comp_apply]
    exact integralRestriction_finiteIntegralCarry_factors g hg h hh _ _ s.symm
      (s.symm_apply_apply g) hgroup
  let aL := Units.map e.toMonoidHom a
  have htransport : restrict e.toRingHom (cyclicBrauerClass E g hg a) =
      cyclicBrauerClass F h hh aL := by
    rw [← hrestrict, cyclicBrauerClass_eq_unitsIntegralClass,
      cyclicBrauerClass_eq_unitsIntegralClass,
      restrictOfEmbedding_unitsIntegralClass e.toRingHom r j.toRingHom hj hr, hcarry]
  have hArtin : s (LocalClassFieldTheory.abelianLocalArtinMap K E a) =
      LocalClassFieldTheory.abelianLocalArtinMap L F aL := by
    have hK : LocalClassFieldTheory.abelianLocalArtinMap K E a =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom K E a :=
      DFunLike.congr_fun (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom K E) a
    have hL : LocalClassFieldTheory.abelianLocalArtinMap L F aL =
        LocalClassFieldTheory.abelianLocalArtinMonoidHom L F aL :=
      DFunLike.congr_fun (LocalClassFieldTheory.abelianLocalArtinMap_toMonoidHom L F) aL
    exact (congrArg s hK).trans
      ((LocalClassFieldTheory.abelianLocalArtinMonoidHom_semilinear_conjugation_apply
        K L E F e b hb hv a).trans hL.symm)
  rw [htransport, localBrauerInvariant_cyclicBrauerClass_eq_artin,
    localBrauerInvariant_cyclicBrauerClass_eq_artin, ← hArtin, ← map_inv]
  exact finiteCyclicArithmeticCharacter_map_of_generator_power h hh g hg s.toMonoidHom 1
    (by decide) (by rw [one_mul]; exact Nat.card_congr s.symm.toEquiv) (by rw [pow_one]; rfl) _

end Transport

/-- The canonical invariant is preserved by a valuation-compatible field equivalence.
At a finite cyclic stage this is the conjugation formula for the arithmetic Artin symbol. -/
theorem localBrauerInvariant_ringEquiv (e : K ≃+* L) (hv : SemilinearValuationCompatible K L e)
    (j : SeparableClosure K ≃+* SeparableClosure L)
    (hj : ∀ a : K, j (algebraMap K (SeparableClosure K) a) =
      algebraMap L (SeparableClosure L) (e a)) (x : Br K) :
    localBrauerInvariant L (restrict e.toRingHom x) = localBrauerInvariant K x := by
  have hx : x ∈ unramifiedBr K := (unramifiedBr_eq_top K).symm ▸ AddSubgroup.mem_top x
  obtain ⟨d, y, hxy⟩ := (mem_unramifiedBr_iff K x).mp hx
  let E := unramifiedBrauerStage K d
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E := localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] := localCompleteDVF_integerRing_moduleFinite K E
  let : IsCyclic Gal(E/K) := isCyclic_galoisGroup_of_unramifiedValuation K E
  let : IsAbelianGalois K E := IsAbelianGalois.of_isCyclic K E
  obtain ⟨g, hgen⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Gal(E/K))
  have hg : ∀ σ : Gal(E/K), σ ∈ Subgroup.zpowers g := (Subgroup.eq_top_iff' _).1 hgen
  obtain ⟨a, ha⟩ := cyclicUnitClass_surjective K E g hg (continuousRelativeUnitsH2Equiv K E y)
  have hclass : cyclicBrauerClass E g hg a.toMul = x := by
    change finiteInflation E ((continuousRelativeUnitsH2Equiv K E).symm
      (cyclicUnitClass K E g hg a)) = x
    rw [ha, AddEquiv.symm_apply_apply]
    exact hxy
  obtain ⟨F, b, hF, hb, hclosure⟩ := exists_semilinearAbelianStage e j hj E
  let : IsAbelianGalois L F := hF
  rw [← hclass]
  exact localBrauerInvariant_cyclic_ringEquiv e j hj hv E F b hb hclosure g hg a.toMul

end ClassFieldTheory.Brauer
