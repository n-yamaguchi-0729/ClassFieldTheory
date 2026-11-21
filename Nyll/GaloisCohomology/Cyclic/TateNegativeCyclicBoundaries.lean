/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Nyll.GaloisCohomology.GroupTheory.GroupEquivComplexComparison
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles

/-!
# The two negative Tate boundaries on bar representatives

At degree minus two the original bar differential applies `g⁻¹ − 1` to
the coefficient of `[g]`. From degree minus one to zero the differential
is the original norm. These formulas determine the signs on the actual
connecting maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex groupHomology groupCohomology

namespace TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The Tate cycle of the original bar chain with the given coefficient at `g`. -/
def negTwoSingleCycle (A : Rep.{u} R G) (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) :
    (tateComplex A).cycles (-2) := by
  refine (tateComplex A).cyclesMk ((chainsIso₁ A).inv (Finsupp.single g a)) (-1)
    ((ComplexShape.up ℤ).next_eq' (by decide)) ?_
  change ((chainsIso₁ A).inv ≫ (inhomogeneousChains A).d 1 0) (Finsupp.single g a) = 0
  rw [eq_d₁₀_comp_inv, ModuleCat.comp_apply, d₁₀_single, ha, sub_self, map_zero]

theorem negTwoSingleCycle_iCycles (A : Rep.{u} R G) (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) :
    (tateComplex A).iCycles (-2) (negTwoSingleCycle A g a ha) =
      (chainsIso₁ A).inv (Finsupp.single g a) :=
  (tateComplex A).i_cyclesMk _ (-1) ((ComplexShape.up ℤ).next_eq' (by decide)) _

/-- The original degree-minus-two Tate class of a single bar chain. -/
def negTwoSingleClass (A : Rep.{u} R G) (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) :
    tateCohomology A (-2) :=
  (tateComplex A).homologyπ (-2) (negTwoSingleCycle A g a ha)

/-- The native comparison with first group homology keeps the original bar chain. -/
theorem isoGroupHomology_hom_negTwoSingleClass (A : Rep.{u} R G) (g : G) (a : A)
    (ha : A.ρ g⁻¹ a = a) :
    ((isoGroupHomology (-2) 1 (by decide)).app A).hom (negTwoSingleClass A g a ha) =
      H1π A ⟨Finsupp.single g a, by
        change d₁₀ A (Finsupp.single g a) = 0
        rw [d₁₀_single, ha, sub_self]⟩ := by
  let D := tateComplexConnectData A
  let K := D.cochainComplex
  let L := inhomogeneousChains A
  let e := ComplexShape.embeddingUpIntLE (-1)
  have he : e.f 1 = (-2 : ℤ) := by decide
  let c := K.restrictionCyclesIso e 1 0 ((ComplexShape.down ℕ).next_eq' rfl) he
    (by decide : e.f 0 = (-1 : ℤ)) ((ComplexShape.up ℤ).next_eq' (by decide))
  let i := K.restrictionXIso e he
  let f := D.restrictionLEIso.hom
  let z : cycles₁ A := ⟨Finsupp.single g a, by
    change d₁₀ A (Finsupp.single g a) = 0
    rw [d₁₀_single, ha, sub_self]⟩
  let x : K.cycles (-2) := negTwoSingleCycle A g a ha
  change (K.homologyπ (-2) ≫ (D.homologyIsoNeg 1 (-2) (by decide)).hom) x =
    L.homologyπ 1 ((isoCycles₁ A).inv z)
  have hπ : K.homologyπ (-2) ≫ (D.homologyIsoNeg 1 (-2) (by decide)).hom =
      c.inv ≫ HomologicalComplex.cyclesMap f 1 ≫ L.homologyπ 1 := by
    unfold CochainComplex.ConnectData.homologyIsoNeg
    rw [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc,
      HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyπ_naturality]
  rw [hπ, ModuleCat.comp_apply, ModuleCat.comp_apply]
  apply congrArg (L.homologyπ 1)
  apply (ModuleCat.mono_iff_injective (L.iCycles 1)).mp inferInstance
  have hi : c.inv ≫ HomologicalComplex.cyclesMap f 1 ≫ L.iCycles 1 =
      K.iCycles (-2) ≫ i.inv ≫ i.hom := by
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc,
      show f.f 1 = i.hom by rfl]
    rfl
  change ((c.inv ≫ HomologicalComplex.cyclesMap f 1 ≫ L.iCycles 1) x) =
    ((isoCycles₁ A).inv ≫ iCycles A 1) z
  rw [hi, i.inv_hom_id, Category.comp_id, isoCycles₁_inv_comp_iCycles]
  exact negTwoSingleCycle_iCycles A g a ha

/-- The Tate cycle represented by the actual norm-zero element at degree minus one. -/
def negOneNormCycle (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    (tateComplex A).cycles (-1) := by
  refine (tateComplex A).cyclesMk ((chainsIso₀ A).inv a) 0
    ((ComplexShape.up ℤ).next_eq' (by decide)) ?_
  change ((chainsIso₀ A).inv ≫ A.tateNorm) a = 0
  rw [Rep.tateNorm, Iso.inv_hom_id_assoc, ModuleCat.comp_apply]
  change (cochainsIso₀ A).inv (A.ρ.norm a) = 0
  rw [ha, map_zero]

theorem negOneNormCycle_iCycles (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) :
    (tateComplex A).iCycles (-1) (negOneNormCycle A a ha) = (chainsIso₀ A).inv a :=
  (tateComplex A).i_cyclesMk _ 0 ((ComplexShape.up ℤ).next_eq' (by decide)) _

/-- The actual Tate class of the original norm-zero representative. -/
def negOneNormClass (A : Rep.{u} R G) (a : A) (ha : A.ρ.norm a = 0) : tateCohomology A (-1) :=
  (tateComplex A).homologyπ (-1) (negOneNormCycle A a ha)

private theorem δ_of_cycle_lifts {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (n : ℤ)
    (z : (tateComplex S.X₃).cycles n) (y : (tateComplex S.X₂).X n)
    (x : (tateComplex S.X₁).cycles (n + 1))
    (hy : (tateComplex.map S.g).f n y = (tateComplex S.X₃).iCycles n z)
    (hx : (tateComplex.map S.f).f (n + 1) ((tateComplex S.X₁).iCycles (n + 1) x) =
      (tateComplex S.X₂).d n (n + 1) y) :
    δ hS n ((tateComplex S.X₃).homologyπ n z) = (tateComplex S.X₁).homologyπ (n + 1) x := by
  let Q := S.map (tateComplexFunctor R G)
  let hQ := map_tateComplexFunctor_shortExact hS
  let z₀ := Q.X₃.iCycles n z
  let x₀ := Q.X₁.iCycles (n + 1) x
  have hz₀ : Q.X₃.d n (n + 1) z₀ = 0 := by
    change (Q.X₃.iCycles n ≫ Q.X₃.d n (n + 1)) z = 0
    exact ConcreteCategory.congr_hom (HomologicalComplex.iCycles_d Q.X₃ n (n + 1)) z
  have hj : (ComplexShape.up ℤ).next n = n + 1 := (ComplexShape.up ℤ).next_eq' rfl
  have hk : (ComplexShape.up ℤ).next (n + 1) = n + 1 + 1 := (ComplexShape.up ℤ).next_eq' rfl
  let z' := Q.X₃.cyclesMk z₀ (n + 1) hj hz₀
  let x' := Q.X₁.cyclesMk x₀ (n + 1 + 1) hk (hQ.d_eq_zero_of_f_eq_d_apply n (n + 1) y x₀ hx _)
  have hz' : z' = z := (ModuleCat.mono_iff_injective (Q.X₃.iCycles n)).mp inferInstance
    (Q.X₃.i_cyclesMk _ _ hj hz₀)
  have hx' : x' = x := (ModuleCat.mono_iff_injective (Q.X₁.iCycles (n + 1))).mp inferInstance
    (Q.X₁.i_cyclesMk _ _ hk _)
  have e := hQ.δ_apply n (n + 1) rfl z₀ hz₀ y hy x₀ hx (n + 1 + 1) hk
  change δ hS n (Q.X₃.homologyπ n z') = Q.X₁.homologyπ (n + 1) x' at e
  rw [hz', hx'] at e
  exact e

private theorem map_chainsIso₁_inv_single {A B : Rep.{u} R G} (f : A ⟶ B) (g : G) (a : A) :
    (tateComplex.map f).f (-2) ((chainsIso₁ A).inv (Finsupp.single g a)) =
      (chainsIso₁ B).inv (Finsupp.single g (f a)) := by
  apply (chainsIso₁ B).toLinearEquiv.injective
  change ((chainsMap (MonoidHom.id G) f).f 1 ≫ (chainsIso₁ B).hom)
      ((chainsIso₁ A).inv (Finsupp.single g a)) =
    (chainsIso₁ B).hom ((chainsIso₁ B).inv (Finsupp.single g (f a)))
  rw [chainsMap_f_1_comp_chainsIso₁, ModuleCat.comp_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply]
  simp only [chainsMap₁, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, MonoidHom.id_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  rfl

private theorem map_chainsIso₀_inv {A B : Rep.{u} R G} (f : A ⟶ B) (a : A) :
    (tateComplex.map f).f (-1) ((chainsIso₀ A).inv a) = (chainsIso₀ B).inv (f a) := by
  apply (chainsIso₀ B).toLinearEquiv.injective
  change ((chainsMap (MonoidHom.id G) f).f 0 ≫ (chainsIso₀ B).hom) ((chainsIso₀ A).inv a) =
    (chainsIso₀ B).hom ((chainsIso₀ B).inv (f a))
  rw [chainsMap_f_0_comp_chainsIso₀, ModuleCat.comp_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply]
  rfl

private theorem homologyMap_negTwoSingleClass {H : Type u} [Group H] [Fintype H]
    {A : Rep.{u} R G} {B : Rep.{u} R H} (f : tateComplex A ⟶ tateComplex B)
    (g : G) (h : H) (a : A) (b : B) (ha : A.ρ g⁻¹ a = a) (hb : B.ρ h⁻¹ b = b)
    (hf : f.f (-2) ((chainsIso₁ A).inv (Finsupp.single g a)) =
      (chainsIso₁ B).inv (Finsupp.single h b)) :
    HomologicalComplex.homologyMap f (-2) (negTwoSingleClass A g a ha) =
      negTwoSingleClass B h b hb := by
  change ((tateComplex A).homologyπ (-2) ≫ HomologicalComplex.homologyMap f (-2))
      (negTwoSingleCycle A g a ha) = (tateComplex B).homologyπ (-2) (negTwoSingleCycle B h b hb)
  rw [HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  apply congrArg ((tateComplex B).homologyπ (-2))
  apply (ModuleCat.mono_iff_injective ((tateComplex B).iCycles (-2))).mp inferInstance
  change (HomologicalComplex.cyclesMap f (-2) ≫ (tateComplex B).iCycles (-2))
      (negTwoSingleCycle A g a ha) = (tateComplex B).iCycles (-2) (negTwoSingleCycle B h b hb)
  rw [HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, negTwoSingleCycle_iCycles,
    negTwoSingleCycle_iCycles, hf]

/-- The original coefficient map applies to the coefficient of the same single bar chain. -/
theorem map_negTwoSingleClass {A B : Rep.{u} R G} (f : A ⟶ B) (g : G)
    (a : A) (ha : A.ρ g⁻¹ a = a) :
    (tateCohomologyFunctor (-2)).map f (negTwoSingleClass A g a ha) =
      negTwoSingleClass B g (f a) (by rw [← Rep.hom_comm_apply, ha]) :=
  homologyMap_negTwoSingleClass (tateComplex.map f) g g a (f a) ha _
    (map_chainsIso₁_inv_single f g a)

/-- Actual group and coefficient reindexing transport the original bar representative. -/
theorem groupEquivIso_hom_negTwoSingleClass {H : Type u} [Group H] [Fintype H]
    {A : Rep.{u} R G} {B : Rep.{u} R H} (e : G ≃* H) (l : A.V ≃ₗ[R] B.V)
    (hl : ∀ g, l.toLinearMap ∘ₗ A.ρ g = B.ρ (e g) ∘ₗ l.toLinearMap)
    (g : G) (a : A) (ha : A.ρ g⁻¹ a = a) (hb : B.ρ (e g)⁻¹ (l a) = l a) :
    (groupEquivIso e l hl (-2)).hom (negTwoSingleClass A g a ha) =
      negTwoSingleClass B (e g) (l a) hb := by
  apply homologyMap_negTwoSingleClass (groupEquivComplexIso e l hl).hom g (e g) a (l a) ha hb
  let φ : A ⟶ Rep.res e.toMonoidHom B := Rep.ofHom ⟨l.toLinearMap, hl⟩
  apply (chainsIso₁ B).toLinearEquiv.injective
  change ((chainsMap e.toMonoidHom φ).f 1 ≫ (chainsIso₁ B).hom)
      ((chainsIso₁ A).inv (Finsupp.single g a)) =
    (chainsIso₁ B).hom ((chainsIso₁ B).inv (Finsupp.single (e g) (l a)))
  rw [chainsMap_f_1_comp_chainsIso₁, ModuleCat.comp_apply, Iso.inv_hom_id_apply,
    Iso.inv_hom_id_apply]
  simp only [chainsMap₁, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  rfl

/-- Group and coefficient reindexing carry a degree-zero fixed vector to its actual image. -/
theorem groupEquivIso_hom_fixedClass {H : Type u} [Group H] [Fintype H]
    {A : Rep.{u} R G} {B : Rep.{u} R H} (e : G ≃* H) (l : A.V ≃ₗ[R] B.V)
    (hl : ∀ g, l.toLinearMap ∘ₗ A.ρ g = B.ρ (e g) ∘ₗ l.toLinearMap)
    (a : A.ρ.invariants) (b : B.ρ.invariants) (hb : b.val = l a.val) :
    (groupEquivIso e l hl 0).hom (fixedClass A a) = fixedClass B b := by
  let f := (groupEquivComplexIso e l hl).hom
  change ((tateComplex A).homologyπ 0 ≫ HomologicalComplex.homologyMap f 0) (fixedCycle A a) =
    (tateComplex B).homologyπ 0 (fixedCycle B b)
  rw [HomologicalComplex.homologyπ_naturality, ModuleCat.comp_apply]
  apply congrArg ((tateComplex B).homologyπ 0)
  apply (ModuleCat.mono_iff_injective ((tateComplex B).iCycles 0)).mp inferInstance
  change (HomologicalComplex.cyclesMap f 0 ≫ (tateComplex B).iCycles 0) (fixedCycle A a) =
    (tateComplex B).iCycles 0 (fixedCycle B b)
  rw [HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply, fixedCycle_iCycles, fixedCycle_iCycles]
  funext h
  change l a.val = b.val
  exact hb.symm

/-- The boundary of a lifted single bar chain uses the `g⁻¹ − 1` differential. -/
theorem δ_negTwoSingleClass {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (g : G)
    (a : S.X₃) (ha : S.X₃.ρ g⁻¹ a = a) (y : S.X₂) (hy : S.g y = a)
    (x : S.X₁) (hx : S.f x = S.X₂.ρ g⁻¹ y - y) (hn : S.X₁.ρ.norm x = 0) :
    δ hS (-2) (negTwoSingleClass S.X₃ g a ha) = negOneNormClass S.X₁ x hn := by
  apply δ_of_cycle_lifts hS (-2) (negTwoSingleCycle S.X₃ g a ha)
    ((chainsIso₁ S.X₂).inv (Finsupp.single g y)) (negOneNormCycle S.X₁ x hn)
  · rw [map_chainsIso₁_inv_single, hy, negTwoSingleCycle_iCycles]
  · change (tateComplex.map S.f).f (-1)
        ((tateComplex S.X₁).iCycles (-1) (negOneNormCycle S.X₁ x hn)) =
      ((chainsIso₁ S.X₂).inv ≫ (inhomogeneousChains S.X₂).d 1 0) (Finsupp.single g y)
    rw [negOneNormCycle_iCycles, map_chainsIso₀_inv, hx,
      eq_d₁₀_comp_inv, ModuleCat.comp_apply, d₁₀_single]

/-- The boundary at the splice is the norm of a lift of the original representative. -/
theorem δ_negOneNormClass {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (a : S.X₃) (ha : S.X₃.ρ.norm a = 0) (y : S.X₂) (hy : S.g y = a)
    (x : S.X₁.ρ.invariants) (hx : S.f x.val = S.X₂.ρ.norm y) :
    δ hS (-1) (negOneNormClass S.X₃ a ha) = fixedClass S.X₁ x := by
  apply δ_of_cycle_lifts hS (-1) (negOneNormCycle S.X₃ a ha)
    ((chainsIso₀ S.X₂).inv y) (fixedCycle S.X₁ x)
  · rw [map_chainsIso₀_inv, hy, negOneNormCycle_iCycles]
  · change (tateComplex.map S.f).f 0 ((tateComplex S.X₁).iCycles 0 (fixedCycle S.X₁ x)) =
      S.X₂.tateNorm ((chainsIso₀ S.X₂).inv y)
    rw [fixedCycle_iCycles]
    apply (cochainsIso₀ S.X₂).toLinearEquiv.injective
    change ((cochainsMap (MonoidHom.id G) S.f).f 0 ≫ (cochainsIso₀ S.X₂).hom)
        ((cochainsIso₀ S.X₁).inv x.val) =
      (cochainsIso₀ S.X₂).hom (S.X₂.tateNorm ((chainsIso₀ S.X₂).inv y))
    rw [cochainsMap_f_0_comp_cochainsIso₀, ModuleCat.comp_apply, Iso.inv_hom_id_apply,
      Rep.tateNorm, ModuleCat.comp_apply, Iso.inv_hom_id_apply,
      ModuleCat.comp_apply, Iso.inv_hom_id_apply]
    exact hx

end TateCohomology
