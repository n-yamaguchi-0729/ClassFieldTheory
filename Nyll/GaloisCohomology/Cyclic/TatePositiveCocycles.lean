/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import Nyll.GaloisCohomology.Cyclic.TateFixedCycles

/-!
# The same cocycle in ordinary and positive Tate cohomology

The positive comparison takes the class of a Tate cocycle to the class of
the identical inhomogeneous cochain. Its construction uses the original
comparison of the ordinary complex with the restricted Tate complex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex
open groupCohomology (inhomogeneousCochains)

namespace TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The ordinary cocycle, regarded in the same degree of the actual Tate complex. -/
def ofOrdinaryCocycle (A : Rep.{u} R G) (n : ℕ) (z : groupCohomology.cocycles A n) :
    (tateComplex A).cycles n :=
  (tateComplex A).cyclesMk (groupCohomology.iCocycles A n z) ((n : ℤ) + 1)
    ((ComplexShape.up ℤ).next_eq' rfl) (by
    change (inhomogeneousCochains A).d n (n + 1) (groupCohomology.iCocycles A n z) = 0
    exact ConcreteCategory.congr_hom ((inhomogeneousCochains A).iCycles_d n (n + 1)) z)

/-- The cycle inclusion in the Tate complex reads the unchanged original cochain. -/
theorem iCycles_ofOrdinaryCocycle (A : Rep.{u} R G) (n : ℕ) (z : groupCohomology.cocycles A n) :
    (tateComplex A).iCycles n (ofOrdinaryCocycle A n z) = groupCohomology.iCocycles A n z := by
  let K := tateComplex A
  let x : K.X (n : ℤ) := groupCohomology.iCocycles A n z
  have hx : K.d (n : ℤ) ((n : ℤ) + 1) x = 0 :=
    ConcreteCategory.congr_hom ((inhomogeneousCochains A).iCycles_d n (n + 1)) z
  exact K.i_cyclesMk (i := (n : ℤ)) x ((n : ℤ) + 1) ((ComplexShape.up ℤ).next_eq' rfl) hx

/-- In positive degree the comparison evaluates on the same ordinary representative. -/
theorem isoGroupCohomology_hom_ofOrdinaryCocycle (A : Rep.{u} R G) (n : ℕ) [NeZero n]
    (z : groupCohomology.cocycles A n) :
    ((isoGroupCohomology n).app A).hom ((tateComplex A).homologyπ n (ofOrdinaryCocycle A n z)) =
      groupCohomology.π A n z := by
  let D := tateComplexConnectData A
  let K := D.cochainComplex
  let L := inhomogeneousCochains A
  let e := ComplexShape.embeddingUpIntGE 0
  have hn : e.f n = (n : ℤ) := by change 0 + (n : ℤ) = n; exact zero_add _
  have hn' : e.f (n + 1) = (n : ℤ) + 1 := by
    change (0 : ℤ) + ((n + 1 : ℕ) : ℤ) = _
    rw [zero_add, Nat.cast_add, Nat.cast_one]
  let c := K.restrictionCyclesIso e n (n + 1) ((ComplexShape.up ℕ).next_eq' rfl) hn hn'
    ((ComplexShape.up ℤ).next_eq' rfl)
  let i := K.restrictionXIso e hn
  let f := D.restrictionGEIso.hom
  let x : K.cycles (n : ℤ) := ofOrdinaryCocycle A n z
  change (K.homologyπ (n : ℤ) ≫ (D.homologyIsoPos n n rfl).hom) x = L.homologyπ n z
  have hπ : K.homologyπ (n : ℤ) ≫ (D.homologyIsoPos n n rfl).hom =
      c.inv ≫ HomologicalComplex.cyclesMap f n ≫ L.homologyπ n := by
    unfold CochainComplex.ConnectData.homologyIsoPos
    rw [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.homologyπ_restrictionHomologyIso_inv_assoc,
      HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyπ_naturality]
  rw [hπ, ModuleCat.comp_apply, ModuleCat.comp_apply]
  apply congrArg (L.homologyπ n)
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).mp inferInstance
  have hi : c.inv ≫ HomologicalComplex.cyclesMap f n ≫ L.iCycles n =
      K.iCycles (n : ℤ) ≫ i.inv ≫ i.hom := by
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.restrictionCyclesIso_inv_iCycles_assoc,
      show f.f n = i.hom by rfl]
    rfl
  change (c.inv ≫ HomologicalComplex.cyclesMap f n ≫ L.iCycles n) x = L.iCycles n z
  rw [hi, i.inv_hom_id, Category.comp_id]
  exact iCycles_ofOrdinaryCocycle A n z

/-- Starting from the same ordinary cocycle in a nonnegative degree, the
actual Tate and ordinary boundaries give the same class in the next degree. -/
theorem δ_ofOrdinaryCocycle {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact) (n : ℕ)
    (z : groupCohomology.cocycles S.X₃ n) :
    ((isoGroupCohomology (n + 1)).app S.X₁).hom
        (δ hS (n : ℤ) ((tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z))) =
      groupCohomology.δ hS n (n + 1) rfl (groupCohomology.π S.X₃ n z) := by
  let Q := S.map (groupCohomology.cochainsFunctor R G)
  let v := groupCohomology.iCocycles S.X₃ n z
  have hv : Q.X₃.d n (n + 1) v = 0 := by
    change (Q.X₃.iCycles n ≫ Q.X₃.d n (n + 1)) z = 0
    exact ConcreteCategory.congr_hom (Q.X₃.iCycles_d n (n + 1)) z
  have hn := (groupCohomology.map_cochainsFunctor_eval_shortExact hS n).epi_g
  change Epi (Q.g.f n) at hn
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (Q.g.f n)).mp hn v
  have hd : Q.g.f (n + 1) (Q.X₂.d n (n + 1) y) = 0 := by
    change (Q.X₂.d n (n + 1) ≫ Q.g.f (n + 1)) y = 0
    rw [← Q.g.comm, ModuleCat.comp_apply, hy, hv]
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (groupCohomology.map_cochainsFunctor_eval_shortExact hS (n + 1)).exact _ hd
  have hx' : S.f.hom ∘ x = Q.X₂.d n (n + 1) y := hx
  let w := groupCohomology.cocyclesMkOfCompEqD hS hx'
  have hw : Q.X₁.iCycles (n + 1) w = x := groupCohomology.iCocycles_mk _ _
  have hv' : inhomogeneousCochains.d S.X₃ n v = 0 := by
    change (inhomogeneousCochains S.X₃).d n (n + 1) v = 0 at hv
    simpa only [CochainComplex.of.d] using! hv
  have hz : groupCohomology.cocyclesMk v hv' = z := by
    apply (ModuleCat.mono_iff_injective (Q.X₃.iCycles n)).mp inferInstance
    exact groupCohomology.iCocycles_mk _ _
  have hordinary := groupCohomology.δ_apply hS rfl v hv y hy x hx'
  change groupCohomology.δ hS n (n + 1) rfl
      (groupCohomology.π S.X₃ n (groupCohomology.cocyclesMk v hv')) =
    groupCohomology.π S.X₁ (n + 1) w at hordinary
  rw [hz] at hordinary
  let Q' := S.map (tateComplexFunctor R G)
  let hQ' : Q'.ShortExact := map_tateComplexFunctor_shortExact hS
  let v₀ : Q'.X₃.X (n : ℤ) := v
  let y₀ : Q'.X₂.X (n : ℤ) := y
  let x₀ : Q'.X₁.X ((n : ℤ) + 1) := x
  have hnext : (ComplexShape.up ℤ).next ((n : ℤ) + 1) = (n : ℤ) + 1 + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have htate := hQ'.δ_apply (n : ℤ) (n + 1) rfl v₀ hv y₀ hy x₀ hx ((n : ℤ) + 1 + 1) hnext
  let w₀ : Q'.X₁.cycles ((n : ℤ) + 1) := ofOrdinaryCocycle S.X₁ (n + 1) w
  have hw₀ : Q'.X₁.iCycles ((n : ℤ) + 1) w₀ = x₀ := (iCycles_ofOrdinaryCocycle _ _ w).trans hw
  have hx₀ : Q'.X₁.d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) x₀ = 0 :=
    (congrArg (Q'.X₁.d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1)) hw₀.symm).trans
      (ConcreteCategory.congr_hom (Q'.X₁.iCycles_d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1)) w₀)
  let b : Q'.X₁.cycles ((n : ℤ) + 1) := Q'.X₁.cyclesMk x₀ ((n : ℤ) + 1 + 1) hnext hx₀
  change δ hS (n : ℤ) ((tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z)) =
    Q'.X₁.homologyπ ((n : ℤ) + 1) b at htate
  have hb : b = ofOrdinaryCocycle S.X₁ (n + 1) w := by
    apply (ModuleCat.mono_iff_injective (Q'.X₁.iCycles ((n : ℤ) + 1))).mp inferInstance
    have hb₀ : Q'.X₁.iCycles ((n : ℤ) + 1) b = x₀ := Q'.X₁.i_cyclesMk _ _ hnext _
    exact hb₀.trans hw₀.symm
  have hbπ := congrArg (fun b' : Q'.X₁.cycles ((n : ℤ) + 1) => Q'.X₁.homologyπ ((n : ℤ) + 1) b') hb
  exact (congrArg ((isoGroupCohomology (n + 1)).app S.X₁).hom (htate.trans hbπ)).trans
    ((isoGroupCohomology_hom_ofOrdinaryCocycle S.X₁ (n + 1) w).trans hordinary.symm)

/-- The original positive Tate comparison commutes with the original ordinary boundary. -/
theorem δ_comp_isoGroupCohomology {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (n : ℕ) [NeZero n] :
    δ hS (n : ℤ) ≫ ((isoGroupCohomology (n + 1)).app S.X₁).hom =
      ((isoGroupCohomology n).app S.X₃).hom ≫ groupCohomology.δ hS n (n + 1) rfl := by
  let e := (isoGroupCohomology n).app S.X₃
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hπ : Epi (groupCohomology.π S.X₃ n) :=
    (inferInstance : Epi ((inhomogeneousCochains S.X₃).homologyπ n))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.π S.X₃ n)).mp
    hπ (e.hom x)
  have hx : x = (tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z) := by
    apply e.toLinearEquiv.injective
    change e.hom x = e.hom ((tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z))
    rw [isoGroupCohomology_hom_ofOrdinaryCocycle, hz]
  rw [hx]
  change ((isoGroupCohomology (n + 1)).app S.X₁).hom
      (δ hS (n : ℤ) ((tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z))) =
    groupCohomology.δ hS n (n + 1) rfl
      (e.hom ((tateComplex S.X₃).homologyπ n (ofOrdinaryCocycle S.X₃ n z)))
  rw [isoGroupCohomology_hom_ofOrdinaryCocycle, δ_ofOrdinaryCocycle]

/-- At degree zero the ordinary fixed vector and its norm-quotient class
give the same boundary in the respective degree-one cohomologies. -/
theorem δ_zero_fixedClass {S : ShortComplex (Rep.{u} R G)} (hS : S.ShortExact)
    (a : S.X₃.ρ.invariants) :
    ((isoGroupCohomology 1).app S.X₁).hom (δ hS 0 (fixedClass S.X₃ a)) =
      groupCohomology.δ hS 0 1 rfl ((groupCohomology.H0Iso S.X₃).inv a) := by
  let z := (groupCohomology.cocyclesIso₀ S.X₃).inv a
  have hz : groupCohomology.π S.X₃ 0 z = (groupCohomology.H0Iso S.X₃).inv a := by
    apply (groupCohomology.H0Iso S.X₃).toLinearEquiv.injective
    change (groupCohomology.π S.X₃ 0 ≫ (groupCohomology.H0Iso S.X₃).hom) z =
      (groupCohomology.H0Iso S.X₃).hom ((groupCohomology.H0Iso S.X₃).inv a)
    rw [groupCohomology.π_comp_H0Iso_hom, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  have hc : ofOrdinaryCocycle S.X₃ 0 z = fixedCycle S.X₃ a := by
    apply (ModuleCat.mono_iff_injective ((tateComplex S.X₃).iCycles 0)).mp inferInstance
    have hcochain : groupCohomology.iCocycles S.X₃ 0 z =
        (groupCohomology.cochainsIso₀ S.X₃).inv a := by
      change ((groupCohomology.cocyclesIso₀ S.X₃).inv ≫ groupCohomology.iCocycles S.X₃ 0) a = _
      rw [groupCohomology.cocyclesIso₀_inv_comp_iCocycles]
      rfl
    exact (iCycles_ofOrdinaryCocycle S.X₃ 0 z).trans
      (hcochain.trans (fixedCycle_iCycles S.X₃ a).symm)
  rw [← hz, fixedClass, ← hc]
  exact δ_ofOrdinaryCocycle hS 0 z

end TateCohomology
