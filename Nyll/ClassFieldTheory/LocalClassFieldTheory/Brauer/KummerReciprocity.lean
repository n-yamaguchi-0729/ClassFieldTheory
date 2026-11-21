/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicReciprocity
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.KummerTrace
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalTatePairing
public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Nyll.GaloisCohomology.Topology.ContinuousCupLow

/-! # The cyclic character cup with the actual Kummer class -/

@[expose] public section

noncomputable section

open CategoryTheory ClassFieldTower.Cohomology ContinuousCohomology TopRep
open LocalClassFieldTheory LocalFieldTheory
open scoped Topology ValuativeRel

namespace ClassFieldTheory.Brauer

attribute [local instance] separableAbsoluteGalois_locallyCompact

universe u

private theorem restrictedCarry_evaluate
    {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [Fintype G]
    (r : H →ₜ* G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (z : cocycles (trivialIntegralTopRep G) 2)
    (hz : ∀ a b c : G, ((homogeneousCochains (trivialIntegralTopRep G)).iCycles 2 z).val a b c =
      ULift.up (finiteCyclicCarry g hg (a⁻¹ * b) (b⁻¹ * c) : ℤ)) (s t : H) :
    ((homogeneousCochains (trivialIntegralTopRep H)).iCycles 2
      (cocyclesMap r (integralRestrictionCoefficient r) 2 z)).val 1 s (s * t) =
        ULift.up (finiteCyclicCarry g hg (r s) (r t) : ℤ) := by
  let φ := integralRestrictionCoefficient r
  have hmap := mappedRelativeCocycle_apply (X := trivialIntegralTopRep G)
    (Y := trivialIntegralTopRep H) r φ z 1 s (s * t)
  have hz' : ((homogeneousCochains (trivialIntegralTopRep G)).iCycles 2 z).val
      (r 1) (r s) (r (s * t)) = ULift.up (finiteCyclicCarry g hg (r s) (r t) : ℤ) := by
    rw [map_one, map_mul]
    simpa only [inv_one, one_mul, inv_mul_cancel_left] using hz 1 (r s) (r s * r t)
  exact hmap.trans (congrArg φ hz')

private theorem exists_continuous_homogeneousOne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : TopRep.{u} ℤ G) (b : G → X) (hb : Continuous b)
    (hAction : Continuous (fun p : G × X => X.ρ p.1 p.2)) :
    ∃ w : (homogeneousCochains X).X 1, ∀ s t : G, w.val s t = X.ρ s (b (s⁻¹ * t)) := by
  have h₀ : Continuous (fun p : Fin 2 → G => p 0) := continuous_apply (0 : Fin 2)
  have h₁ : Continuous (fun p : Fin 2 → G => p 1) := continuous_apply (1 : Fin 2)
  have hargs : Continuous (fun p : Fin 2 → G => (p 0, b ((p 0)⁻¹ * p 1))) :=
    h₀.prodMk (hb.comp (h₀.inv.mul h₁))
  let v : C(Fin 2 → G, X) :=
    ⟨fun p => X.ρ (p 0) (b ((p 0)⁻¹ * p 1)), hAction.comp hargs⟩
  have hv (s : G) (p : Fin 2 → G) : v (fun i => s * p i) = X.ρ s (v p) := by
    change X.ρ (s * p 0) (b ((s * p 0)⁻¹ * (s * p 1))) =
      X.ρ s (X.ρ (p 0) (b ((p 0)⁻¹ * p 1)))
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact DFunLike.congr_fun (map_mul X.ρ s (p 0)) (b ((p 0)⁻¹ * p 1))
  exact ⟨homogeneousCochainOfTuple G X 1 v hv, fun s t =>
    congrArg (fun f : C(Fin 2 → G, X) => f ![s, t]) (homogeneousCochainOfTuple_apply G X 1 v hv)⟩

private theorem continuous_weighted_action
    {G : Type u} [Group G] [TopologicalSpace G]
    (X : TopRep.{u} ℤ G) [DiscreteTopology X]
    (k : G → ℕ) (hk : Continuous k) (x : X)
    (hAction : Continuous (fun a : G × X => X.ρ a.1 a.2)) :
    Continuous (fun s => k s • X.ρ s x) := by
  have hconst : Continuous (fun _ : G => x) := continuous_const
  have hx : Continuous (fun s : G => X.ρ s x) :=
    hAction.comp ((continuous_id : Continuous (id : G → G)).prodMk hconst)
  have hsmul : Continuous (fun p : ℕ × X => p.1 • p.2) := continuous_of_discreteTopology
  exact hsmul.comp (hk.prodMk hx)

private theorem twoCocycles_ext_at_one_mul
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep.{u} ℤ G) (x y : cocycles X 2)
    (h : ∀ s t : G, dehomogenizeIntegralTwo X x (s, t) = dehomogenizeIntegralTwo X y (s, t)) :
    x = y := by
  apply cochain_cocycle_injective X 2
  apply Subtype.ext
  apply ContinuousMap.ext
  intro a
  apply ContinuousMap.ext
  intro b
  apply ContinuousMap.ext
  intro c
  rw [homogeneousIntegralTwo_apply, homogeneousIntegralTwo_apply]
  exact congrArg (X.ρ a) (h (a⁻¹ * b) (b⁻¹ * c))

variable (K : Type u) [Field K]

local notation "Ω" => SeparableClosure K
local notation "G" => Gal(Ω/K)
local notation "U" => unitsRep K
local notation "Z[" n "]" => trivialIntegralZModPLifted n G
local notation "Mu[" n "]" => separableMuTopRep K n

/-- The action of a residue class on the original module of (n)-th roots of unity. -/
def kummerScalarReduction (n : ℕ) : ZMod n →+ (Mu[n] →ₗ[ℤ] Mu[n]) :=
  ZMod.lift n ⟨zmultiplesHom _ LinearMap.id, by
    change (n : ℤ) • (LinearMap.id : Mu[n] →ₗ[ℤ] Mu[n]) = 0
    apply LinearMap.ext
    intro x
    change (n : ℤ) • x = 0
    rw [natCast_zsmul]
    apply Subtype.ext
    exact x.property⟩

/-- The residue of an integer acts by that integer on the actual roots
of unity. This pairing uses their original integral representation. -/
def kummerScalarPairing (n : ℕ) : Z[n] →ₗ[ℤ] Mu[n] →ₗ[ℤ] Mu[n] :=
  ((kummerScalarReduction K n).comp
    (AddEquiv.ulift : ULift.{u} (ZMod n) ≃+ ZMod n).toAddMonoidHom).toIntLinearMap

theorem kummerScalarPairing_intCast (n : ℕ) (m : ℤ) (x : Mu[n]) :
    kummerScalarPairing K n (ULift.up (m : ZMod n)) x = m • x := by
  change kummerScalarReduction K n (m : ZMod n) x = m • x
  rw [kummerScalarReduction, ZMod.lift_coe]
  rfl

theorem kummerScalarPairing_continuous (n : ℕ) :
    Continuous (fun t : Z[n] × Mu[n] => kummerScalarPairing K n t.1 t.2) := by
  let : DiscreteTopology (Z[n]) :=
    inferInstanceAs (DiscreteTopology (ULift.{u} (ZMod n)))
  exact continuous_of_discreteTopology

theorem kummerScalarPairing_equivariant (n : ℕ) (σ : G) (m : Z[n]) (x : Mu[n]) :
    kummerScalarPairing K n ((Z[n]).ρ σ m) ((Mu[n]).ρ σ x) =
      (Mu[n]).ρ σ (kummerScalarPairing K n m x) := by
  change kummerScalarPairing K n m ((Mu[n]).ρ σ x) =
    (Mu[n]).ρ σ (kummerScalarPairing K n m x)
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (show ULift.{u} (ZMod n) from m).down
  have h : m = ULift.up (k : ZMod n) := ULift.ext hk.symm
  rw [h, kummerScalarPairing_intCast, kummerScalarPairing_intCast, map_zsmul]

section CyclicCharacter

variable (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [IsCyclic Gal(E/K)]
  (g : Gal(E/K)) (hg : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers g)

local notation "n" => Nat.card Gal(E/K)

/-- The original finite cyclic character pulled back to the absolute
Galois group, viewed as its continuous degree-one cocycle. -/
def finiteCyclicCharacterCrossedHom : CrossedHom (Z[n]) where
  toFun σ := ULift.up (finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E σ))
  continuous_toFun := by
    let f : Gal(E/K) → ULift.{u} (ZMod n) :=
      fun τ => ULift.up (finiteCyclicGeneratorCoordinate g hg τ)
    have hf : Continuous f := continuous_of_discreteTopology
    exact hf.comp (finiteGaloisRestriction E).continuous
  map_mul σ τ := by
    apply ULift.ext
    change finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E (σ * τ)) =
      finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E σ) +
        finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E τ)
    rw [map_mul, finiteCyclicGeneratorCoordinate_mul]

/-- The actual cup of the cyclic character and the Kummer representative
obtained from a specified root. -/
def cyclicKummerCup (a : Kˣ) (β : U) (hβ : n • β = baseUnitValue K a) :
    continuousCohomology 2 (Mu[n]) :=
  cupOneOne (kummerScalarPairing K n) (kummerScalarPairing_continuous K n)
    (kummerScalarPairing_equivariant K n)
    (π (Z[n]) 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle)
    (π (Mu[n]) 1 (rootKummerCrossedHom K n a β hβ).toCocycle)

private def cyclicKummerUnitCupCocycle (a : Kˣ) (β : U) (hβ : n • β = baseUnitValue K a) :
    cocycles (Mu[n]) 2 :=
  cupOneOneCocycle (kummerScalarPairing K n) (kummerScalarPairing_continuous K n)
    (kummerScalarPairing_equivariant K n)
    (finiteCyclicCharacterCrossedHom K E g hg).toCocycle
    (rootKummerCrossedHom K n a β hβ).toCocycle

private def cyclicKummerUnitCupInUnits (a : Kˣ) (β : U) (hβ : n • β = baseUnitValue K a) :
    cocycles U 2 :=
  let identity := ContinuousMonoidHom.id G
  let μ : TopRep.res identity.toMonoidHom (Mu[n]) ⟶ U := separableMuInclusion K n
  cocyclesMap identity μ 2 (cyclicKummerUnitCupCocycle K E g hg a β hβ)

omit [IsCyclic Gal(E/K)] in
private theorem cyclicKummerUnitCupInUnits_evaluate
    (a : Kˣ) (β : U) (hβ : n • β = baseUnitValue K a) (s t : G) :
    ((homogeneousCochains U).iCycles 2 (cyclicKummerUnitCupInUnits K E g hg a β hβ)).val
        1 s (s * t) =
      (finiteCyclicGeneratorCoordinate g hg (finiteGaloisRestriction E s)).val •
        ((U).ρ (s * t) β - (U).ρ s β) := by
  let r := finiteGaloisRestriction E
  let k (s : G) : ℕ := (finiteCyclicGeneratorCoordinate g hg (r s)).val
  let x := (finiteCyclicCharacterCrossedHom K E g hg).toCocycle
  let y := (rootKummerCrossedHom K n a β hβ).toCocycle
  let q := cyclicKummerUnitCupCocycle K E g hg a β hβ
  let identity := ContinuousMonoidHom.id G
  let μ : TopRep.res identity.toMonoidHom (Mu[n]) ⟶ U := separableMuInclusion K n
  have hx : ((homogeneousCochains (Z[n])).iCycles 1 x).val 1 s =
      ULift.up ((k s : ℤ) : ZMod n) := by
    change ((homogeneousCochains (Z[n])).iCycles 1
      (finiteCyclicCharacterCrossedHom K E g hg).toCocycle).val 1 s = _
    rw [CrossedHom.iCycles_toCocycle, CrossedHom.homogeneous_apply, CrossedHom.map_one, sub_zero]
    apply ULift.ext
    change finiteCyclicGeneratorCoordinate g hg (r s) = ((k s : ℤ) : ZMod n)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hy (j l : G) :
      (((homogeneousCochains (Mu[n])).iCycles 1 y).val j l).val =
        (U).ρ l β - (U).ρ j β := by
    change (((homogeneousCochains (Mu[n])).iCycles 1
      (rootKummerCrossedHom K n a β hβ).toCocycle).val j l).val = _
    rw [CrossedHom.iCycles_toCocycle, CrossedHom.homogeneous_apply]
    change ((U).ρ l β - β) - ((U).ρ j β - β) = _
    abel
  have hμ := mappedRelativeCocycle_apply (X := Mu[n]) (Y := U) identity μ q 1 s (s * t)
  refine hμ.trans ?_
  change (((homogeneousCochains (Mu[n])).iCycles 2
    (cupOneOneCocycle (kummerScalarPairing K n) (kummerScalarPairing_continuous K n)
      (kummerScalarPairing_equivariant K n) x y)).val 1 s (s * t)).val = _
  rw [iCycles_cupOneOneCocycle, cupOneOneCochain_apply, hx, kummerScalarPairing_intCast,
    natCast_zsmul]
  change k s • (((homogeneousCochains (Mu[n])).iCycles 1 y).val s (s * t)).val = _
  rw [hy]

/-- After inclusion into units the original Kummer cup is the cyclic
carry class, by a continuous cochain identity with the chosen root. -/
theorem separableMuH2ToBr_cyclicKummerCup (a : Kˣ) (β : U) (hβ : n • β = baseUnitValue K a) :
    separableMuH2ToBr K n (cyclicKummerCup K E g hg a β hβ) =
      cyclicBrauerClass E g hg a := by
  let r := finiteGaloisRestriction E
  let k (s : G) : ℕ := (finiteCyclicGeneratorCoordinate g hg (r s)).val
  let C := homogeneousCochains U
  let identity := ContinuousMonoidHom.id G
  let cup := cyclicKummerUnitCupInUnits K E g hg a β hβ
  obtain ⟨z, hz, hzc⟩ := exists_finiteIntegralCarry_representative g hg
  let zK := cocyclesMap r (integralRestrictionCoefficient r) 2 z
  let coeff : TopRep.res identity.toMonoidHom (trivialIntegralTopRep G) ⟶ U :=
    unitScalarCoefficientMap K a
  let carry := cocyclesMap identity coeff 2 zK
  have hcup :
      separableMuH2ToBr K n (cyclicKummerCup K E g hg a β hβ) = π U 2 cup := by
    unfold cyclicKummerCup
    rw [cupOneOne_π, separableMuH2ToBr_π]
    rfl
  have hcarry : cyclicBrauerClass E g hg a = π U 2 carry := by
    rw [cyclicBrauerClass_eq_unitsIntegralClass, ← hz, integralRestriction_π,
      unitsIntegralClass_π]
  have hcupVal (s t : G) : (C.iCycles 2 cup).val 1 s (s * t) =
      k s • ((U).ρ (s * t) β - (U).ρ s β) :=
    cyclicKummerUnitCupInUnits_evaluate K E g hg a β hβ s t
  have hcarryVal (s t : G) : (C.iCycles 2 carry).val 1 s (s * t) =
      finiteCyclicCarry g hg (r s) (r t) • baseUnitValue K a := by
    have hcoeff := mappedRelativeCocycle_apply (X := trivialIntegralTopRep G) (Y := U)
      identity coeff zK 1 s (s * t)
    refine hcoeff.trans ?_
    have hvalue := restrictedCarry_evaluate r g hg z hzc s t
    have hm := congrArg (unitScalarCoefficientMap K a) hvalue
    exact (hm.trans (unitScalarCoefficientMap_apply K a
      (ULift.up (finiteCyclicCarry g hg (r s) (r t) : ℤ)))).trans (natCast_zsmul _ _)
  let b (s : G) : U := k s • (U).ρ s β
  have hk : Continuous k :=
    (show Continuous (fun σ : Gal(E/K) => (finiteCyclicGeneratorCoordinate g hg σ).val) from
      continuous_of_discreteTopology).comp r.continuous
  have hAction : Continuous (fun p : G × U => (U).ρ p.1 p.2) :=
    galoisUnitsRep_action_continuous K Ω
  let : DiscreteTopology U := galoisUnitsRep_discrete K Ω
  have hb : Continuous b := continuous_weighted_action U k hk β hAction
  obtain ⟨w, hw⟩ := exists_continuous_homogeneousOne U b hb hAction
  let boundary := C.toCycles 1 2 w
  have hboundary : boundary = carry - cup := by
    apply twoCocycles_ext_at_one_mul U
    intro s t
    rw [map_sub]
    change (C.iCycles 2 boundary).val 1 s (s * t) =
      (C.iCycles 2 carry).val 1 s (s * t) - (C.iCycles 2 cup).val 1 s (s * t)
    rw [hcarryVal, hcupVal]
    have hcochain : C.iCycles 2 boundary = (C.d 1 2).hom w :=
      ConcreteCategory.congr_hom (C.toCycles_i 1 2) w
    refine (congrArg (fun f : C.X 2 => f.val 1 s (s * t)) hcochain).trans
      ((dehomogenizeBoundary_one_apply U w s t).trans ?_)
    change (U).ρ s (w.val 1 t) - w.val 1 (s * t) + w.val 1 s = _
    simp only [hw, inv_one, one_mul, map_one, one_apply_eq_self]
    change (U).ρ s (k t • (U).ρ t β) - k (s * t) • (U).ρ (s * t) β + k s • (U).ρ s β = _
    have hρ := congrArg (fun f : U →L[ℤ] U => f β) (map_mul (U).ρ s t)
    change (U).ρ (s * t) β = (U).ρ s ((U).ρ t β) at hρ
    rw [map_nsmul, ← hρ]
    let c := finiteCyclicCarry g hg (r s) (r t)
    have hNat : n * c + k (s * t) = k s + k t := by
      have h := finiteCyclicCarry_balance g hg (r s) (r t)
      rwa [← map_mul] at h
    have hnorm : n • (U).ρ (s * t) β = baseUnitValue K a := by
      rw [← map_nsmul, hβ, baseUnitValue_invariant]
    have hweight : (n * c) • (U).ρ (s * t) β = c • baseUnitValue K a := by
      rw [mul_nsmul, hnorm]
    have hbal := congrArg (fun m : ℕ => m • (U).ρ (s * t) β) hNat
    simp only [add_nsmul, hweight] at hbal
    have heq := congrArg (fun a : U => a - k (s * t) • (U).ρ (s * t) β) hbal
    rw [add_sub_cancel_right] at heq
    change _ = c • baseUnitValue K a - k s • ((U).ρ (s * t) β - (U).ρ s β)
    calc
      _ = (k s • (U).ρ (s * t) β + k t • (U).ρ (s * t) β) -
          k (s * t) • (U).ρ (s * t) β + k s • (U).ρ s β - k s • (U).ρ (s * t) β := by
        abel
      _ = _ := by
        rw [← heq, nsmul_sub]
        abel
  rw [hcup, hcarry]
  have hx : π U 2 (carry - cup) = 0 := by
    rw [← hboundary]
    exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 1 2) w
  rw [map_sub, sub_eq_zero] at hx
  exact hx.symm

/-- The positive order used for the natural Kummer coefficients of the cyclic extension. -/
abbrev cyclicKummerOrder : ℕ+ := ⟨n, Nat.card_pos⟩

omit [IsCyclic Gal(E/K)] in
private theorem exists_cyclicKummerRoot (a : Kˣ) (hn : (n : K) ≠ 0) :
    ∃ β : U, n • β = baseUnitValue K a :=
  separableUnits_nsmul_surjective K (cyclicKummerOrder K E) hn (baseUnitValue K a)

/-- The same Kummer cup can be evaluated on a unit using the original
separable coefficient connecting morphism. -/
def cyclicKummerCupOfUnit (a : Kˣ) (hn : (n : K) ≠ 0) : continuousCohomology 2 (Mu[n]) :=
  cupOneOne (kummerScalarPairing K n) (kummerScalarPairing_continuous K n)
    (kummerScalarPairing_equivariant K n)
    (π (Z[n]) 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle)
    (separableKummerH1Class K (cyclicKummerOrder K E) hn a)

omit [IsCyclic Gal(E/K)] in
theorem cyclicKummerCupOfUnit_eq (a : Kˣ) (hn : (n : K) ≠ 0)
    (β : U) (hβ : n • β = baseUnitValue K a) :
    cyclicKummerCupOfUnit K E g hg a hn = cyclicKummerCup K E g hg a β hβ := by
  let pairing := cupOneOne (kummerScalarPairing K n) (kummerScalarPairing_continuous K n)
    (kummerScalarPairing_equivariant K n)
    (π (Z[n]) 1 (finiteCyclicCharacterCrossedHom K E g hg).toCocycle)
  exact congrArg pairing (separableKummerH1Class_eq_root K (cyclicKummerOrder K E) hn a β hβ)

/-- For a cyclic character, the original Kummer cup evaluates the
character at the arithmetic Artin value. -/
theorem localKummerTrace_cyclicKummerCupOfUnit_eq_artin
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [IsAbelianGalois K E] (a : Kˣ) (hn : (n : K) ≠ 0) :
    zmodToRationalCircle n Nat.card_pos (localKummerTrace K (cyclicKummerOrder K E) hn
        (cyclicKummerCupOfUnit K E g hg a hn)) =
      finiteCyclicArithmeticCharacter g hg
        (Additive.ofMul ((LocalClassFieldTheory.abelianLocalArtinMap K E a)⁻¹)) := by
  obtain ⟨β, hβ⟩ := exists_cyclicKummerRoot K E a hn
  let N := cyclicKummerOrder K E
  let evaluate := zmodToRationalCircle n Nat.card_pos ∘ localKummerTrace K N hn
  let y := cyclicKummerCup K E g hg a β hβ
  have h₁ := congrArg evaluate (cyclicKummerCupOfUnit_eq K E g hg a hn β hβ)
  have h₂ := zmodToRationalCircle_localKummerTrace K N hn y
  have h₃ := congrArg (localBrauerInvariant K)
    (separableMuH2ToBr_cyclicKummerCup K E g hg a β hβ)
  exact h₁.trans (h₂.trans (h₃.trans (localBrauerInvariant_cyclicBrauerClass_eq_artin K E g hg a)))

end CyclicCharacter

end ClassFieldTheory.Brauer
