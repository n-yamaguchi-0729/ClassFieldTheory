/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Invariants
public import Nyll.GaloisCohomology.Cyclic.IntegralTateExactness
public import Nyll.GaloisCohomology.Cyclic.IntegralTateFixedCycles
public import Nyll.GaloisCohomology.Cyclic.TatePositiveCocycles

/-!
# Positive-degree integral Tate inflation

Inflation is the ordinary group cochain pullback with the original
inclusion of invariants, transported across the positive-degree Tate
comparison. Both the group homomorphism and the coefficient map are used
on their actual representatives under the established universe lift.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G H P : Type u} [Group G] [Group H] [Group P]

/-- The same group homomorphism on the lifted group carriers. -/
def nativeGroupHom (f : H →* G) : ULift.{v} H →* ULift.{v} G where
  toFun h := ULift.up (f h.down)
  map_one' := congrArg ULift.up (map_one f)
  map_mul' a b := congrArg ULift.up (map_mul f a.down b.down)

/-- Lift an original coefficient map together with its specified group homomorphism. -/
def nativeCohomologyCoefficientMap {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) :
    Rep.res (nativeGroupHom.{u, v} f) ((nativeFunctor G).obj A) ⟶ (nativeFunctor H).obj B :=
  (nativeFunctor H).map g

/-- Integral cohomology pullback along the original group and coefficient maps. -/
def cohomologyMapAlong {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) (n : ℕ) : cohomology A n ⟶ cohomology B n :=
  IntegralGroupCohomology.integerScalars.map
    (groupCohomology.map (nativeGroupHom.{u, v} f) (nativeCohomologyCoefficientMap f g) n)

/-- Pullback of actual integral cochains preserves composition. -/
theorem cohomologyMapAlong_comp {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H} {C : Rep.{v} ℤ P}
    (f : H →* G) (g : P →* H) (a : Rep.res f A ⟶ B) (b : Rep.res g B ⟶ C) (n : ℕ) :
    cohomologyMapAlong (f.comp g) ((Rep.resFunctor g).map a ≫ b) n =
      cohomologyMapAlong f a n ≫ cohomologyMapAlong g b n := by
  let nf := nativeGroupHom.{u, v} f
  let ng := nativeGroupHom.{u, v} g
  let na := nativeCohomologyCoefficientMap f a
  let nb := nativeCohomologyCoefficientMap g b
  let nc := nativeCohomologyCoefficientMap (f.comp g) ((Rep.resFunctor g).map a ≫ b)
  have hcomp : groupCohomology.map (nativeGroupHom.{u, v} (f.comp g)) nc n =
      groupCohomology.map nf na n ≫ groupCohomology.map ng nb n :=
    (groupCohomology.map_congr (f := nativeGroupHom.{u, v} (f.comp g))
      (g := nf.comp ng) (φ := nc) (ψ := (Rep.resFunctor ng).map na ≫ nb)
      (MonoidHom.ext fun _ => rfl) (LinearMap.ext fun _ => rfl) n).trans
      (groupCohomology.map_comp nf ng na nb n)
  have h := congrArg (fun m => integerScalars.{max u v}.map m) hcomp
  simpa only [Functor.map_comp] using! h

/-- Removing the auxiliary lift in the common universe preserves the
original ordinary pullback along the group and coefficient maps. -/
theorem cohomologyMapAlong_comp_common {A : Rep.{u} ℤ G} {B : Rep.{u} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) (n : ℕ) :
    cohomologyMapAlong f g n ≫ (cohomologyIsoCommon B n).hom =
      (cohomologyIsoCommon A n).hom ≫ IntegralGroupCohomology.integerScalars.map
        (groupCohomology.map f ((IntegralGroupCohomology.coefficientFunctor H).map g) n) := by
  let nf := nativeGroupHom.{u, u} f
  let ng := nativeCohomologyCoefficientMap f g
  let eG := (MulEquiv.ulift : ULift.{u} G ≃* G).symm.toMonoidHom
  let eH := (MulEquiv.ulift : ULift.{u} H ≃* H).symm.toMonoidHom
  let a : Rep.res eG ((nativeFunctor G).obj A) ⟶ (coefficientFunctor G).obj A :=
    Rep.ofHom ⟨(nativeCarrierEquiv A).toLinearMap,
      fun x => nativeCarrierEquiv_comm A (ULift.up x)⟩
  let b : Rep.res eH ((nativeFunctor H).obj B) ⟶ (coefficientFunctor H).obj B :=
    Rep.ofHom ⟨(nativeCarrierEquiv B).toLinearMap,
      fun x => nativeCarrierEquiv_comm B (ULift.up x)⟩
  let cg := (coefficientFunctor H).map g
  have hcomp : groupCohomology.map nf ng n ≫ groupCohomology.map eH b n =
      groupCohomology.map eG a n ≫ groupCohomology.map f cg n :=
    (groupCohomology.map_comp nf eH ng b n).symm.trans
      ((groupCohomology.map_congr (f := nf.comp eH) (g := eG.comp f)
        (φ := (Rep.resFunctor eH).map ng ≫ b) (ψ := (Rep.resFunctor f).map a ≫ cg)
        (MonoidHom.ext fun _ => rfl) (LinearMap.ext fun _ => rfl) n).trans
        (groupCohomology.map_comp eG f a cg n))
  have h := congrArg (fun m => integerScalars.{u}.map m) hcomp
  simpa only [Functor.map_comp] using! h

/-- Ordinary cochain pullback commutes with the actual connecting maps for a
morphism of coefficient sequences across the indicated group homomorphism. -/
theorem cohomologyMapAlong_δ {S : ShortComplex (Rep.{v} ℤ G)}
    {T : ShortComplex (Rep.{v} ℤ H)} (f : H →* G) (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S.map (Rep.resFunctor f) ⟶ T) (n : ℕ) :
    δ hS n (n + 1) rfl ≫ cohomologyMapAlong f a.τ₁ (n + 1) =
      cohomologyMapAlong f a.τ₃ n ≫ δ hT n (n + 1) rfl := by
  let R := ULift.{max u v} ℤ
  let S' := S.map (nativeFunctor G)
  let T' := T.map (nativeFunctor H)
  let e := nativeGroupHom.{u, v} f
  let E : S'.map (groupCohomology.cochainsFunctor R (ULift.{v} G)) ⟶
      T'.map (groupCohomology.cochainsFunctor R (ULift.{v} H)) := {
    τ₁ := groupCohomology.cochainsMap e (nativeCohomologyCoefficientMap f a.τ₁)
    τ₂ := groupCohomology.cochainsMap e (nativeCohomologyCoefficientMap f a.τ₂)
    τ₃ := groupCohomology.cochainsMap e (nativeCohomologyCoefficientMap f a.τ₃)
    comm₁₂ := by
      apply HomologicalComplex.hom_ext
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext h
      change ULift.up ((a.τ₁ ≫ T.f) (x (e ∘ h)).down) =
        ULift.up ((((S.map (Rep.resFunctor f)).f) ≫ a.τ₂) (x (e ∘ h)).down)
      rw [a.comm₁₂]
    comm₂₃ := by
      apply HomologicalComplex.hom_ext
      intro i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      funext h
      change ULift.up ((a.τ₂ ≫ T.g) (x (e ∘ h)).down) =
        ULift.up ((((S.map (Rep.resFunctor f)).g) ≫ a.τ₃) (x (e ∘ h)).down)
      rw [a.comm₂₃] }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality E
    (groupCohomology.map_cochainsFunctor_shortExact (native_shortExact hS))
    (groupCohomology.map_cochainsFunctor_shortExact (native_shortExact hT)) n (n + 1) rfl
  have h := congrArg (fun m => integerScalars.{max u v}.map m) hδ
  simpa only [Functor.map_comp] using! h

variable [Fintype G] [Fintype H] [Fintype P]

/-- The original positive-degree Tate comparison with ordinary integral
cohomology in independent group and coefficient universes. -/
def tatePositiveIsoCohomology (A : Rep.{v} ℤ G) (n : ℕ) [NeZero n] :
    tate A n ≅ cohomology A n :=
  IntegralGroupCohomology.integerScalars.mapIso
    ((TateCohomology.isoGroupCohomology n).app ((nativeFunctor G).obj A))

/-- The ordinary degree-zero class of the very same fixed vector. -/
def cohomologyZeroFixedClass (A : Rep.{v} ℤ G) (a : A.ρ.invariants) : cohomology A 0 :=
  (groupCohomology.H0Iso ((nativeFunctor G).obj A)).inv (nativeFixedEquiv A a)

private theorem native_map_zero_fixedClass {R G₀ H₀ : Type w}
    [CommRing R] [Group G₀] [Group H₀] {A : Rep R G₀} {B : Rep R H₀}
    (f : H₀ →* G₀) (φ : Rep.res f A ⟶ B) (a : A.ρ.invariants) (b : B.ρ.invariants)
    (hb : φ a.val = b.val) :
    groupCohomology.map f φ 0 ((groupCohomology.H0Iso A).inv a) =
      (groupCohomology.H0Iso B).inv b := by
  let eA := groupCohomology.H0Iso A
  let eB := groupCohomology.H0Iso B
  apply eB.toLinearEquiv.injective
  apply Subtype.val_injective
  have hm := ConcreteCategory.congr_hom (groupCohomology.map_H0Iso_hom_f f φ) (eA.inv a)
  change (eB.hom (groupCohomology.map f φ 0 (eA.inv a))).val =
    φ ((eA.hom (eA.inv a)).val) at hm
  change (eB.hom (groupCohomology.map f φ 0 (eA.inv a))).val = (eB.hom (eB.inv b)).val
  have ha' : eA.hom (eA.inv a) = a := Iso.inv_hom_id_apply eA a
  have hb' : eB.hom (eB.inv b) = b := Iso.inv_hom_id_apply eB b
  rw [ha'] at hm
  rw [hb']
  exact hm.trans hb

omit [Fintype G] [Fintype H] in
/-- Ordinary degree-zero pullback carries the original fixed representative
to its actual coefficient image. -/
theorem cohomologyMapAlong_zero_fixedClass {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) (a : A.ρ.invariants) :
    let b : B.ρ.invariants := ⟨g a.val, fun h => by
      rw [← Rep.hom_comm_apply]
      exact congrArg g (a.property (f h))⟩
    cohomologyMapAlong f g 0 (cohomologyZeroFixedClass A a) = cohomologyZeroFixedClass B b := by
  intro b
  exact native_map_zero_fixedClass.{max u v} (nativeGroupHom.{u, v} f)
    (nativeCohomologyCoefficientMap f g) (nativeFixedEquiv A a) (nativeFixedEquiv B b) rfl

/-- The positive-degree comparison carries the integral Tate boundary to the
ordinary boundary of the very same short exact sequence. -/
@[reassoc]
theorem tateδ_positive_comparison {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact)
    (n : ℕ) [NeZero n] :
    tateδ hS n ≫ (tatePositiveIsoCohomology S.X₁ (n + 1)).hom =
      (tatePositiveIsoCohomology S.X₃ n).hom ≫ δ hS n (n + 1) rfl := by
  let F := integerScalars.{max u v}
  let S' := S.map (nativeFunctor G)
  let a := TateCohomology.δ (native_shortExact hS) (n : ℤ)
  let b := ((TateCohomology.isoGroupCohomology (n + 1)).app S'.X₁).hom
  let c := ((TateCohomology.isoGroupCohomology n).app S'.X₃).hom
  let d := groupCohomology.δ (native_shortExact hS) n (n + 1) rfl
  have h : a ≫ b = c ≫ d := TateCohomology.δ_comp_isoGroupCohomology (native_shortExact hS) n
  exact (F.map_comp a b).symm.trans ((congrArg (fun m => F.map m) h).trans (F.map_comp c d))

/-- The ordinary fixed vector and its degree-zero Tate class have the same
boundary in degree one on the original short exact sequence. -/
theorem tateδ_zero_fixedClass_comparison {S : ShortComplex (Rep.{v} ℤ G)} (hS : S.ShortExact)
    (a : S.X₃.ρ.invariants) :
    (tatePositiveIsoCohomology S.X₁ 1).hom (tateδ hS 0 (fixedClass S.X₃ a)) =
      δ hS 0 1 rfl (cohomologyZeroFixedClass S.X₃ a) :=
  TateCohomology.δ_zero_fixedClass (native_shortExact hS) (nativeFixedEquiv S.X₃ a)

/-- Positive-degree Tate pullback via the actual ordinary group cochains. -/
def tatePositiveMapAlong {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) (n : ℕ) [NeZero n] : tate A n ⟶ tate B n :=
  (tatePositiveIsoCohomology A n).hom ≫ cohomologyMapAlong f g n ≫
    (tatePositiveIsoCohomology B n).inv

/-- Positive Tate pullback is precisely ordinary pullback under comparison. -/
theorem tatePositiveMapAlong_comp_comparison {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H}
    (f : H →* G) (g : Rep.res f A ⟶ B) (n : ℕ) [NeZero n] :
    tatePositiveMapAlong f g n ≫ (tatePositiveIsoCohomology B n).hom =
      (tatePositiveIsoCohomology A n).hom ≫ cohomologyMapAlong f g n := by
  simp only [tatePositiveMapAlong, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The original positive Tate pullback respects towers of group and coefficient maps. -/
theorem tatePositiveMapAlong_comp {A : Rep.{v} ℤ G} {B : Rep.{v} ℤ H} {C : Rep.{v} ℤ P}
    (f : H →* G) (g : P →* H) (a : Rep.res f A ⟶ B) (b : Rep.res g B ⟶ C)
    (n : ℕ) [NeZero n] :
    tatePositiveMapAlong (f.comp g) ((Rep.resFunctor g).map a ≫ b) n =
      tatePositiveMapAlong f a n ≫ tatePositiveMapAlong g b n := by
  unfold tatePositiveMapAlong
  rw [cohomologyMapAlong_comp f g a b n]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Over the identity group map, positive pullback is the original Tate map
of the given coefficient morphism. -/
theorem tatePositiveMapAlong_id_group {A B : Rep.{v} ℤ G} (g : A ⟶ B)
    (n : ℕ) [NeZero n] : tatePositiveMapAlong (MonoidHom.id G) g n = (tateFunctor G n).map g := by
  have h : cohomologyMapAlong (MonoidHom.id G) g n = (cohomologyFunctor G n).map g := by
    unfold cohomologyMapAlong
    apply congrArg IntegralGroupCohomology.integerScalars.map
    exact groupCohomology.map_congr (MonoidHom.ext fun _ => rfl) (LinearMap.ext fun _ => rfl) n
  rw [← cancel_mono (tatePositiveIsoCohomology B n).hom, tatePositiveMapAlong_comp_comparison, h]
  have hi := congrArg (fun m => integerScalars.{max u v}.map m)
    ((TateCohomology.isoGroupCohomology n).hom.naturality ((nativeFunctor G).map g)).symm
  simpa only [Functor.map_comp] using! hi

/-- Positive Tate pullback commutes with the original positive connecting maps. -/
theorem tatePositiveMapAlong_δ {S : ShortComplex (Rep.{v} ℤ G)}
    {T : ShortComplex (Rep.{v} ℤ H)} (f : H →* G) (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S.map (Rep.resFunctor f) ⟶ T) (n : ℕ) [NeZero n] :
    tateδ hS n ≫ tatePositiveMapAlong f a.τ₁ (n + 1) =
      tatePositiveMapAlong f a.τ₃ n ≫ tateδ hT n := by
  rw [← cancel_mono (tatePositiveIsoCohomology T.X₁ (n + 1)).hom]
  simp only [Category.assoc, tatePositiveMapAlong_comp_comparison]
  rw [tateδ_positive_comparison_assoc, tateδ_positive_comparison,
    ← Category.assoc (tatePositiveMapAlong f a.τ₃ n), tatePositiveMapAlong_comp_comparison,
    Category.assoc, cohomologyMapAlong_δ f hS hT a n]

/-- Positive pullback sends the boundary of a fixed representative to the
boundary of its actual coefficient image. -/
theorem tatePositiveMapAlong_δ_fixedClass {S : ShortComplex (Rep.{v} ℤ G)}
    {T : ShortComplex (Rep.{v} ℤ H)} (f : H →* G) (hS : S.ShortExact) (hT : T.ShortExact)
    (a : S.map (Rep.resFunctor f) ⟶ T) (x : S.X₃.ρ.invariants) :
    let y : T.X₃.ρ.invariants := ⟨a.τ₃ x.val, fun h => by
      rw [← Rep.hom_comm_apply]
      exact congrArg a.τ₃ (x.property (f h))⟩
    tatePositiveMapAlong f a.τ₁ 1 (tateδ hS 0 (fixedClass S.X₃ x)) =
      tateδ hT 0 (fixedClass T.X₃ y) := by
  intro y
  let e := tatePositiveIsoCohomology T.X₁ 1
  apply e.toLinearEquiv.injective
  change (tatePositiveMapAlong f a.τ₁ 1 ≫ e.hom) (tateδ hS 0 (fixedClass S.X₃ x)) =
    e.hom (tateδ hT 0 (fixedClass T.X₃ y))
  rw [tatePositiveMapAlong_comp_comparison, ModuleCat.comp_apply]
  change cohomologyMapAlong f a.τ₁ 1
      ((tatePositiveIsoCohomology S.X₁ 1).hom (tateδ hS 0 (fixedClass S.X₃ x))) =
    (tatePositiveIsoCohomology T.X₁ 1).hom (tateδ hT 0 (fixedClass T.X₃ y))
  rw [tateδ_zero_fixedClass_comparison, tateδ_zero_fixedClass_comparison]
  change (δ hS 0 1 rfl ≫ cohomologyMapAlong f a.τ₁ 1) (cohomologyZeroFixedClass S.X₃ x) = _
  rw [cohomologyMapAlong_δ f hS hT a 0, ModuleCat.comp_apply, cohomologyMapAlong_zero_fixedClass]

/-- The original inclusion used when inflating from the normal-subgroup invariants. -/
def tateInflationCoefficientMap (S : Subgroup G) [S.Normal] (A : Rep.{v} ℤ G) :
    Rep.res (QuotientGroup.mk' S) (A.quotientToInvariants S) ⟶ A := by
  let B := Rep.res (QuotientGroup.mk' S) (A.quotientToInvariants S)
  letI : Module ℤ B := B.hV2
  exact Rep.ofHom (A.ρ.quotientToInvariants_lift S)

/-- Inflate from the actual normal-subgroup invariants in positive degree. -/
def tateInflate (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]
    (A : Rep.{v} ℤ G) (n : ℕ) [NeZero n] :
    tate (A.quotientToInvariants S) n ⟶ tate A n :=
  tatePositiveMapAlong (QuotientGroup.mk' S) (tateInflationCoefficientMap S A) n

/-- Inflation acts by the original quotient pullback and includes the same invariant values. -/
theorem tateInflate_comp_comparison (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]
    (A : Rep.{v} ℤ G) (n : ℕ) [NeZero n] :
    tateInflate S A n ≫ (tatePositiveIsoCohomology A n).hom =
      (tatePositiveIsoCohomology (A.quotientToInvariants S) n).hom ≫ cohomologyMapAlong
        (QuotientGroup.mk' S) (tateInflationCoefficientMap S A) n :=
  tatePositiveMapAlong_comp_comparison (QuotientGroup.mk' S)
    (tateInflationCoefficientMap S A) n

end IntegralGroupCohomology.Universe
