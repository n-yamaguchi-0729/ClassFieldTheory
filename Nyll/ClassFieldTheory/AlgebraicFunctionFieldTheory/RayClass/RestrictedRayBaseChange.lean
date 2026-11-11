/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReciprocity
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RayPrincipalUnitValues
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantExtensionUnramified
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Actual restricted-ray transitions under finite field extension

The original completion maps preserve the full first principal-unit groups.
For a reduced boundary modulus they therefore induce a map of the actual
restricted ray products. This map is constructed from idele base change,
before its restriction to the absolute-reciprocity kernels.

The kernel transition carries every original function to its actual field
image. All local orders transform by the original ramification indices;
the actual finite constant extensions have index one and preserve those orders.
-/

@[expose] public section

universe u v w

noncomputable section

open AlgebraicCurve Filter
open scoped AlgebraicCurve.Place WithZero

namespace FunctionField.RayClass

section BaseChange

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

variable (L) in
/-- Pull the modulus function back along the original restriction of places.
Its support stays finite because the extension has finite place fibres. -/
def rayModulusBaseChange (m : Modulus k K) : Modulus k L :=
  Finsupp.ofSupportFinite (fun w : Place k L => m (w.restrict K))
    (Filter.eventually_cofinite.mp
      ((IdeleGroup.tendsto_restrict_cofinite (k := k) (K := K) (L := L)).eventually
        (Filter.eventually_cofinite.mpr m.hasFiniteSupport)))

/-- The new exponent is precisely the exponent at the original place below. -/
theorem rayModulusBaseChange_apply (m : Modulus k K) (w : Place k L) :
    rayModulusBaseChange L m w = m (w.restrict K) := rfl

/-- A nonempty boundary remains nonempty under actual finite extension. -/
theorem rayModulusBaseChange_ne_zero (m : Modulus k K) (hm : m ≠ 0) :
    rayModulusBaseChange L m ≠ 0 := by
  intro h
  apply hm
  apply Finsupp.ext
  intro v
  obtain ⟨w, hw⟩ := Place.exists_restrict_eq (M := L) v
  have he := congrArg (fun n : Modulus k L => n w) h
  change m (w.restrict K) = 0 at he
  exact hw ▸ he

/-- The literal completion inclusion preserves and reflects the full group
`1 + 𝔪`, for any finite extension and every original extending place. -/
theorem localBaseChange_mem_firstHigherUnit_iff (w : Place k L)
    (x : (w.restrict K).adicCompletionˣ) :
    IdeleGroup.localBaseChange (K := K) w x ∈ localHigherUnitGroup w 1 ↔
      x ∈ localHigherUnitGroup (w.restrict K) 1 := by
  rw [localHigherUnitGroup_one_iff_sub_one_lt_one,
    localHigherUnitGroup_one_iff_sub_one_lt_one]
  change Valued.v
    (algebraMap (w.restrict K).adicCompletion w.adicCompletion (x : _) - 1) < 1 ↔ _
  rw [← map_one (algebraMap (w.restrict K).adicCompletion w.adicCompletion),
    ← map_sub, Place.algebraMap_adicCompletionComap_eq, Place.valued_adicCompletionComap]
  exact pow_lt_one_iff_of_nonneg zero_le (w.ramificationIndex_pos (F := K)).ne'

/-- Actual idele base change respects every reduced boundary congruence. -/
theorem baseChange_mem_reducedCongruence (m : Modulus k K)
    (hm : ∀ v, m v ≤ 1) (a : IdeleGroup k K) (ha : a ∈ congruenceSubgroup m) :
    IdeleGroup.baseChange (K := K) (L := L) a ∈
      congruenceSubgroup (rayModulusBaseChange L m) := by
  intro w
  change IdeleGroup.localBaseChange (K := K) w (a (w.restrict K)) ∈
    localHigherUnitGroup w (m (w.restrict K))
  rcases Nat.eq_zero_or_pos (m (w.restrict K)) with hzero | hpos
  · rw [hzero, localHigherUnitGroup_zero]
    apply IdeleGroup.localBaseChange_mem_localUnits
    exact localHigherUnitGroup_le_localUnits _ _ (ha (w.restrict K))
  · have hone : m (w.restrict K) = 1 := Nat.le_antisymm (hm _) hpos
    rw [hone]
    apply (localBaseChange_mem_firstHigherUnit_iff w _).mpr
    simpa only [hone] using ha (w.restrict K)

/-- The map on local ray quotients induced by the original idele inclusion. -/
def rayLocalBaseChange (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    RayLocalQuotient m →* RayLocalQuotient (rayModulusBaseChange L m) :=
  QuotientGroup.map (congruenceSubgroup m) (congruenceSubgroup (rayModulusBaseChange L m))
    (IdeleGroup.baseChange (K := K) (L := L))
    (fun a ha => baseChange_mem_reducedCongruence m hm a ha)

/-- Actual finite-extension transition on the restricted product of local ray factors. -/
def restrictedRayBaseChange (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    RayRestrictedProduct m →* RayRestrictedProduct (rayModulusBaseChange L m) :=
  (rayLocalRestrictedProductEquiv (rayModulusBaseChange L m)).toMonoidHom.comp
    ((rayLocalBaseChange m hm).comp (rayLocalRestrictedProductEquiv m).symm.toMonoidHom)

/-- The transition is induced by the original completion maps on every idele. -/
theorem restrictedRayBaseChange_idele (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (a : IdeleGroup k K) :
    restrictedRayBaseChange (L := L) m hm (ideleToRayRestrictedProduct m a) =
      ideleToRayRestrictedProduct (rayModulusBaseChange L m)
        (IdeleGroup.baseChange (K := K) (L := L) a) := by
  have he : ideleToRayRestrictedProduct m a =
      rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a) := rfl
  rw [he]
  change rayLocalRestrictedProductEquiv (rayModulusBaseChange L m)
    (rayLocalBaseChange m hm ((rayLocalRestrictedProductEquiv m).symm
      (rayLocalRestrictedProductEquiv m (QuotientGroup.mk' (congruenceSubgroup m) a)))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- Every coordinate is the actual inclusion into the extending completion. -/
theorem restrictedRayBaseChange_idele_apply
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : IdeleGroup k K) (w : Place k L) :
    restrictedRayBaseChange (L := L) m hm (ideleToRayRestrictedProduct m a) w =
      QuotientGroup.mk' (localHigherUnitGroup w (m (w.restrict K)))
        (IdeleGroup.localBaseChange (K := K) w (a (w.restrict K))) := by
  rw [restrictedRayBaseChange_idele]
  rfl

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The actual transition sends diagonal functions to their original field images. -/
theorem restrictedRayBaseChange_principal (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (x : Kˣ) :
    restrictedRayBaseChange (L := L) m hm (principalToRayRestrictedProduct m x) =
      principalToRayRestrictedProduct (rayModulusBaseChange L m)
        (Units.map (algebraMap K L) x) := by
  change restrictedRayBaseChange (L := L) m hm
    (ideleToRayRestrictedProduct m (IdeleGroup.principalIdele k K x)) =
      ideleToRayRestrictedProduct (rayModulusBaseChange L m)
        (IdeleGroup.principalIdele k L (Units.map (algebraMap K L) x))
  rw [restrictedRayBaseChange_idele, IdeleGroup.baseChange_principalIdele]

end BaseChange

private theorem map_mem_range_of_commuting_square
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (p : A →* B) (q : C →* D) (f : B →* D) (g : A →* C)
    (h : ∀ x, f (p x) = q (g x)) {b : B} (hb : b ∈ p.range) :
    f b ∈ q.range := by
  obtain ⟨x, rfl⟩ := hb
  exact ⟨g x, (h x).symm⟩

section Arithmetic

variable {k : Type u} {K : Type v} {L : Type w}
    [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]

/-- The actual restricted-product transition carries the native absolute-Artin
kernel into the native absolute-Artin kernel of the extended field. -/
theorem restrictedRayBaseChange_mem_artinKernel
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (a : RayRestrictedProduct m)
    (ha : a ∈ (restrictedProductAbsoluteArtin m).ker) :
    restrictedRayBaseChange (L := L) m hm a ∈
      (restrictedProductAbsoluteArtin (rayModulusBaseChange L m)).ker := by
  have hsource : a ∈ (principalToRayRestrictedProduct m).range :=
    (congrArg (fun H : Subgroup (RayRestrictedProduct m) => a ∈ H)
      (restrictedProductAbsoluteArtin_ker m)).mp ha
  apply (congrArg
    (fun H : Subgroup (RayRestrictedProduct (rayModulusBaseChange L m)) =>
      restrictedRayBaseChange (L := L) m hm a ∈ H)
    (restrictedProductAbsoluteArtin_ker (rayModulusBaseChange L m))).mpr
  exact map_mem_range_of_commuting_square
    (principalToRayRestrictedProduct m)
    (principalToRayRestrictedProduct (rayModulusBaseChange L m))
    (restrictedRayBaseChange (L := L) m hm)
    (Units.map (algebraMap K L).toMonoidHom)
    (restrictedRayBaseChange_principal (L := L) m hm) hsource

/-- The kernel transition is the restriction of actual idele base change;
it is constructed before comparing the kernels with function groups. -/
def principalArtinKernelBaseChange (m : Modulus k K) (hm : ∀ v, m v ≤ 1) :
    (restrictedProductAbsoluteArtin m).ker →*
      (restrictedProductAbsoluteArtin (rayModulusBaseChange L m)).ker where
  toFun a := ⟨restrictedRayBaseChange (L := L) m hm a.val,
    restrictedRayBaseChange_mem_artinKernel (L := L) m hm a.val a.property⟩
  map_one' := Subtype.ext (map_one (restrictedRayBaseChange (L := L) m hm))
  map_mul' a b := Subtype.ext (map_mul (restrictedRayBaseChange (L := L) m hm) a.val b.val)

/-- The kernel identifications commute with the original inclusion of functions. -/
theorem principalArtinKernelBaseChange_equiv
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) (x : Kˣ) :
    principalArtinKernelBaseChange (L := L) m hm
        (principalRestrictedArtinKernelEquiv m hmzero x) =
      principalRestrictedArtinKernelEquiv (rayModulusBaseChange L m)
        (rayModulusBaseChange_ne_zero m hmzero) (Units.map (algebraMap K L) x) := by
  apply Subtype.ext
  exact restrictedRayBaseChange_principal m hm x

/-- The actual kernel transition is injective, as is the original field inclusion. -/
theorem principalArtinKernelBaseChange_injective
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0) :
    Function.Injective (principalArtinKernelBaseChange (L := L) m hm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (principalRestrictedArtinKernelEquiv m hmzero).surjective a
  obtain ⟨y, rfl⟩ := (principalRestrictedArtinKernelEquiv m hmzero).surjective b
  rw [principalArtinKernelBaseChange_equiv, principalArtinKernelBaseChange_equiv] at hab
  have hxy := (principalRestrictedArtinKernelEquiv (rayModulusBaseChange L m)
    (rayModulusBaseChange_ne_zero m hmzero)).injective hab
  exact congrArg (principalRestrictedArtinKernelEquiv m hmzero)
    (Units.map_injective (algebraMap K L).injective hxy)

/-- Every original local order transforms by its actual ramification index. -/
theorem principalArtinKernelBaseChange_order
    (m : Modulus k K) (hm : ∀ v, m v ≤ 1) (hmzero : m ≠ 0)
    (x : Kˣ) (w : Place k L) :
    (restrictedRayOrder (rayModulusBaseChange L m) w
        (principalArtinKernelBaseChange (L := L) m hm
          (principalRestrictedArtinKernelEquiv m hmzero x))).toAdd =
      (w.ramificationIndex K : ℤ) * (w.restrict K).ord (x : K) := by
  rw [principalArtinKernelBaseChange_equiv,
    restrictedRayOrder_principalRestrictedArtinKernelEquiv]
  exact w.ord_restrict (x : K)

end Arithmetic

section Constants

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
    [HasPrincipalDivisors k K] [Algebra (RatFunc k) K]
    [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    (Ω : Type w) [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsSepClosed Ω]

/-- Along the actual finite extensions of the full constants, the kernel
transition preserves every original normalized integer order. The target
function-field presentation and principal divisors are supplied internally. -/
theorem principalArtinKernelBaseChange_fullConstant_order
    (n : ℕ) [NeZero n] (m : Modulus k K) (hm : ∀ v, m v ≤ 1)
    (hmzero : m ≠ 0) (x : Kˣ) :
    let E := fullConstantDegreeStage k K Ω n
    let p := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K E
    let _ : Algebra (RatFunc k) E := p.val
    let _ : IsScalarTower k (RatFunc k) E := p.property.1
    let _ : FunctionField k E := p.property.2
    let _ : HasPrincipalDivisors k E :=
      (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
    ∀ w : Place k E,
      (restrictedRayOrder (rayModulusBaseChange E m) w
          (principalArtinKernelBaseChange (L := E) m hm
            (principalRestrictedArtinKernelEquiv m hmzero x))).toAdd =
        (w.restrict K).ord (x : K) := by
  intro E p aRE hkRE hE hprincipal w
  rw [principalArtinKernelBaseChange_order,
    ramificationIndex_fullConstantDegreeStage k K Ω n w, Nat.cast_one, one_mul]

end Constants

end FunctionField.RayClass
