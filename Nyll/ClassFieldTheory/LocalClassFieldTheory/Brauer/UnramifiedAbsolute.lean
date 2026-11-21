/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteInflationExactness
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.UnramifiedInflation
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Infinite.WeilReciprocityDegree

/-! # The arithmetic invariant on the unramified Brauer subgroup

The images of the canonical finite unramified layers form an additive subgroup
of absolute continuous H². Their arithmetic invariants agree on intersections
and give an equivalence of this subgroup with `ℚ/ℤ`.
-/

@[expose] public section

open scoped ValuativeRel
open ClassFormation LocalClassFieldTheory LocalFieldTheory
  LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]

/-- The actual degree-`d` unramified layer in the chosen separable closure. -/
abbrev unramifiedBrauerStage (d : ℕ+) : FiniteGaloisIntermediateField K (SeparableClosure K) where
  toIntermediateField := localFiniteUnramifiedField K d d.pos

/-- The generating unramified stage at a divisor embeds in the stage at its multiple. -/
theorem unramifiedBrauerStage_le {d e : ℕ+} (hde : (d : ℕ) ∣ (e : ℕ)) :
    (unramifiedBrauerStage K d).toIntermediateField ≤
      (unramifiedBrauerStage K e).toIntermediateField := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (unramifiedBrauerStage K d).toIntermediateField,
    ← InfiniteGalois.fixedField_fixingSubgroup (unramifiedBrauerStage K e).toIntermediateField]
  apply IntermediateField.fixedField_le
  intro σ hσ
  have he := (localFiniteUnramifiedField_mem_fixingSubgroup_iff K e e.pos σ).mp hσ
  apply (localFiniteUnramifiedField_mem_fixingSubgroup_iff K d d.pos σ).mpr
  apply Multiplicative.ext
  have he' := congrArg Multiplicative.toAdd he
  change zHatReduction e e.pos (localResidueDegree K σ).toAdd = 0 at he'
  change zHatReduction d d.pos (localResidueDegree K σ).toAdd = 0
  rw [← zHatReduction_transition d.pos e.pos hde, he', map_zero]

/-- The fixed-degree invariant uses the same relative cohomology and arithmetic Frobenius
as the invariant on a finite unramified local extension. -/
def unramifiedBrauerStageInvariant (d : ℕ+) :
    relativeBr (unramifiedBrauerStage K d) →+ AddCircle (1 : ℚ) :=
  unramifiedContinuousInvariant K (localFiniteUnramifiedField K d d.pos)

private theorem stageInvariant_injective (d : ℕ+) :
    Function.Injective (unramifiedBrauerStageInvariant K d) :=
  unramifiedContinuousInvariant_injective K (localFiniteUnramifiedField K d d.pos)

private theorem exists_stageInflation {d e : ℕ+} (hde : (d : ℕ) ∣ (e : ℕ))
    (x : relativeBr (unramifiedBrauerStage K d)) :
    ∃ y : relativeBr (unramifiedBrauerStage K e),
      finiteInflation (unramifiedBrauerStage K e) y =
        finiteInflation (unramifiedBrauerStage K d) x ∧
        unramifiedBrauerStageInvariant K e y = unramifiedBrauerStageInvariant K d x := by
  let E := localFiniteUnramifiedField K d d.pos
  let F := localFiniteUnramifiedField K e e.pos
  let : Algebra E F :=
    (IntermediateField.inclusion (unramifiedBrauerStage_le K hde)).toRingHom.toAlgebra
  let : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional E F := FiniteDimensional.right K E F
  let y := relativeInflation K E F x
  refine ⟨y, ?_, ?_⟩
  · exact finiteInflation_tower (unramifiedBrauerStage K d) (unramifiedBrauerStage K e)
      (fun _ => rfl) x
  · exact unramifiedContinuousInvariant_inflation K E F x

private theorem exists_commonStage {d e : ℕ+}
    (x : relativeBr (unramifiedBrauerStage K d)) (y : relativeBr (unramifiedBrauerStage K e)) :
    ∃ x' y' : relativeBr (unramifiedBrauerStage K (d * e)),
      finiteInflation (unramifiedBrauerStage K (d * e)) x' =
        finiteInflation (unramifiedBrauerStage K d) x ∧
      finiteInflation (unramifiedBrauerStage K (d * e)) y' =
        finiteInflation (unramifiedBrauerStage K e) y ∧
      unramifiedBrauerStageInvariant K (d * e) x' = unramifiedBrauerStageInvariant K d x ∧
      unramifiedBrauerStageInvariant K (d * e) y' = unramifiedBrauerStageInvariant K e y := by
  obtain ⟨x', hx', hxinv⟩ := exists_stageInflation K (e := d * e) (dvd_mul_right (d : ℕ) (e : ℕ)) x
  obtain ⟨y', hy', hyinv⟩ := exists_stageInflation K (e := d * e) (dvd_mul_left (e : ℕ) (d : ℕ)) y
  exact ⟨x', y', hx', hy', hxinv, hyinv⟩

/-- The actual subgroup of absolute classes in the images of finite unramified inflation. -/
def unramifiedBr : AddSubgroup (Br K) where
  carrier := {z | ∃ (d : ℕ+) (x : relativeBr (unramifiedBrauerStage K d)),
    finiteInflation (unramifiedBrauerStage K d) x = z}
  zero_mem' := ⟨1, 0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨d, x, rfl⟩ ⟨e, y, rfl⟩
    obtain ⟨x', y', hx, hy, _, _⟩ := exists_commonStage K x y
    exact ⟨d * e, x' + y', by rw [map_add, hx, hy]⟩
  neg_mem' := by
    rintro _ ⟨d, x, rfl⟩
    exact ⟨d, -x, map_neg _ _⟩

/-- A class in the unramified subgroup has an actual finite unramified relative representative. -/
theorem mem_unramifiedBr_iff (z : Br K) :
    z ∈ unramifiedBr K ↔
      ∃ (d : ℕ+) (x : relativeBr (unramifiedBrauerStage K d)),
        finiteInflation (unramifiedBrauerStage K d) x = z :=
  Iff.rfl

/-- Absolute inflation of a finite unramified class, with its membership witness. -/
def unramifiedBrauerInflation (d : ℕ+) :
    relativeBr (unramifiedBrauerStage K d) →+ unramifiedBr K :=
  (finiteInflation (unramifiedBrauerStage K d)).codRestrict (unramifiedBr K) fun x => ⟨d, x, rfl⟩

private theorem stageInvariant_eq_of_inflation_eq {d e : ℕ+}
    {x : relativeBr (unramifiedBrauerStage K d)} {y : relativeBr (unramifiedBrauerStage K e)}
    (h : finiteInflation (unramifiedBrauerStage K d) x =
      finiteInflation (unramifiedBrauerStage K e) y) :
    unramifiedBrauerStageInvariant K d x = unramifiedBrauerStageInvariant K e y := by
  obtain ⟨x', y', hx, hy, hxinv, hyinv⟩ := exists_commonStage K x y
  have hxy : x' = y' := finiteInflation_injective (unramifiedBrauerStage K (d * e))
    (hx.trans (h.trans hy.symm))
  rw [← hxinv, ← hyinv, hxy]

/-- The value computed on a finite unramified representative of an absolute Brauer class. -/
def unramifiedBrauerValue (z : unramifiedBr K) : AddCircle (1 : ℚ) :=
  let h := (mem_unramifiedBr_iff K z).mp z.property
  unramifiedBrauerStageInvariant K h.choose h.choose_spec.choose

/-- The value is the same for every finite unramified representative. -/
theorem unramifiedBrauerValue_eq (z : unramifiedBr K)
    (d : ℕ+) (x : relativeBr (unramifiedBrauerStage K d))
    (h : finiteInflation (unramifiedBrauerStage K d) x = z) :
    unramifiedBrauerValue K z = unramifiedBrauerStageInvariant K d x := by
  let hz := (mem_unramifiedBr_iff K z).mp z.property
  exact stageInvariant_eq_of_inflation_eq K (hz.choose_spec.choose_spec.trans h.symm)

/-- The arithmetic invariant on the actual subgroup generated by finite unramified inflation. -/
def unramifiedBrauerInvariant : unramifiedBr K →+ AddCircle (1 : ℚ) where
  toFun := unramifiedBrauerValue K
  map_zero' := (unramifiedBrauerValue_eq K 0 1 0 (map_zero _)).trans (map_zero _)
  map_add' x y := by
    obtain ⟨d, a, ha⟩ := (mem_unramifiedBr_iff K x).mp x.property
    obtain ⟨e, b, hb⟩ := (mem_unramifiedBr_iff K y).mp y.property
    obtain ⟨a', b', ha', hb', _, _⟩ := exists_commonStage K a b
    have hsum : finiteInflation (unramifiedBrauerStage K (d * e)) (a' + b') =
        (↑(x + y) : Br K) := by
      change _ = (x : Br K) + (y : Br K)
      rw [map_add, ha', hb', ha, hb]
    rw [unramifiedBrauerValue_eq K (x + y) (d * e) (a' + b') hsum,
      map_add, unramifiedBrauerValue_eq K x (d * e) a' (ha'.trans ha),
      unramifiedBrauerValue_eq K y (d * e) b' (hb'.trans hb)]

/-- The arithmetic invariant evaluates the original finite unramified relative class. -/
@[simp] theorem unramifiedBrauerInvariant_inflation (d : ℕ+)
    (x : relativeBr (unramifiedBrauerStage K d)) :
    unramifiedBrauerInvariant K (unramifiedBrauerInflation K d x) =
      unramifiedBrauerStageInvariant K d x :=
  unramifiedBrauerValue_eq K (unramifiedBrauerInflation K d x) d x rfl

/-- The unramified subgroup embeds into `ℚ/ℤ` by its arithmetic invariant. -/
theorem unramifiedBrauerInvariant_injective : Function.Injective (unramifiedBrauerInvariant K) := by
  apply (injective_iff_map_eq_zero (unramifiedBrauerInvariant K)).mpr
  intro z hz
  obtain ⟨d, x, hx⟩ := (mem_unramifiedBr_iff K z).mp z.property
  have hzero : unramifiedBrauerStageInvariant K d x = 0 :=
    (unramifiedBrauerValue_eq K z d x hx).symm.trans hz
  have hx0 : x = 0 := stageInvariant_injective K d (hzero.trans (map_zero _).symm)
  apply Subtype.ext
  change (z : Br K) = 0
  rw [← hx, hx0, map_zero]

/-- The image of the actual degree-`d` unramified layer is the `d`-torsion
subgroup of the unramified Brauer group. -/
theorem mem_range_unramifiedBrauerInflation_iff (d : ℕ+) (z : unramifiedBr K) :
    z ∈ (unramifiedBrauerInflation K d).range ↔ (d : ℕ) • z = 0 := by
  let L := localFiniteUnramifiedField K d d.pos
  have hstage : unramifiedBrauerInvariant K z ∈ (unramifiedBrauerStageInvariant K d).range ↔
      (d : ℕ) • unramifiedBrauerInvariant K z = 0 := by
    change unramifiedBrauerInvariant K z ∈ (unramifiedContinuousInvariant K L).range ↔ _
    rw [mem_range_unramifiedContinuousInvariant_iff, localFiniteUnramifiedField_finrank]
  constructor
  · rintro ⟨x, rfl⟩
    apply unramifiedBrauerInvariant_injective K
    rw [map_nsmul, map_zero]
    exact hstage.mp ⟨x, (unramifiedBrauerInvariant_inflation K d x).symm⟩
  · intro hz
    have hv : (d : ℕ) • unramifiedBrauerInvariant K z = 0 := by
      rw [← map_nsmul, hz, map_zero]
    obtain ⟨x, hx⟩ := hstage.mpr hv
    exact ⟨x, unramifiedBrauerInvariant_injective K
      ((unramifiedBrauerInvariant_inflation K d x).trans hx)⟩

/-- Each rational class comes from the unramified layer of its denominator. -/
theorem unramifiedBrauerInvariant_surjective :
    Function.Surjective (unramifiedBrauerInvariant K) := by
  intro z
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective z
  let : Fact (0 < (1 : ℚ)) := ⟨zero_lt_one⟩
  let d : ℕ+ := ⟨q.den, q.pos⟩
  let L := localFiniteUnramifiedField K d d.pos
  let t : AddCircle (1 : ℚ) := (q : AddCircle (1 : ℚ))
  have horder : addOrderOf t = q.den := by
    have hq₀ := AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := q)
    rw [mul_one] at hq₀
    exact hq₀
  have ht : Module.finrank K L • t = 0 := by
    rw [localFiniteUnramifiedField_finrank K (d : ℕ) d.pos]
    change q.den • t = 0
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero t
  obtain ⟨x, hx⟩ := (mem_range_unramifiedContinuousInvariant_iff K L t).mpr ht
  exact ⟨unramifiedBrauerInflation K d x, (unramifiedBrauerInvariant_inflation K d x).trans hx⟩

/-- The arithmetic invariant identifies the actual unramified Brauer subgroup with `ℚ/ℤ`. -/
def unramifiedBrauerInvariantEquiv : unramifiedBr K ≃+ AddCircle (1 : ℚ) :=
  AddEquiv.ofBijective (unramifiedBrauerInvariant K)
    ⟨unramifiedBrauerInvariant_injective K, unramifiedBrauerInvariant_surjective K⟩

/-- On inflated uniformizer carry classes the absolute unramified invariant is `1 / d`. -/
theorem unramifiedBrauerInvariant_uniformizer (d : ℕ+) :
    unramifiedBrauerInvariant K (unramifiedBrauerInflation K d
      (unramifiedContinuousClass K (localFiniteUnramifiedField K d d.pos)
        (Additive.ofMul (integerRingUniformizerFieldUnit K)))) = ((1 : ℚ) / (d : ℕ) : ℚ) := by
  rw [unramifiedBrauerInvariant_inflation]
  change unramifiedContinuousInvariant K (localFiniteUnramifiedField K d d.pos) _ = _
  rw [unramifiedContinuousInvariant_uniformizer, localFiniteUnramifiedField_finrank]

end ClassFieldTheory.Brauer
