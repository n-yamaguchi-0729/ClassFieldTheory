/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.CharacterConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ConductorLattice
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.TopologicalGlobalNormResidue
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.Data.Finset.Lattice.Union

/-!
# The full conductor as the least common multiple of character conductors

Characters are composed with the actual global norm-residue symbol. Finite
abelian character separation identifies the intersection of their kernels
with the actual norm subgroup. The full conductor lattice then gives the
least common multiple, with maximum finite exponents and union of real parts.
The coefficient monoid only needs enough roots of unity for the finite Galois
group; no topology or field structure on the coefficient monoid is needed.
-/

@[expose] public section

open scoped NumberField IsMulCommutative

noncomputable section

namespace GlobalClassFieldTheory.GlobalClassFields

open NumberField IsDedekindDomain Reciprocity

universe u v w

variable (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The kernel of a finite Galois character composed with actual global
reciprocity is conductorial because it contains the actual norm subgroup. -/
def abelianCharacterConductorialSubgroup
    {A : Type*} [CommGroup A] (χ : Gal(L/K) →* A) : ConductorialSubgroup K :=
  ⟨(χ.comp (globalNormResidueMonoidHom K L)).ker,
    ⟨(ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor, by
      let H := ideleClassNormConductorialSubgroup (K := K) (L := L)
      apply H.fullConductor_isDefiningModulus.trans
      intro c hc
      change χ (globalNormResidueMonoidHom K L c) = 1
      rw [(globalNormResidueMonoidHom_eq_one_iff K L c).mpr hc, map_one]⟩⟩

/-- The full conductor of a finite Galois character, using the kernel of its
actual norm-residue character on the original idele class group. -/
def abelianCharacterConductor
    {A : Type*} [CommGroup A] (χ : Gal(L/K) →* A) : RayClass.Modulus K :=
  (abelianCharacterConductorialSubgroup K L χ).fullConductor

/-- With a discrete target, the finite Galois definition is exactly the
existing continuous idele-character conductor. -/
theorem abelianCharacterConductor_eq_characterConductor
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [DiscreteTopology A] (χ : Gal(L/K) →ₜ* A) :
    abelianCharacterConductor K L χ.toMonoidHom =
      characterConductor (χ.comp (globalNormResidueContinuousMonoidHom K L)) :=
  rfl

/-- Every finite Galois character conductor divides the full norm conductor. -/
theorem abelianCharacterConductor_le
    {A : Type*} [CommGroup A] (χ : Gal(L/K) →* A) :
    abelianCharacterConductor K L χ ≤
      (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor := by
  let H := ideleClassNormConductorialSubgroup (K := K) (L := L)
  let C := abelianCharacterConductorialSubgroup K L χ
  apply (C.isDefiningModulus_iff_fullConductor_le H.fullConductor).mp
  apply H.fullConductor_isDefiningModulus.trans
  intro c hc
  change χ (globalNormResidueMonoidHom K L c) = 1
  rw [(globalNormResidueMonoidHom_eq_one_iff K L c).mpr hc, map_one]

variable (M : Type w) [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent Gal(L/K))]

local instance : Fintype (Gal(L/K) →* Mˣ) := Fintype.ofFinite _

/-- Finite abelian characters with enough roots detect exactly the kernel of
actual global reciprocity, namely the original idele-class norm range. -/
theorem ideleClassNorm_range_eq_iInf_characterKernels :
    (_root_.ideleClassNorm K L).range =
      ⨅ χ : Gal(L/K) →* Mˣ, (abelianCharacterConductorialSubgroup K L χ).1 := by
  ext c
  constructor
  · intro hc
    apply Subgroup.mem_iInf.mpr
    intro χ
    change χ (globalNormResidueMonoidHom K L c) = 1
    rw [(globalNormResidueMonoidHom_eq_one_iff K L c).mpr hc, map_one]
  · intro hc
    apply (globalNormResidueMonoidHom_eq_one_iff K L c).mp
    by_contra hne
    obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      Gal(L/K) M hne
    exact hχ (Subgroup.mem_iInf.mp hc χ)

/-- The full conductor of a finite abelian extension is the least common
multiple of all its one-dimensional character conductors. -/
theorem abelianFullConductor_eq_sup_characterConductor :
    (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor =
      Finset.univ.sup (fun χ : Gal(L/K) →* Mˣ =>
        abelianCharacterConductor K L χ) := by
  apply ConductorialSubgroup.fullConductor_eq_finset_sup
    (ideleClassNormConductorialSubgroup (K := K) (L := L))
    (fun χ : Gal(L/K) →* Mˣ => abelianCharacterConductorialSubgroup K L χ)
  change (_root_.ideleClassNorm K L).range = _
  simp only [Finset.mem_univ, iInf_true]
  exact ideleClassNorm_range_eq_iInf_characterKernels K L M

/-- At each finite prime, the extension conductor exponent is the maximum
of the character conductor exponents. -/
theorem abelianFullConductor_finiteExponent_eq_sup_characterConductor
    (v : HeightOneSpectrum (𝓞 K)) :
    (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.finitePart v =
      Finset.univ.sup (fun χ : Gal(L/K) →* Mˣ =>
        (abelianCharacterConductor K L χ).finitePart v) := by
  rw [abelianFullConductor_eq_sup_characterConductor K L M]
  exact Finset.apply_sup_eq_sup_comp
    (fun m : RayClass.Modulus K => m.finitePart v) (fun _ _ => rfl) rfl

open scoped Classical in
/-- The real part of the extension conductor is the union of the real parts
of the character conductors. -/
theorem abelianFullConductor_infinitePart_eq_biUnion_characterConductor :
    (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.infinitePart =
      Finset.univ.biUnion (fun χ : Gal(L/K) →* Mˣ =>
        (abelianCharacterConductor K L χ).infinitePart) := by
  classical
  rw [abelianFullConductor_eq_sup_characterConductor K L M,
    ← Finset.sup_eq_biUnion]
  exact Finset.apply_sup_eq_sup_comp
    (fun m : RayClass.Modulus K => m.infinitePart) (fun _ _ => rfl) rfl

/-- A real place occurs in the extension conductor exactly when some finite
Galois character detects its one-place idelic image. -/
theorem abelianFullConductor_mem_infinitePart_iff_exists_character
    (v : RayClass.RealPlace K) :
    v ∈ (ideleClassNormConductorialSubgroup (K := K) (L := L)).fullConductor.infinitePart ↔
      ∃ χ : Gal(L/K) →* Mˣ, v ∈ (abelianCharacterConductor K L χ).infinitePart := by
  classical
  rw [abelianFullConductor_infinitePart_eq_biUnion_characterConductor K L M]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- A real prime ramifies in the abelian extension exactly when it appears
in the conductor of some one-dimensional character. -/
theorem realRamified_iff_exists_characterConductor
    (v : RayClass.RealPlace K) :
    ¬ v.1.IsUnramifiedIn L ↔
      ∃ χ : Gal(L/K) →* Mˣ, v ∈ (abelianCharacterConductor K L χ).infinitePart :=
  (ClassFieldTheory.abelianFullConductor_mem_infinitePart_iff_realRamified
    (K := K) (L := L) v).symm.trans
      (abelianFullConductor_mem_infinitePart_iff_exists_character K L M v)

end GlobalClassFieldTheory.GlobalClassFields
