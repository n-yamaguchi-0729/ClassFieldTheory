/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SupportedIdeleH2Localization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandOutsideSupport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassRepresentation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.SupportedIdeleExactSequence

/-!
# Prescribed local degree-two classes and the idèle class quotient

Finite and archimedean tensor classes specify a supported idèle class in
cohomology. The quotient induces the corresponding class with coefficients
in `C_L`. For the Herbrand support, exactness identifies the kernel with
the image from the actual extension-field `S`-units.
-/

@[expose] public section

open CategoryTheory NumberField IsDedekindDomain
open CyclicCohomology.ProfiniteCohomology.Herbrand RelativeIdeleGroup.Cohomology
open ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations HilbertRamification
open scoped NumberField TensorProduct

noncomputable section

namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "J" => relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S
local notation "Cₗ" => RelativeIdeleGroup.ClassGroup K L
local notation "U" => SUnitGroup (K := L) (finitePlacesAbove (K := K) (L := L) S)

local instance : MulDistribMulAction Gal(L/K) J :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

local instance : MulDistribMulAction Gal(L/K) Cₗ := ideleClassMulDistribMulAction K L

local instance : MulDistribMulAction Gal(L/K) U :=
  sUnitMulDistribMulAction K L (finitePlacesAbove (K := K) (L := L) S)
    (finitePlacesAbove_isGaloisStable (K := K) (L := L) S)

local notation "A_f" => (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S} ↦
  (HeightOneSpectrum.adicCompletion K (Subtype.val v) ⊗[K] L)ˣ)
local notation "A_∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)

local instance (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

local instance (v : InfinitePlace K) : MulDistribMulAction Gal(L/K) (A_∞ v) :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.Completion)

include S in
/-- The actual supported-idele sequence `S`-units → supported ideles → `C_L`
in the category of integer representations. -/
def supportedIdeleClassShortComplex : ShortComplex (Rep ℤ Gal(L/K)) := by
  let i : U →* J := sUnitToRelativeIdeleSupported (K := K) (L := L) S
  let q : J →* Cₗ := relativeIdeleSupportedToClass (K := K) (L := L) S
  have hi : ∀ (g : Gal(L/K)) (x : U), i (g • x) = g • i x :=
    sUnitToRelativeIdeleSupported_equivariant (K := K) (L := L) S
  have hq : ∀ (g : Gal(L/K)) (y : J), q (g • y) = g • q y :=
    relativeIdeleSupportedToClass_equivariant (K := K) (L := L) S
  have hker : ∀ b : J, q b = 1 ↔ ∃ a : U, i a = b :=
    sUnit_supportedIdele_ideleClass_exact (K := K) (L := L) S
  exact equivariantShortComplex (G := Gal(L/K)) (A := U) (B := J) (C := Cₗ)
    i q hi hq hker

omit [IsGalois K L] in
/-- Supported and principal idèles that generate all idèles give a short exact
coefficient sequence. -/
theorem supportedIdeleClassShortComplex_shortExact
    (hSP : J ⊔ RelativeIdeleGroup.principalSubgroup K L = ⊤) :
    (supportedIdeleClassShortComplex K L S).ShortExact := by
  let i : U →* J := sUnitToRelativeIdeleSupported (K := K) (L := L) S
  let q : J →* Cₗ := relativeIdeleSupportedToClass (K := K) (L := L) S
  have hi : ∀ (g : Gal(L/K)) (x : U), i (g • x) = g • i x :=
    sUnitToRelativeIdeleSupported_equivariant (K := K) (L := L) S
  have hq : ∀ (g : Gal(L/K)) (y : J), q (g • y) = g • q y :=
    relativeIdeleSupportedToClass_equivariant (K := K) (L := L) S
  have hker : ∀ b : J, q b = 1 ↔ ∃ a : U, i a = b :=
    sUnit_supportedIdele_ideleClass_exact (K := K) (L := L) S
  have hinj : Function.Injective i := sUnitToRelativeIdeleSupported_injective S
  have hsurj : Function.Surjective q := relativeIdeleSupportedToClass_surjective S hSP
  change (equivariantShortComplex (G := Gal(L/K)) (A := U) (B := J) (C := Cₗ)
    i q hi hq hker).ShortExact
  exact equivariantShortComplex_shortExact (G := Gal(L/K)) (A := U) (B := J) (C := Cₗ)
    i q hi hq hker hinj hsurj

omit [IsGalois K L] in
/-- The canonical arithmetic support makes the actual coefficient sequence short exact. -/
theorem supportedIdeleClassShortComplex_shortExact_herbrandSupport :
    (supportedIdeleClassShortComplex K L
      (ideleClassHerbrandSupport (K := K) (L := L))).ShortExact :=
  supportedIdeleClassShortComplex_shortExact K L _
    (relativeSupportedAboveHerbrandSupport_sup_principal_eq_top (K := K) (L := L))

omit [IsGalois K L] in
/-- On the canonical support, the kernel of the map to `C_L` in degree two
is the image of the actual `S`-unit cohomology. -/
theorem supportedIdeleClassH2_exact_herbrandSupport :
    (groupCohomology.mapShortComplex₂
      (supportedIdeleClassShortComplex K L
        (ideleClassHerbrandSupport (K := K) (L := L))) 2).Exact :=
  groupCohomology.mapShortComplex₂_exact
    (supportedIdeleClassShortComplex_shortExact_herbrandSupport K L) 2

/-- The actual degree-two tensor cohomology at the finite places in `S` and
all archimedean places. -/
abbrev SupportedLocalH2 : Type :=
  (∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ S},
      groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (A_f v)) 2) ×
    (∀ v : InfinitePlace K,
      groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (A_∞ v)) 2)

/-- On a support containing the ramified places, prescribed local tensor
classes give an additive map to the cohomology of the actual idèle class group. -/
def prescribedSupportedIdeleClassH2
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v) :
    SupportedLocalH2 K L S →+ groupCohomology (standardIdeleClassRep K L) 2 :=
  let H := groupCohomology.functor ℤ Gal(L/K) 2
  ((H.map ((supportedIdeleClassShortComplex K L S).g ≫
    (relativeToStandardIdeleClassRepIso K L).hom)).hom.toAddMonoidHom).comp
      (supportedSPlaceH2LocalizationsEquiv K L S hfin).symm.toAddMonoidHom

/-- The canonical support supplies the unramified condition in the prescribed
class map. Its input is the family of actual tensor cohomology coordinates. -/
abbrev prescribedHerbrandSupportIdeleClassH2 :
    SupportedLocalH2 K L (ideleClassHerbrandSupport (K := K) (L := L)) →+
      groupCohomology (standardIdeleClassRep K L) 2 :=
  prescribedSupportedIdeleClassH2 K L (ideleClassHerbrandSupport (K := K) (L := L))
    (fun v hv => chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := L) v hv)

end GlobalClassFieldTheory.Cohomology
