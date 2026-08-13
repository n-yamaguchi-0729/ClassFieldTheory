#!/usr/bin/env python3
"""Check the public choice boundary of the ClassFieldTheory library.

This is intentionally a static, dependency-free check.  It inventories both
the declaration command that directly contains each use of one of the
configured choice primitives and the public object layer derived from reviewed
essentially-chosen objects.  Uses in comments and strings are ignored.  The
checked-in manifest then turns both inventories into an API contract: adding,
removing, moving, or silently renaming a choice-based public declaration
requires an explicit review.

The parser is conservative rather than an elaborator.  Repository declarations
are top-level Lean commands, so command starts and namespace scopes are enough
to obtain stable fully-qualified names and declaration bodies for this gate.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping

from source_layout import (
    DOCS_ROOT,
    LEAN_ROOT,
    lean_source_files,
    source_inventory,
)


LIBRARY_ROOT = LEAN_ROOT
DEFAULT_MANIFEST = DOCS_ROOT / "choice-audit.json"
SCHEMA_VERSION = 3

CHOICE_PRIMITIVES = (
    "Classical.choose",
    "Classical.choice",
    "Classical.epsilon",
    "Exists.choose",
    "Nonempty.some",
    "Nat.find",
    "Quotient.out",
)

OBJECT_KINDS = {
    "def",
    "abbrev",
    "instance",
    "structure",
    "class",
    "inductive",
    "opaque",
}

# Choice taint is a property of exposed values.  The derived graph therefore
# does not flow through theorem/lemma/axiom commands, generated instances,
# structures, classes, or inductive declarations.
DERIVED_VALUE_KINDS = {
    "def",
    "opaque",
    "abbrev",
}

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)"
    r"(?:(?:@\[[^\]]*\])\s*)*"
    r"(?P<mods>(?:(?:private|protected|noncomputable|unsafe|partial|scoped|local)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|constant)\b"
    r"(?:\s+(?P<name>[^\s:{(\[]+))?"
)
STRUCTURE_FIELD_RE = re.compile(
    r"^[ \t]+(?P<name>[A-Za-z_][A-Za-z0-9_']*)"
    r"(?:\s+|\s*\([^\n)]*\)\s*|\s*\{[^\n}]*\}\s*)*:"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(.+?)\s*$")
SECTION_RE = re.compile(r"^section(?:\s+(.+?))?\s*$")
END_RE = re.compile(r"^end(?:\s+(.+?))?\s*$")

# A following top-level command terminates a declaration command.  Declaration
# starts are handled separately; this list protects the final declaration in a
# file from accidentally absorbing a later `example` or command block.
OTHER_COMMAND_RE = re.compile(
    r"^(?:"
    r"namespace|section|end|example|variable|variables|universe|universes|"
    r"import|open|export|include|omit|attribute|initialize|"
    r"set_option|syntax|macro|elab|command_elab|notation|infix|infixl|infixr|"
    r"prefix|postfix|mutual"
    r")\b"
)

FORBIDDEN_PUBLIC_SUFFIXES = (
    "zHatRepresentation",
    "zHatRepresentationHomeomorph",
    "relativeTowerCosetEquiv",
)

VALID_OBJECT_CLASSIFICATIONS = {
    "internal_choice",
    "result_canonical",
    "essentially_chosen",
}

LOCAL_CONTRACT_PREFIXES = (
    "AbstractClassFieldTheory.",
    "AlgebraicNumberTheory.",
    "ClassFormation.",
    "CyclicCohomology.",
    "HasseArf.",
    "KroneckerWeber.",
    "KummerTheory.",
    "LocalClassFieldTheory.",
    "LocalFieldTheory.",
    "LubinTate.",
    "RamificationTheory.",
    "ValuationTheory.",
)

LEAN_IDENTIFIER_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)

DERIVED_METADATA_FIELDS = (
    "name",
    "kind",
    "file",
    "depends_on",
    "detection",
)

DERIVED_CURATED_FIELDS = (
    "classification",
    "choice_taint_override",
    "witness",
    "spec",
    "independence",
    "note",
)

DEFAULT_DERIVED_NOTE = (
    "A public derived construction whose chosen/choice-visible name "
    "keeps its noncanonical dependency explicit."
)

DIRECT_CURATED_FIELDS = (
    "classification",
    "witness",
    "spec",
    "independence",
    "choice_visible",
    "quotient_lift_exception",
    "note",
)


# This is the reviewed recovery seed for the current public boundary.  Keeping
# the complete object partition here makes `--initialize-manifest` a formal
# initializer: a newly discovered object cannot be silently approved merely by
# deleting and regenerating the JSON manifest.
REVIEWED_DIRECT_CANONICAL: dict[
    str, tuple[tuple[str, ...], tuple[str, ...]]
] = {
    "AlgebraicNumberTheory.PowerResidueSymbols.rootsOfUnityReductionEquiv": (
        (
            "AlgebraicNumberTheory.PowerResidueSymbols."
            "rootsOfUnityReductionEquiv_apply",
        ),
        (
            "AlgebraicNumberTheory.PowerResidueSymbols."
            "rootsOfUnityReductionEquiv_apply",
        ),
    ),
    "AlgebraicNumberTheory.Valuations.finiteNormExtension_archimedean_finite_extension": (
        (
            "AlgebraicNumberTheory.Valuations."
            "FiniteNormExtensionFiniteExtensionResult.norm_formula",
        ),
        (
            "AlgebraicNumberTheory.Valuations."
            "FiniteNormExtensionFiniteExtensionResult.ext_unique",
        ),
    ),
    "ClassFormation.DegreeData.frobeniusExponent": (
        ("ClassFormation.DegreeData.extensionNormalizedDegree_frobenius_eq_pow",),
        ("ClassFormation.DegreeData.frobeniusExponent_unique",),
    ),
    "ClassFormation.DegreeData.frobeniusFixedFieldAction": (
        ("ClassFormation.DegreeData.frobeniusFixedFieldAction_coe_of_mk",),
        (
            "ClassFormation.DegreeData."
            "frobeniusFixedFieldAction_eq_conjugateStableAction",
        ),
    ),
    "ClassFormation.orbitQuotientEquivDoubleCoset": (
        ("ClassFormation.orbitQuotientEquivDoubleCoset_mk",),
        ("ClassFormation.orbitQuotientEquivDoubleCoset_symm_mk",),
    ),
    "CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandH0.liftOn": (
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "HerbrandH0.liftOn_mk",
        ),
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "HerbrandH0.liftOn_mk",
        ),
    ),
    "CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandHMinusOne.liftOn": (
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "HerbrandHMinusOne.liftOn_mk",
        ),
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "HerbrandHMinusOne.liftOn_mk",
        ),
    ),
    "CyclicCohomology.ProfiniteCohomology.Herbrand.rightRegularCyclicIndex": (
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "rightRegularCyclicIndex_spec",
        ),
        (
            "CyclicCohomology.ProfiniteCohomology.Herbrand."
            "rightRegularCyclicIndex_eq_of_repr",
        ),
    ),
    "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteConductorExponent": (
        (
            "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup."
            "narrowFiniteConductorExponent_spec",
        ),
        (
            "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup."
            "narrowFiniteConductorExponent_le",
        ),
    ),
    "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.narrowFiniteLocalConductorExponent": (
        (
            "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup."
            "narrowFiniteLocalConductorExponent_spec",
        ),
        (
            "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup."
            "narrowFiniteLocalConductorExponent_le",
        ),
    ),
    "GlobalClassFieldTheory.GlobalClassFields.ideleClassNormLocalHigherUnitExponent": (
        (
            "GlobalClassFieldTheory.GlobalClassFields."
            "ideleClassNormLocalHigherUnitExponent_spec",
        ),
        (
            "GlobalClassFieldTheory.GlobalClassFields."
            "ideleClassNormLocalHigherUnitExponent_min",
        ),
    ),
    "GlobalClassFieldTheory.GlobalClassFields.ordinaryNormClassFieldSubextension": (
        (
            "GlobalClassFieldTheory.GlobalClassFields."
            "ordinaryNormClassFieldSubextension_normSubgroup",
        ),
        ("ClassFormation.FiniteAbelianSubextension.normSubgroupMap_injective",),
    ),
    "GlobalClassFieldTheory.IdealClassFieldTheory.secondSmallHilbertClassFieldSubextension": (
        (
            "GlobalClassFieldTheory.IdealClassFieldTheory."
            "secondSmallHilbertClassFieldSubextension_normSubgroup",
        ),
        ("ClassFormation.FiniteAbelianSubextension.normSubgroupMap_injective",),
    ),
    "LocalClassFieldTheory.ambientEmbeddedPrimeTarget": (
        ("LocalClassFieldTheory.ambientEmbeddedPrimeTarget_eq",),
        ("LocalClassFieldTheory.ambientEmbeddedPrimeTarget_eq",),
    ),
    "LocalClassFieldTheory.localConductorExponent": (
        ("LocalClassFieldTheory.localConductorExponent_spec",),
        ("LocalClassFieldTheory.localConductorExponent_min",),
    ),
    "LocalClassFieldTheory.lubinTateUniformizerDiagonalAutomorphism": (
        (
            "LocalClassFieldTheory."
            "lubinTateUniformizerDiagonalAutomorphism_restrict_level",
        ),
        (
            "LocalClassFieldTheory."
            "lubinTateUniformizerDiagonalAutomorphism_unique",
        ),
    ),
    "LocalClassFieldTheory.rightCosetExtension": (
        ("LocalClassFieldTheory.rightCosetExtension_eq_of_mk",),
        ("LocalClassFieldTheory.rightCosetExtension_eq_of_mk",),
    ),
    "LocalClassFieldTheory.rightCosetExtensionEquiv": (
        ("LocalClassFieldTheory.rightCosetExtensionEquiv_apply",),
        ("LocalClassFieldTheory.rightCosetExtensionEquiv_apply",),
    ),
    "LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.principalUnitResidueDegree": (
        (
            "LocalFieldTheory.DiscreteValuationField.CompleteDVF."
            "higherPrincipalUnitGroup."
            "residueCharacteristic_prime_and_card_eq_pow_residueDegree",
        ),
        (
            "LocalFieldTheory.DiscreteValuationField.CompleteDVF."
            "higherPrincipalUnitGroup.principalUnitResidueDegree_unique",
        ),
    ),
    "LocalFieldTheory.DiscreteValuationField.CompleteDVF.uniformizerValueExponent": (
        (
            "LocalFieldTheory.DiscreteValuationField.CompleteDVF."
            "uniformizerValueUnit_zpow_uniformizerValueExponent_eq_fieldUnitValueUnit",
        ),
        (
            "LocalFieldTheory.DiscreteValuationField.CompleteDVF."
            "uniformizerValueUnit_zpow_inj",
        ),
    ),
    "LubinTate.EqualCharacteristic.equalCharacteristicAdditiveExponentIndex": (
        ("LubinTate.EqualCharacteristic.equalCharacteristicAdditiveExponentIndex_spec",),
        ("LubinTate.EqualCharacteristic.equalCharacteristicAdditiveExponentIndex_min",),
    ),
    "LubinTate.EqualCharacteristic.equalCharacteristicCompletedUnramifiedFixedCoeff": (
        (
            "LubinTate.EqualCharacteristic."
            "algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff",
        ),
        (
            "LubinTate.EqualCharacteristic."
            "algebraMap_equalCharacteristicCompletedUnramifiedFixedCoeff",
        ),
    ),
    "LubinTate.EqualCharacteristic.powerSeriesEquivLaurentInteger": (
        ("LubinTate.EqualCharacteristic.powerSeriesEquivLaurentInteger_coe",),
        ("LubinTate.EqualCharacteristic.powerSeriesEquivLaurentInteger_coe",),
    ),
    "LubinTate.SameUniformizer.correctionCoefficient": (
        ("LubinTate.SameUniformizer.correctionCoefficient_spec",),
        ("LubinTate.SameUniformizer.correctionCoefficient_unique",),
    ),
    "LubinTate.Valuations.remainder": (
        ("LubinTate.Valuations.remainder_step",),
        ("LubinTate.Valuations.coeff_remainder_unique",),
    ),
    "LubinTate.equalCharacteristicLubinTateLevelCompleteDVF": (
        ("LubinTate.equalCharacteristicLubinTateLevelCompleteDVF_hasExtension",),
        (
            "LubinTate."
            "equalCharacteristicLubinTateLevelCompleteDVF_hasUniqueValuationExtension",
        ),
    ),
    "LubinTate.padicChangedUniformizerCorrectionCoefficient": (
        ("LubinTate.padicChangedUniformizerCorrectionCoefficient_spec",),
        ("LubinTate.existsUnique_padicChangedUniformizerCoefficient",),
    ),
    "LubinTate.standardLubinTateChangedLevelCompositumCompleteDVF": (
        (
            "LubinTate."
            "standardLubinTateChangedLevelCompositumCompleteDVF_hasExtension",
        ),
        (
            "LubinTate."
            "standardLubinTateChangedLevelCompositumCompleteDVF_hasUniqueValuationExtension",
        ),
    ),
    "LubinTate.standardLubinTateLevelCompleteDVF": (
        ("LubinTate.standardLubinTateLevelCompleteDVF_hasExtension",),
        (
            "LubinTate."
            "standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension",
        ),
    ),
    "RayClass.idealNormLiftedModulusExponent": (
        ("RayClass.localHigherUnitGroup_idealNormLiftedModulusExponent_le",),
        ("RayClass.idealNormLiftedModulusExponent_min",),
    ),
}

REVIEWED_DIRECT_INTERNAL: dict[
    str, tuple[tuple[str, ...], tuple[str, ...]]
] = {
    "LocalClassFieldTheory.ambientEmbeddedPrimeSymbolProperty": (
        ("LocalClassFieldTheory.ambientEmbeddedPrimeWitness_symbol",),
        ("proof_irrel_heq",),
    ),
    "LocalFieldTheory.DiscreteValuationField.WithZeroValuation.rankOneOfUnitsIsCyclic": (
        (
            "LocalFieldTheory.DiscreteValuationField.WithZeroValuation."
            "rankOneOfUnitsIsCyclic",
        ),
        ("proof_irrel_heq",),
    ),
}

REVIEWED_DIRECT_ESSENTIAL = frozenset(
    {
        "AlgebraicNumberTheory.Valuations.henselFactorization_chosenNextPrefixState_of_mem_span",
        "ClassFormation.DegreeData.chosenDegreeOneFrobeniusElement",
        "ClassFormation.DegreeData.chosenDegreeOneFrobeniusLiftOfTotallyRamified",
        "ClassFormation.DegreeData.chosenFiniteReciprocityFrobeniusLift",
        "ClassFormation.DegreeData.chosenUnramifiedFrobeniusLift",
        "ClassFormation.ValuationData.chosenPrimeElement",
        "CyclicCohomology.chosenPermutationOrbitRepresentative",
        "CyclicCohomology.chosenPermutationOrbitTransport",
        "FiniteIdeleGroup.chosenLocalOrderSection",
        "GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerChosenBasePlaces",
        "GlobalClassFieldTheory.ClassFieldAxiom.sUnitKummerCoordinatePlace",
        "GlobalClassFieldTheory.GlobalClassFields.ConductorialSubgroup.chosenDefiningModulus",
        "GlobalClassFieldTheory.GlobalClassFields.bigHilbertClassFieldCompatibleEmbedding",
        "GlobalClassFieldTheory.GlobalClassFields.closedFiniteIndexClassFieldCompatibleEmbedding",
        "GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfieldSeparableClosureEmbedding",
        "GlobalClassFieldTheory.Reciprocity.numberFieldEmbeddingComparisonAutomorphism",
        "GlobalClassFieldTheory.Reciprocity.numberFieldTowerFinitePadicAuxiliaryLocalGlobalRepresentative",
        "GlobalClassFieldTheory.Reciprocity.rationalCyclotomicLevelPrimitiveRoot",
        "KroneckerWeber.kroneckerWeberCompositumPrimeAbove",
        "KroneckerWeber.kroneckerWeberGlobalValuedCompositumEmbeddingData",
        "KroneckerWeber.kroneckerWeberLocalCyclotomicData",
        "KummerTheory.chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod",
        "KummerTheory.chosenFiniteKummerRadicalDatum",
        "KummerTheory.chosenFiniteKummerRadicalRepresentative",
        "KummerTheory.chosenFiniteSupportCoefficient",
        "KummerTheory.chosenFullSUnitKummerExtensionGaloisEquivSUnitQuotient",
        "KummerTheory.chosenSimpleKummerRoot",
        "KummerTheory.chosenUnitFiniteSupport",
        "LocalClassFieldTheory.ambientEmbeddedPrimeWitness",
        "LocalClassFieldTheory.chosenFilteredLiftCorrectionSequence",
        "LocalClassFieldTheory.chosenFilteredLiftStateSequence",
        "LocalClassFieldTheory.chosenMaximalKummerGaloisEquivPowerQuotient",
        "LocalClassFieldTheory.chosenNormQuotientEquivZModResidueFinrank_of_fieldPrincipalUnits_zero_le",
        "LocalClassFieldTheory.chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrection",
        "LocalClassFieldTheory.chosenValuationOneUnitOfRingEquiv",
        "LocalClassFieldTheory.inducedRightCosetCoordinates",
        "LocalClassFieldTheory.rightCosetCoefficient",
        "LocalClassFieldTheory.rightCosetCompletionAlgEquiv",
        "LocalClassFieldTheory.rightCosetCompletionUnitsEquiv",
        "LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.chosenPadicModuleContinuousAddEquivZModProdFinPi",
        "LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.chosenPrincipalUnitPadicUniformizer",
        "LocalFieldTheory.DiscreteValuationField.LocalField.chosenFieldUnitsStructure_equalCharacteristic",
        "LocalFieldTheory.DiscreteValuationField.LocalField.chosenFieldUnitsStructure_mixedCharacteristic",
        "LocalFieldTheory.DiscreteValuationField.LocalField.chosenFirstPrincipalUnitStructure_equalCharacteristic",
        "LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitAlgebraicData",
        "LocalFieldTheory.DiscreteValuationField.LocalField.chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation",
        "LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv",
        "LocalFieldTheory.DiscreteValuationField.chosenIwasawaIndexEquivNat",
        "LocalFieldTheory.IsNonarchimedeanLocalField.chosenLocalUniformizer",
        "LocalFieldTheory.IsNonarchimedeanLocalField.chosenValuationMapSection",
        "LocalFieldTheory.chosenIntegerRingUniformizer",
        "LocalFieldTheory.chosenLocalExtensionCompleteDVF",
        "LubinTate.EqualCharacteristic.chosenEqualCharacteristicChangedPrimitiveRoot",
        "LubinTate.EqualCharacteristic.chosenEqualCharacteristicLubinTatePrimitiveRoot",
        "LubinTate.EqualCharacteristic.chosenEqualCharacteristicSemilinearCoefficient",
        "LubinTate.EqualCharacteristic.chosenEqualCharacteristicSemilinearLeadingCoefficient",
        "LubinTate.SameUniformizer.normalizedDefectCoefficient",
        "LubinTate.Valuations.chosenHigherUnitCoeff",
        "LubinTate.Valuations.residueRepresentativeSystemOf.ofChoice",
        "LubinTate.chosenStandardLubinTatePrimitiveRoot",
        "LubinTate.padicChangedUniformizerLinearCoefficient",
        "LubinTate.padicCompletedLevelCompleteDVF",
        "LubinTate.standardLubinTateUnitParameterChosenRepresentative",
        "RamificationTheory.HilbertRamification.FiniteGaloisLevel.chosenIntegralClosureTarget",
        "RamificationTheory.HilbertRamification.Higher.chosenRamificationGeneratorOfUniqueExtension",
        "RamificationTheory.HilbertRamification.Higher.dvfUniformizerQuotientUnit",
        "RayClass.chosenModulusInside",
        "chosenFinitePlaceCompletionIntegralUniformizer",
        "chosenInfinitePlaceAbove",
        "chosenRelativeBasisIntegralScale",
        "chosenScaledRelativeIntegerLatticeAnnihilatorData",
        "rightCosetCompletionIntegersRingEquivLocalized",
        "rightCosetCompletionRingEquivLocalized",
    }
)

REVIEWED_DERIVED_EXTERNAL_SPECS = {
    "ChosenFinitePlaceBaseCompletion": ("finitePlaceCompletionRingEquiv_mem_integers_iff",),
    "ClassFormation.DegreeData.chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified": (
        "ClassFormation.DegreeData."
        "frobeniusExponent_chosenDegreeOneFrobeniusLiftOfFiniteTotallyRamified",
    ),
    "CyclicCohomology.chosenNormalBasisIntegerLattice": (
        "CyclicCohomology.chosenNormalBasisIntegerLattice_eq_span",
    ),
    "CyclicCohomology.chosenNormalBasisPrincipalUnitSuccSubgroup": (
        "CyclicCohomology.mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iff",
    ),
    "GlobalClassFieldTheory.GlobalClassFields.chosenFinitePlaceNormQuotientEquivDecompositionGroup": (
        "GlobalClassFieldTheory.GlobalClassFields."
        "chosenFinitePlaceNormQuotientEquivDecompositionGroup_mk",
    ),
    "GlobalClassFieldTheory.GlobalClassFields.ideleClassNormChosenFinitePlaceLocalConductorExponent": (
        "GlobalClassFieldTheory.GlobalClassFields."
        "ideleClassNormLocalHigherUnitExponent_eq_localConductorExponent",
    ),
    "LocalClassFieldTheory.chosenNormalBasisCoordinateMaximalSubmodule": (
        "LocalClassFieldTheory.mem_chosenNormalBasisCoordinateMaximalSubmodule_iff",
    ),
    "LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap": (
        "LocalClassFieldTheory.chosenNormalBasisIntegerUnitsQuotientMap_apply",
    ),
    "LocalClassFieldTheory.chosenNormalBasisPiResidueInverseIndexAddEquiv": (
        "LocalClassFieldTheory.chosenNormalBasisPiResidueInverseIndexAddEquiv_apply",
    ),
    "LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct": (
        "LocalClassFieldTheory.chosenNormalBasisPrincipalUnitCorrectionProduct_succ",
    ),
    "LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupInclusion": (
        "LocalClassFieldTheory.chosenNormalBasisPrincipalUnitSubgroupInclusion_apply",
    ),
    "LocalClassFieldTheory.chosenPrincipalUnitsNormOfUnramifiedValuationOfIsIntegralClosureApproxCorrectionSeq": (
        "LocalClassFieldTheory."
        "principalUnitsCorrectionProduct_approxCorrectionSeqOfIsIntegralClosure",
    ),
    "LocalClassFieldTheory.localTensorUnitsEquivChosenCoordinates": (
        "LocalClassFieldTheory.localTensorDetNorm_eq_prod_chosenCoordinates",
    ),
    "chosenFinitePlaceExtension": ("chosenFinitePlaceExtension",),
}

EXPECTED_REVIEWED_DIRECT_COUNT = 215
EXPECTED_REVIEWED_OBJECT_COUNT = 105
EXPECTED_REVIEWED_PROOF_COUNT = 110
EXPECTED_REVIEWED_DERIVED_COUNT = 85
EXPECTED_REVIEWED_CANONICAL_COUNT = 30
EXPECTED_REVIEWED_ESSENTIAL_COUNT = 73
EXPECTED_REVIEWED_INTERNAL_COUNT = 2


@dataclass(frozen=True)
class Scope:
    kind: str
    names: tuple[str, ...] = ()


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    file: str
    line: int
    private: bool
    body: str

    @property
    def uses(self) -> tuple[str, ...]:
        found: list[str] = []
        for primitive in CHOICE_PRIMITIVES:
            pattern = re.escape(primitive) + r"(?![A-Za-z0-9_'])"
            if re.search(pattern, self.body):
                found.append(primitive)
        return tuple(found)

    @property
    def is_object(self) -> bool:
        return self.kind in OBJECT_KINDS


@dataclass(frozen=True)
class DerivedChosenObject:
    """Freshly scanned metadata for a non-direct public chosen object."""

    declaration: Declaration
    depends_on: tuple[str, ...]
    detection: tuple[str, ...]

    @property
    def name(self) -> str:
        return self.declaration.name

    def manifest_metadata(self) -> dict[str, object]:
        return {
            "name": self.declaration.name,
            "kind": self.declaration.kind,
            "file": self.declaration.file,
            "depends_on": list(self.depends_on),
            "detection": list(self.detection),
        }


def strip_comments_and_strings(text: str) -> str:
    """Blank Lean comments and strings while preserving positions and lines."""

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and nxt:
                out.extend((" ", "\n" if nxt == "\n" else " "))
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if ch == "-" and nxt == "-":
            out.extend((" ", " "))
            i += 2
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def namespace_prefix(scopes: list[Scope]) -> list[str]:
    result: list[str] = []
    for scope in scopes:
        if scope.kind == "namespace":
            result.extend(scope.names)
    return result


def qualify(short_name: str, scopes: list[Scope]) -> str:
    if short_name.startswith("_root_."):
        return short_name.removeprefix("_root_.")
    prefix = ".".join(namespace_prefix(scopes))
    if not prefix:
        return short_name
    if short_name == prefix or short_name.startswith(prefix + "."):
        return short_name
    return f"{prefix}.{short_name}"


def pop_scope(scopes: list[Scope], raw_name: str | None) -> None:
    if not scopes:
        return
    if raw_name is None or not raw_name.strip():
        scopes.pop()
        return
    target = raw_name.strip().split()[0]
    for index in range(len(scopes) - 1, -1, -1):
        scope = scopes[index]
        if target in scope.names or target == ".".join(scope.names):
            del scopes[index:]
            return
    # Lean accepts named section ends as well.  If static recovery cannot match
    # the name, dropping the innermost scope is safer than leaking it forward.
    scopes.pop()


def recover_name(
    raw_name: str | None,
    kind: str,
    clean_lines: list[str],
    line_index: int,
    relative_file: str,
) -> str:
    if raw_name and raw_name[0] not in ":({[":
        return raw_name.rstrip(",")
    if kind == "instance":
        return f"_anonymous_instance@{relative_file}:{line_index + 1}"
    for candidate_index in range(line_index + 1, min(len(clean_lines), line_index + 6)):
        stripped = clean_lines[candidate_index].strip()
        if not stripped:
            continue
        token = stripped.split(maxsplit=1)[0].rstrip(",")
        if token and token not in {"where", ":=", "|"} and token[0] not in ":({[":
            return token
    return f"_anonymous_{kind}@{relative_file}:{line_index + 1}"


def is_top_level(line: str) -> bool:
    return bool(line) and not line[0].isspace()


def scan_source(source: str, relative_file: str) -> list[Declaration]:
    clean = strip_comments_and_strings(source)
    clean_lines = clean.splitlines(keepends=True)

    scopes: list[Scope] = []
    starts: list[tuple[int, re.Match[str], str]] = []
    boundaries: set[int] = set()

    for line_index, line_with_end in enumerate(clean_lines):
        line = line_with_end.rstrip("\r\n")
        if not is_top_level(line):
            continue
        stripped = line.strip()

        declaration_match = DECL_RE.match(line)
        if declaration_match and not declaration_match.group("indent"):
            raw_name = recover_name(
                declaration_match.group("name"),
                declaration_match.group("kind"),
                [item.rstrip("\r\n") for item in clean_lines],
                line_index,
                relative_file,
            )
            starts.append((line_index, declaration_match, qualify(raw_name, scopes)))
            boundaries.add(line_index)
            continue

        namespace_match = NAMESPACE_RE.match(stripped)
        if namespace_match:
            names = tuple(item for item in namespace_match.group(1).split() if item)
            scopes.append(Scope("namespace", names))
            boundaries.add(line_index)
            continue
        section_match = SECTION_RE.match(stripped)
        if section_match:
            names = tuple(item for item in (section_match.group(1) or "").split() if item)
            scopes.append(Scope("section", names))
            boundaries.add(line_index)
            continue
        end_match = END_RE.match(stripped)
        if end_match:
            pop_scope(scopes, end_match.group(1))
            boundaries.add(line_index)
            continue
        if OTHER_COMMAND_RE.match(stripped):
            boundaries.add(line_index)

    ordered_boundaries = sorted(boundaries | {len(clean_lines)})
    declarations: list[Declaration] = []
    for line_index, match, qualified_name in starts:
        end_index = next(index for index in ordered_boundaries if index > line_index)
        modifiers = set(match.group("mods").split())
        declarations.append(
            Declaration(
                name=qualified_name,
                kind=match.group("kind"),
                file=relative_file,
                line=line_index + 1,
                private="private" in modifiers or "local" in modifiers,
                body="".join(clean_lines[line_index:end_index]),
            )
        )
    return declarations


def scan_file(path: Path) -> list[Declaration]:
    source = path.read_text(encoding="utf-8", errors="replace")
    return scan_source(source, path.relative_to(LIBRARY_ROOT).as_posix())


def lean_files() -> Iterable[Path]:
    yield from lean_source_files()


def scan_library() -> tuple[list[Declaration], list[Declaration]]:
    all_declarations = [declaration for path in lean_files() for declaration in scan_file(path)]
    public_choice = [
        declaration
        for declaration in all_declarations
        if not declaration.private and declaration.uses
    ]
    return all_declarations, public_choice


def public_object_declarations(
    declarations: Iterable[Declaration],
) -> dict[str, Declaration]:
    """Return value-bearing public commands used by derived-choice analysis."""

    return {
        declaration.name: declaration
        for declaration in declarations
        if not declaration.private and declaration.kind in DERIVED_VALUE_KINDS
    }


def declaration_dependency_graph(
    declarations: Iterable[Declaration],
) -> dict[str, tuple[str, ...]]:
    """Resolve syntactic references between known public object declarations.

    This deliberately does not treat arbitrary tokens containing the English
    word ``Choice`` as dependencies.  A token contributes an edge only when it
    resolves uniquely to a public declaration in the scanned library.
    """

    objects = public_object_declarations(declarations)
    by_leaf: dict[str, list[str]] = {}
    for name in objects:
        by_leaf.setdefault(name.rsplit(".", 1)[-1], []).append(name)

    def resolve(owner: str, token: str) -> str | None:
        if token in objects:
            return token

        namespace = owner.split(".")[:-1]
        for prefix_length in range(len(namespace), -1, -1):
            candidate = ".".join(namespace[:prefix_length] + [token])
            if candidate in objects:
                return candidate

        if "." in token:
            candidates = [
                name for name in objects if name.endswith("." + token)
            ]
        else:
            candidates = by_leaf.get(token, [])
        return candidates[0] if len(candidates) == 1 else None

    graph: dict[str, tuple[str, ...]] = {}
    for declaration in objects.values():
        dependencies = {
            resolved
            for token in LEAN_IDENTIFIER_RE.findall(declaration.body)
            if (resolved := resolve(declaration.name, token)) is not None
            and resolved != declaration.name
        }
        graph[declaration.name] = tuple(sorted(dependencies))
    return graph


def has_chosen_marker(name: str) -> bool:
    """A strong marker: unlike bare English ``Choice``, ``chosen`` is semantic."""

    return "chosen" in name.lower()


def choice_taint_is_overridden(entry: Mapping[str, object] | None) -> bool:
    """Whether review explicitly proves that a derived boundary stops taint."""

    if not entry or entry.get("choice_taint_override") is not True:
        return False
    return entry.get("classification") in {"internal_choice", "result_canonical"}


def derived_chosen_inventory(
    declarations: list[Declaration],
    public_choice: list[Declaration],
    direct_entries_by_name: Mapping[str, Mapping[str, object]],
    curated_derived_by_name: Mapping[str, Mapping[str, object]] | None = None,
) -> tuple[list[DerivedChosenObject], set[str]]:
    """Compute the reviewed public derived-choice family and its taint set.

    Direct ``essentially_chosen`` objects are the local syntactic roots.
    Non-direct names containing ``chosen`` are also roots: this accounts for
    choices implemented behind imported APIs (for example Mathlib's normal
    basis).  A bare ``choice`` marker joins the family only when an actual
    declaration dependency reaches a tainted root; this avoids classifying
    combinatorial helpers merely because their English name says ``Choice``.

    The manifest may additionally keep an unmarked derived object under
    explicit review.  Unmarked value declarations are not pulled in merely
    because a proof field or type-level argument mentions a chosen object;
    that would confuse logical evidence with an exposed chosen value.
    """

    curated = curated_derived_by_name or {}
    objects = public_object_declarations(declarations)
    direct_names = {
        declaration.name for declaration in public_choice if declaration.is_object
    }
    graph = declaration_dependency_graph(declarations)

    direct_taint = {
        name
        for name in direct_names
        if direct_entries_by_name.get(name, {}).get("classification")
        == "essentially_chosen"
    }
    reviewed_curated = {
        name
        for name, entry in curated.items()
        if entry.get("note") != DEFAULT_DERIVED_NOTE
    }
    selected = {
        name
        for name in objects
        if name not in direct_names
        and (has_chosen_marker(name) or name in reviewed_curated)
    }
    tainted = set(direct_taint)
    # A strong public marker is a choice root even when the actual primitive is
    # hidden in an imported construction.
    for name in selected:
        if has_chosen_marker(name) and not choice_taint_is_overridden(curated.get(name)):
            tainted.add(name)

    changed = True
    while changed:
        changed = False
        for name in sorted(objects):
            if name in direct_names:
                continue
            tainted_dependencies = set(graph.get(name, ())) & tainted
            if (
                name in selected
                and tainted_dependencies
                and name not in tainted
                and not choice_taint_is_overridden(curated.get(name))
            ):
                tainted.add(name)
                changed = True

    result: list[DerivedChosenObject] = []
    for name in sorted(selected):
        declaration = objects.get(name)
        if declaration is None or name in direct_names:
            continue
        dependencies = tuple(
            sorted(set(graph.get(name, ())) & tainted)
        )
        detection: list[str] = []
        if has_choice_marker(name):
            detection.append("name_marker")
        if any(dependency in direct_taint for dependency in dependencies):
            detection.append("direct_essential_dependency")
        if any(dependency in selected for dependency in dependencies):
            detection.append("derived_essential_dependency")
        if has_chosen_marker(name) and not dependencies:
            detection.append("external_or_opaque_choice_source")
        if name in reviewed_curated and not has_choice_marker(name):
            detection.append("curated_dependency")
        result.append(
            DerivedChosenObject(
                declaration=declaration,
                depends_on=dependencies,
                detection=tuple(detection),
            )
        )
    return result, tainted


def inventory_key(declaration: Declaration) -> tuple[str, str, str, tuple[str, ...]]:
    return declaration.name, declaration.kind, declaration.file, declaration.uses


def manifest_key(entry: dict[str, object]) -> tuple[str, str, str, tuple[str, ...]]:
    return (
        str(entry.get("name", "")),
        str(entry.get("kind", "")),
        str(entry.get("file", "")),
        tuple(str(item) for item in entry.get("uses", [])),
    )


def display_key(key: tuple[str, str, str, tuple[str, ...]]) -> str:
    name, kind, file, uses = key
    return f"{kind} {name} ({file}; {', '.join(uses)})"


def derived_inventory_key(
    item: DerivedChosenObject,
) -> tuple[str, str, str, tuple[str, ...], tuple[str, ...]]:
    declaration = item.declaration
    return (
        declaration.name,
        declaration.kind,
        declaration.file,
        item.depends_on,
        item.detection,
    )


def derived_manifest_key(
    entry: Mapping[str, object],
) -> tuple[str, str, str, tuple[str, ...], tuple[str, ...]]:
    return (
        str(entry.get("name", "")),
        str(entry.get("kind", "")),
        str(entry.get("file", "")),
        tuple(str(item) for item in entry.get("depends_on", [])),
        tuple(str(item) for item in entry.get("detection", [])),
    )


def display_derived_key(
    key: tuple[str, str, str, tuple[str, ...], tuple[str, ...]],
) -> str:
    name, kind, file, dependencies, detection = key
    return (
        f"{kind} {name} ({file}; depends_on=[{', '.join(dependencies)}]; "
        f"detection=[{', '.join(detection)}])"
    )


def validate_manifest_shape(entries: list[dict[str, object]]) -> list[str]:
    errors: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        name = str(entry.get("name", ""))
        kind = str(entry.get("kind", ""))
        role = str(entry.get("role", ""))
        if not name:
            errors.append("manifest entry has no declaration name")
            continue
        if name in seen:
            errors.append(f"duplicate manifest entry: {name}")
        seen.add(name)
        expected_role = "object" if kind in OBJECT_KINDS else "proof_only"
        if role != expected_role:
            errors.append(f"{name}: role must be {expected_role!r}, got {role!r}")
        if role != "object":
            if "classification" in entry:
                errors.append(f"{name}: proof-only entry must not claim an object classification")
            continue

        classification = str(entry.get("classification", ""))
        if classification not in VALID_OBJECT_CLASSIFICATIONS:
            errors.append(f"{name}: invalid object classification {classification!r}")
        for field in ("witness", "spec"):
            values = entry.get(field)
            if not isinstance(values, list) or not all(isinstance(item, str) and item for item in values):
                errors.append(f"{name}: object entry requires string list {field!r}")
        witness = entry.get("witness")
        if isinstance(witness, list) and not witness:
            errors.append(f"{name}: object entry requires at least one witness/source declaration")
        independence = entry.get("independence")
        if not isinstance(independence, list) or not all(isinstance(item, str) and item for item in independence):
            errors.append(f"{name}: object entry requires string list 'independence'")
        if classification == "result_canonical":
            if not entry.get("spec"):
                errors.append(f"{name}: result-canonical choice requires a specification declaration")
            if not independence:
                errors.append(f"{name}: result-canonical choice requires an independence/uniqueness declaration")
        if "choice_visible" in entry and not isinstance(entry.get("choice_visible"), bool):
            errors.append(f"{name}: 'choice_visible' must be boolean when present")
        if entry.get("choice_visible") is True and classification != "essentially_chosen":
            errors.append(
                f"{name}: 'choice_visible' is only valid for an essentially-chosen "
                "legacy public name"
            )
        if entry.get("quotient_lift_exception") is True and classification != "result_canonical":
            errors.append(f"{name}: quotient-lift exceptions must be result-canonical")
    return errors


def validate_derived_manifest_shape(
    entries: list[dict[str, object]],
    direct_entries: list[dict[str, object]],
) -> list[str]:
    """Validate curated fields without weakening the direct manifest contract."""

    errors: list[str] = []
    seen: set[str] = set()
    direct_names = {str(entry.get("name", "")) for entry in direct_entries}
    for entry in entries:
        name = str(entry.get("name", ""))
        kind = str(entry.get("kind", ""))
        if not name:
            errors.append("derived manifest entry has no declaration name")
            continue
        if name in seen:
            errors.append(f"duplicate derived manifest entry: {name}")
        seen.add(name)
        if name in direct_names:
            errors.append(f"{name}: direct declaration must not be repeated as derived")
        if kind not in OBJECT_KINDS:
            errors.append(f"{name}: derived entry kind {kind!r} is not object-producing")

        for field in ("depends_on", "detection", "witness", "spec", "independence"):
            values = entry.get(field)
            if not isinstance(values, list) or not all(
                isinstance(item, str) and item for item in values
            ):
                errors.append(f"{name}: derived entry requires string list {field!r}")
        classification = str(entry.get("classification", ""))
        if classification not in VALID_OBJECT_CLASSIFICATIONS:
            errors.append(f"{name}: invalid derived classification {classification!r}")

        override = entry.get("choice_taint_override", False)
        if not isinstance(override, bool):
            errors.append(f"{name}: 'choice_taint_override' must be boolean")
        if classification == "essentially_chosen" and override is True:
            errors.append(
                f"{name}: essentially-chosen derived objects cannot stop choice taint"
            )
        if classification == "essentially_chosen":
            if not entry.get("witness"):
                errors.append(
                    f"{name}: essentially-chosen derived object requires a witness/source declaration"
                )
            detection = entry.get("detection", [])
            if (
                isinstance(detection, list)
                and "external_or_opaque_choice_source" in detection
                and not entry.get("spec")
            ):
                errors.append(
                    f"{name}: external essentially-chosen root requires a public specification declaration"
                )
        if classification in {"internal_choice", "result_canonical"}:
            if override is not True:
                errors.append(
                    f"{name}: {classification} derived boundary requires explicit "
                    "'choice_taint_override': true"
                )
            if not entry.get("independence"):
                errors.append(
                    f"{name}: {classification} derived boundary requires "
                    "independence/uniqueness evidence"
                )
        if classification == "result_canonical" and not entry.get("spec"):
            errors.append(
                f"{name}: result-canonical derived boundary requires a specification declaration"
            )
        note = entry.get("note")
        if not isinstance(note, str) or not note.strip():
            errors.append(f"{name}: derived entry requires a nonempty rationale 'note'")
    return errors


def validate_reviewed_totals(
    direct_entries: list[dict[str, object]],
    derived_entries: list[dict[str, object]],
) -> list[str]:
    """Keep the recovered review matrix itself under contract."""

    objects = [entry for entry in direct_entries if entry.get("role") == "object"]
    proofs = [entry for entry in direct_entries if entry.get("role") == "proof_only"]
    counts = {
        classification: sum(
            entry.get("classification") == classification for entry in objects
        )
        for classification in VALID_OBJECT_CLASSIFICATIONS
    }
    expected_counts = {
        "result_canonical": EXPECTED_REVIEWED_CANONICAL_COUNT,
        "essentially_chosen": EXPECTED_REVIEWED_ESSENTIAL_COUNT,
        "internal_choice": EXPECTED_REVIEWED_INTERNAL_COUNT,
    }
    reviewed_classifications = {
        **{name: "result_canonical" for name in REVIEWED_DIRECT_CANONICAL},
        **{name: "essentially_chosen" for name in REVIEWED_DIRECT_ESSENTIAL},
        **{name: "internal_choice" for name in REVIEWED_DIRECT_INTERNAL},
    }
    errors: list[str] = []
    expected_sizes = (
        ("direct declarations", len(direct_entries), EXPECTED_REVIEWED_DIRECT_COUNT),
        ("object declarations", len(objects), EXPECTED_REVIEWED_OBJECT_COUNT),
        ("proof-only declarations", len(proofs), EXPECTED_REVIEWED_PROOF_COUNT),
        ("derived declarations", len(derived_entries), EXPECTED_REVIEWED_DERIVED_COUNT),
    )
    for label, actual, expected in expected_sizes:
        if actual != expected:
            errors.append(f"reviewed matrix requires {expected} {label}, got {actual}")
    for classification, expected in expected_counts.items():
        actual = counts[classification]
        if actual != expected:
            errors.append(
                "reviewed matrix requires "
                f"{expected} {classification} objects, got {actual}"
            )
    for entry in objects:
        name = str(entry.get("name", ""))
        expected = reviewed_classifications.get(name)
        actual = entry.get("classification")
        if expected is None:
            errors.append(f"reviewed matrix has no classification for {name}")
        elif actual != expected:
            errors.append(
                f"reviewed matrix requires {name} to be {expected}, got {actual}"
            )
    return errors


def declared_reference_names(declarations: list[Declaration]) -> set[str]:
    """Names that may be cited as a choice witness/specification contract.

    Structure and class projections are generated by Lean rather than written
    as top-level declaration commands, so recover their field names from the
    declaration body in addition to the ordinary command inventory.
    """

    result = {declaration.name for declaration in declarations}
    for declaration in declarations:
        if declaration.kind not in {"structure", "class"}:
            continue
        for line in declaration.body.splitlines()[1:]:
            match = STRUCTURE_FIELD_RE.match(line)
            if match:
                result.add(f"{declaration.name}.{match.group('name')}")
    return result


def validate_manifest_references(
    entries: list[dict[str, object]],
    declarations: list[Declaration],
    local_prefixes: tuple[str, ...] = LOCAL_CONTRACT_PREFIXES,
) -> list[str]:
    """Reject stale witness/specification names, not just stale object rows."""

    errors: list[str] = []
    known = declared_reference_names(declarations)
    for entry in entries:
        if entry.get("role") != "object":
            continue
        owner = str(entry.get("name", ""))
        for field in ("witness", "spec", "independence"):
            values = entry.get(field, [])
            if not isinstance(values, list):
                continue
            for value in values:
                if (
                    isinstance(value, str)
                    and value
                    and value.startswith(local_prefixes)
                    and value not in known
                ):
                    errors.append(
                        f"{owner}: {field} references missing declaration {value!r}"
                    )
    return errors


def validate_derived_manifest_references(
    entries: list[dict[str, object]],
    declarations: list[Declaration],
    local_prefixes: tuple[str, ...] = LOCAL_CONTRACT_PREFIXES,
) -> list[str]:
    """Reject stale specification/independence names on derived rows."""

    errors: list[str] = []
    known = declared_reference_names(declarations)
    for entry in entries:
        owner = str(entry.get("name", ""))
        for field in ("witness", "spec", "independence"):
            values = entry.get(field, [])
            if not isinstance(values, list):
                continue
            for value in values:
                if (
                    isinstance(value, str)
                    and value
                    and value.startswith(local_prefixes)
                    and value not in known
                ):
                    errors.append(
                        f"{owner}: {field} references missing declaration {value!r}"
                    )
    return errors


def check_quotient_boundary(
    declarations: list[Declaration], entries_by_name: dict[str, dict[str, object]]
) -> list[str]:
    errors: list[str] = []
    for declaration in declarations:
        if declaration.private or not declaration.is_object or "Quotient.out" not in declaration.uses:
            continue
        entry = entries_by_name.get(declaration.name, {})
        classification = entry.get("classification")
        internal = is_internal_name(declaration.name)
        explicitly_chosen = has_choice_marker(declaration.name)
        canonical_exception = (
            classification == "result_canonical"
            and entry.get("quotient_lift_exception") is True
        )
        reviewed_visible_choice = (
            classification == "essentially_chosen"
            and entry.get("choice_visible") is True
        )
        if not (
            internal
            or explicitly_chosen
            or canonical_exception
            or reviewed_visible_choice
        ):
            errors.append(
                f"{declaration.file}:{declaration.line}: public object {declaration.name} uses "
                "Quotient.out without an Internal/chosen boundary, reviewed visible-choice "
                "boundary, or canonical quotient-lift exception"
            )
    return errors


def is_internal_name(name: str) -> bool:
    return ".Internal." in f".{name}."


def has_choice_marker(name: str) -> bool:
    """Whether a public name itself advertises its noncanonical choice."""

    lowered = name.lower()
    return "chosen" in lowered or "choice" in lowered


def unmarked_essential_choices(
    public_choice: list[Declaration], entries_by_name: dict[str, dict[str, object]]
) -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for declaration in public_choice:
        if not declaration.is_object:
            continue
        entry = entries_by_name.get(declaration.name, {})
        if entry.get("classification") != "essentially_chosen":
            continue
        if (
            is_internal_name(declaration.name)
            or has_choice_marker(declaration.name)
            or entry.get("choice_visible") is True
        ):
            continue
        result.append(
            {
                "name": declaration.name,
                "kind": declaration.kind,
                "file": declaration.file,
                "line": declaration.line,
                "uses": list(declaration.uses),
                "required_action": (
                    "rename_with_choice_marker_move_to_Internal_or_set_reviewed_choice_visible"
                ),
            }
        )
    return sorted(result, key=lambda item: str(item["name"]))


def unmarked_derived_essential_choices(
    derived: list[DerivedChosenObject],
    entries_by_name: Mapping[str, Mapping[str, object]],
) -> list[dict[str, object]]:
    """Find reviewed derived choices whose public names conceal noncanonicity."""

    result: list[dict[str, object]] = []
    for item in derived:
        declaration = item.declaration
        entry = entries_by_name.get(declaration.name, {})
        if entry.get("classification") != "essentially_chosen":
            continue
        if is_internal_name(declaration.name) or has_choice_marker(declaration.name):
            continue
        result.append(
            {
                "name": declaration.name,
                "kind": declaration.kind,
                "file": declaration.file,
                "line": declaration.line,
                "depends_on": list(item.depends_on),
                "required_action": (
                    "rename_with_choice_marker_move_to_Internal_or_prove_canonical_override"
                ),
            }
        )
    return sorted(result, key=lambda item: str(item["name"]))


def forbidden_public_declarations(declarations: list[Declaration]) -> list[Declaration]:
    return [
        declaration
        for declaration in declarations
        if not declaration.private
        and any(
            declaration.name == suffix or declaration.name.endswith("." + suffix)
            for suffix in FORBIDDEN_PUBLIC_SUFFIXES
        )
    ]


def default_derived_manifest_entry(item: DerivedChosenObject) -> dict[str, object]:
    entry = item.manifest_metadata()
    entry.update(
        {
            "classification": "essentially_chosen",
            "choice_taint_override": False,
            "witness": list(item.depends_on),
            "spec": [],
            "independence": [],
            "note": DEFAULT_DERIVED_NOTE,
        }
    )
    return entry


def merge_refreshed_derived_entries(
    actual: list[DerivedChosenObject],
    existing: list[dict[str, object]],
) -> list[dict[str, object]]:
    """Refresh scanner metadata while preserving every curated review field."""

    existing_by_name = {str(entry.get("name", "")): entry for entry in existing}
    refreshed: list[dict[str, object]] = []
    for item in sorted(actual, key=derived_inventory_key):
        entry = default_derived_manifest_entry(item)
        old = existing_by_name.get(item.name)
        if old is not None:
            for field in DERIVED_CURATED_FIELDS:
                if field in old:
                    entry[field] = old[field]
        refreshed.append(entry)
    return refreshed


def default_direct_manifest_entry(declaration: Declaration) -> dict[str, object]:
    entry: dict[str, object] = {
        "name": declaration.name,
        "kind": declaration.kind,
        "file": declaration.file,
        "uses": list(declaration.uses),
        "role": "object" if declaration.is_object else "proof_only",
    }
    if declaration.is_object:
        entry.update(
            {
                "classification": "essentially_chosen",
                "witness": [],
                "spec": [],
                "independence": [],
                "note": "REVIEW REQUIRED: newly discovered direct choice object.",
            }
        )
    return entry


def reviewed_direct_manifest_entries(
    actual: list[Declaration],
) -> tuple[list[dict[str, object]], list[str]]:
    """Apply the checked recovery review to an exact direct inventory."""

    errors: list[str] = []
    objects = {declaration.name for declaration in actual if declaration.is_object}
    reviewed_objects = (
        set(REVIEWED_DIRECT_CANONICAL)
        | set(REVIEWED_DIRECT_INTERNAL)
        | set(REVIEWED_DIRECT_ESSENTIAL)
    )
    configured_counts = (
        (
            "result_canonical",
            len(REVIEWED_DIRECT_CANONICAL),
            EXPECTED_REVIEWED_CANONICAL_COUNT,
        ),
        (
            "essentially_chosen",
            len(REVIEWED_DIRECT_ESSENTIAL),
            EXPECTED_REVIEWED_ESSENTIAL_COUNT,
        ),
        (
            "internal_choice",
            len(REVIEWED_DIRECT_INTERNAL),
            EXPECTED_REVIEWED_INTERNAL_COUNT,
        ),
    )
    for classification, actual_count, expected_count in configured_counts:
        if actual_count != expected_count:
            errors.append(
                "formal initializer review config requires "
                f"{expected_count} {classification} objects, got {actual_count}"
            )
    proof_count = sum(not declaration.is_object for declaration in actual)
    if len(actual) != EXPECTED_REVIEWED_DIRECT_COUNT:
        errors.append(
            "formal initializer expected "
            f"{EXPECTED_REVIEWED_DIRECT_COUNT} direct declarations, got {len(actual)}"
        )
    if len(objects) != EXPECTED_REVIEWED_OBJECT_COUNT:
        errors.append(
            "formal initializer expected "
            f"{EXPECTED_REVIEWED_OBJECT_COUNT} objects, got {len(objects)}"
        )
    if proof_count != EXPECTED_REVIEWED_PROOF_COUNT:
        errors.append(
            "formal initializer expected "
            f"{EXPECTED_REVIEWED_PROOF_COUNT} proof-only declarations, got {proof_count}"
        )
    for name in sorted(objects - reviewed_objects):
        errors.append(f"formal initializer has no object review for {name}")
    for name in sorted(reviewed_objects - objects):
        errors.append(f"formal initializer review is stale for {name}")
    if errors:
        return [], errors

    entries: list[dict[str, object]] = []
    for declaration in sorted(actual, key=inventory_key):
        entry = default_direct_manifest_entry(declaration)
        if not declaration.is_object:
            entries.append(entry)
            continue

        name = declaration.name
        entry["witness"] = [name]
        if name in REVIEWED_DIRECT_CANONICAL:
            spec, independence = REVIEWED_DIRECT_CANONICAL[name]
            entry.update(
                {
                    "classification": "result_canonical",
                    "spec": list(spec),
                    "independence": list(independence),
                    "note": (
                        "The listed evaluation/minimality specification and "
                        "uniqueness boundary determine the public result; the "
                        "implementation witness is not observable."
                    ),
                }
            )
            if "Quotient.out" in declaration.uses:
                entry["quotient_lift_exception"] = True
        elif name in REVIEWED_DIRECT_INTERNAL:
            spec, independence = REVIEWED_DIRECT_INTERNAL[name]
            entry.update(
                {
                    "classification": "internal_choice",
                    "spec": list(spec),
                    "independence": list(independence),
                    "note": (
                        "This helper is proof-valued; proof irrelevance prevents "
                        "the selected inhabitant from becoming observable data."
                    ),
                }
            )
        else:
            entry.update(
                {
                    "classification": "essentially_chosen",
                    "spec": [],
                    "independence": [],
                    "note": (
                        "The declaration exposes selected data and no reviewed "
                        "uniqueness theorem identifies all alternatives."
                    ),
                }
            )
            if not has_choice_marker(name) and not is_internal_name(name):
                # These are existing public names, not an automatic exemption:
                # their complete name set is frozen above and the flag makes the
                # legacy visible-choice boundary explicit in the manifest.
                entry["choice_visible"] = True
        entries.append(entry)
    return entries, []


def reviewed_derived_manifest_entries(
    actual: list[DerivedChosenObject],
) -> tuple[list[dict[str, object]], list[str]]:
    """Review the exact derived chosen-value inventory for initialization."""

    errors: list[str] = []
    if len(actual) != EXPECTED_REVIEWED_DERIVED_COUNT:
        errors.append(
            "formal initializer expected "
            f"{EXPECTED_REVIEWED_DERIVED_COUNT} derived objects, got {len(actual)}"
        )
    external = {
        item.name
        for item in actual
        if "external_or_opaque_choice_source" in item.detection
    }
    expected_external = set(REVIEWED_DERIVED_EXTERNAL_SPECS)
    for name in sorted(external - expected_external):
        errors.append(f"formal initializer has no external derived review for {name}")
    for name in sorted(expected_external - external):
        errors.append(f"formal initializer external derived review is stale for {name}")
    if errors:
        return [], errors

    entries: list[dict[str, object]] = []
    for item in sorted(actual, key=derived_inventory_key):
        entry = item.manifest_metadata()
        entry.update(
            {
                "classification": "essentially_chosen",
                "choice_taint_override": False,
                "witness": list(item.depends_on) or [item.name],
                "spec": list(REVIEWED_DERIVED_EXTERNAL_SPECS.get(item.name, ())),
                "independence": [],
                "note": (
                    "The public chosen-value boundary retains an observable "
                    "choice dependency; no canonicity override is asserted."
                ),
            }
        )
        entries.append(entry)
    return entries, []


def merge_refreshed_direct_entries(
    actual: list[Declaration],
    existing: list[dict[str, object]],
) -> list[dict[str, object]]:
    """Refresh scanner metadata while preserving reviewed direct contracts."""

    existing_by_name = {str(entry.get("name", "")): entry for entry in existing}
    refreshed: list[dict[str, object]] = []
    for declaration in sorted(actual, key=inventory_key):
        entry = default_direct_manifest_entry(declaration)
        old = existing_by_name.get(declaration.name)
        if old is not None and declaration.is_object:
            for field in DIRECT_CURATED_FIELDS:
                if field in old:
                    entry[field] = old[field]
        refreshed.append(entry)
    return refreshed


def manifest_payload(
    direct_entries: list[dict[str, object]],
    derived_entries: list[dict[str, object]],
) -> dict[str, object]:
    return {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": source_inventory(),
        "choice_primitives": list(CHOICE_PRIMITIVES),
        "declarations": direct_entries,
        "derived_declarations": derived_entries,
    }


def run_self_tests() -> None:
    synthetic = r'''
namespace AuditFixture

def publicChoice := Classical.choose witness

structure Contract where
  specification : True

private def hiddenChoice := Quotient.out q

theorem proofChoice : True := by
  let n := Nat.find existsNat
  trivial

def safeChooseSpec := Classical.choose_spec witness

def safeComment := 0 -- Classical.choose witness

def safeString := "Quotient.out"

def beforeExample := 0

example := Classical.choice nonemptyWitness

def afterExample := 1

def
splitName := Nonempty.some nonemptyWitness

end AuditFixture
'''
    declarations = scan_source(synthetic, "AuditFixture.lean")
    by_name = {declaration.name: declaration for declaration in declarations}
    assert by_name["AuditFixture.publicChoice"].uses == ("Classical.choose",)
    assert by_name["AuditFixture.hiddenChoice"].private
    assert by_name["AuditFixture.hiddenChoice"].uses == ("Quotient.out",)
    assert by_name["AuditFixture.proofChoice"].uses == ("Nat.find",)
    assert not by_name["AuditFixture.safeChooseSpec"].uses
    assert not by_name["AuditFixture.safeComment"].uses
    assert not by_name["AuditFixture.safeString"].uses
    assert not by_name["AuditFixture.beforeExample"].uses
    assert not by_name["AuditFixture.afterExample"].uses
    assert by_name["AuditFixture.splitName"].uses == ("Nonempty.some",)

    reference_entry = {
        "name": "AuditFixture.publicChoice",
        "kind": "def",
        "role": "object",
        "classification": "result_canonical",
        "witness": ["AuditFixture.publicChoice"],
        "spec": ["AuditFixture.Contract.specification"],
        "independence": ["Subsingleton.elim"],
    }
    assert not validate_manifest_references(
        [reference_entry], declarations, ("AuditFixture.",)
    )
    stale_reference = dict(
        reference_entry, spec=["AuditFixture.Contract.removedSpecification"]
    )
    assert any(
        "missing declaration" in error
        for error in validate_manifest_references(
            [stale_reference], declarations, ("AuditFixture.",)
        )
    )

    valid_object = {
        "name": "AuditFixture.canonical",
        "kind": "def",
        "role": "object",
        "classification": "result_canonical",
        "witness": ["source"],
        "spec": ["spec"],
        "independence": ["unique"],
    }
    assert not validate_manifest_shape([valid_object])
    missing_unique = dict(valid_object, independence=[])
    assert any("independence/uniqueness" in error for error in validate_manifest_shape([missing_unique]))

    bad_quotient = Declaration(
        "AuditFixture.hiddenRepresentative", "def", "AuditFixture.lean", 1, False,
        "def hiddenRepresentative := Quotient.out q\n",
    )
    chosen_quotient = Declaration(
        "AuditFixture.chosenRepresentative", "def", "AuditFixture.lean", 2, False,
        "def chosenRepresentative := Quotient.out q\n",
    )
    canonical_quotient = Declaration(
        "AuditFixture.canonical", "def", "AuditFixture.lean", 3, False,
        "def canonical := Quotient.out q\n",
    )
    entries = {
        "AuditFixture.hiddenRepresentative": {"classification": "essentially_chosen"},
        "AuditFixture.chosenRepresentative": {"classification": "essentially_chosen"},
        "AuditFixture.canonical": {
            "classification": "result_canonical",
            "quotient_lift_exception": True,
        },
    }
    quotient_errors = check_quotient_boundary(
        [bad_quotient, chosen_quotient, canonical_quotient], entries
    )
    assert len(quotient_errors) == 1 and "hiddenRepresentative" in quotient_errors[0]

    unmarked = unmarked_essential_choices(
        [bad_quotient, chosen_quotient, canonical_quotient], entries
    )
    assert [item["name"] for item in unmarked] == ["AuditFixture.hiddenRepresentative"]

    forbidden = Declaration(
        "AuditFixture.zHatRepresentation", "def", "AuditFixture.lean", 4, False,
        "def zHatRepresentation := 0\n",
    )
    private_forbidden = Declaration(
        "AuditFixture.relativeTowerCosetEquiv", "def", "AuditFixture.lean", 5, True,
        "private def relativeTowerCosetEquiv := 0\n",
    )
    assert forbidden_public_declarations([forbidden, private_forbidden]) == [forbidden]

    derived_source = r'''
namespace DerivedFixture

def chosenSeed := Classical.choose seedWitness

def chosenDerived := chosenSeed

def chosenTransitive := chosenDerived

def hiddenDerived := chosenSeed

def canonicalSeed := Nat.find canonicalWitness

def fromCanonical := canonicalSeed

def chosenCanonicalBoundary := chosenSeed

def afterCanonicalBoundary := chosenCanonicalBoundary

def formalChoiceCount := Combinator.Choice input

theorem proofBridge : chosenSeed = chosenSeed := rfl

def afterProofBridge := by
  have := proofBridge
  exact 0

end DerivedFixture
'''
    derived_declarations = scan_source(derived_source, "DerivedFixture.lean")
    derived_public_choice = [
        declaration
        for declaration in derived_declarations
        if not declaration.private and declaration.uses
    ]
    direct_contract = {
        "DerivedFixture.chosenSeed": {"classification": "essentially_chosen"},
        "DerivedFixture.canonicalSeed": {"classification": "result_canonical"},
    }
    curated_derived = {
        "DerivedFixture.hiddenDerived": {
            "classification": "essentially_chosen",
            "choice_taint_override": False,
        },
        "DerivedFixture.chosenCanonicalBoundary": {
            "classification": "result_canonical",
            "choice_taint_override": True,
        },
    }
    derived_inventory, derived_taint = derived_chosen_inventory(
        derived_declarations,
        derived_public_choice,
        direct_contract,
        curated_derived,
    )
    derived_by_name = {item.name: item for item in derived_inventory}
    assert derived_by_name["DerivedFixture.chosenDerived"].depends_on == (
        "DerivedFixture.chosenSeed",
    )
    assert derived_by_name["DerivedFixture.chosenTransitive"].depends_on == (
        "DerivedFixture.chosenDerived",
    )
    assert "DerivedFixture.hiddenDerived" in derived_by_name
    assert "DerivedFixture.fromCanonical" not in derived_by_name
    assert "DerivedFixture.formalChoiceCount" not in derived_by_name
    assert "DerivedFixture.afterProofBridge" not in derived_by_name
    assert "DerivedFixture.chosenCanonicalBoundary" not in derived_taint
    assert "DerivedFixture.afterCanonicalBoundary" not in derived_by_name

    hidden_entry = {
        **derived_by_name["DerivedFixture.hiddenDerived"].manifest_metadata(),
        "classification": "essentially_chosen",
        "choice_taint_override": False,
        "witness": ["DerivedFixture.chosenSeed"],
        "spec": ["DerivedFixture.hiddenDerived_spec"],
        "independence": [],
        "note": "Synthetic hidden choice.",
    }
    hidden_errors = unmarked_derived_essential_choices(
        derived_inventory,
        {"DerivedFixture.hiddenDerived": hidden_entry},
    )
    assert [item["name"] for item in hidden_errors] == [
        "DerivedFixture.hiddenDerived"
    ]

    canonical_entry = {
        **derived_by_name[
            "DerivedFixture.chosenCanonicalBoundary"
        ].manifest_metadata(),
        "classification": "result_canonical",
        "choice_taint_override": True,
        "witness": ["DerivedFixture.chosenSeed"],
        "spec": ["DerivedFixture.chosenCanonicalBoundary_spec"],
        "independence": ["DerivedFixture.chosenCanonicalBoundary_unique"],
        "note": "Synthetic reviewed canonical boundary.",
    }
    assert not validate_derived_manifest_shape(
        [canonical_entry], []
    )
    unproved_override = dict(canonical_entry, independence=[])
    assert any(
        "independence/uniqueness evidence" in error
        for error in validate_derived_manifest_shape([unproved_override], [])
    )

    refreshed = merge_refreshed_derived_entries(
        [derived_by_name["DerivedFixture.chosenCanonicalBoundary"]],
        [canonical_entry],
    )
    assert refreshed[0]["classification"] == "result_canonical"
    assert refreshed[0]["choice_taint_override"] is True
    assert refreshed[0]["note"] == canonical_entry["note"]


def current_json(public_choice: list[Declaration]) -> str:
    payload = {
        "schema_version": SCHEMA_VERSION,
        "source_inventory": source_inventory(),
        "choice_primitives": list(CHOICE_PRIMITIVES),
        "declarations": [
            {
                "name": declaration.name,
                "kind": declaration.kind,
                "file": declaration.file,
                "line": declaration.line,
                "uses": list(declaration.uses),
                "role": "object" if declaration.is_object else "proof_only",
            }
            for declaration in sorted(public_choice, key=inventory_key)
        ],
    }
    # Compact output stays below common CI/log transport limits even for the
    # complete proof-only inventory.  The checked-in manifest remains pretty
    # printed for review.
    return json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=False)


def write_manifest(path: Path, payload: dict[str, object]) -> None:
    """Atomically write a manifest after creating its documentation directory."""

    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--print-current",
        action="store_true",
        help="print the freshly scanned, unclassified direct inventory and exit",
    )
    parser.add_argument(
        "--scan-only",
        action="store_true",
        help="scan all sources and report the direct inventory without a manifest",
    )
    parser.add_argument(
        "--print-derived-current",
        action="store_true",
        help="print the freshly scanned derived-choice metadata and exit",
    )
    parser.add_argument(
        "--refresh-manifest",
        action="store_true",
        help=(
            "refresh exact scanner metadata in the manifest while preserving "
            "all reviewed classification fields"
        ),
    )
    parser.add_argument(
        "--initialize-manifest",
        action="store_true",
        help=(
            "create a missing manifest from the exact formally reviewed recovery "
            "inventory; refuse changed or unreviewed objects"
        ),
    )
    parser.add_argument(
        "--report-unmarked-essential",
        action="store_true",
        help="print a machine-readable list of essentially-chosen objects whose public names hide choice",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run deterministic parser and policy regression tests without scanning the repository",
    )
    args = parser.parse_args(argv)

    if args.refresh_manifest and args.initialize_manifest:
        parser.error(
            "--refresh-manifest and --initialize-manifest are mutually exclusive"
        )
    if args.self_test:
        try:
            run_self_tests()
        except AssertionError as error:
            print(f"choice-contract self-test: FAILED: {error}", file=sys.stderr)
            return 1
        print("choice-contract self-test: OK")
        return 0

    all_declarations, public_choice = scan_library()
    if args.scan_only:
        print(
            "choice-contract scan: OK "
            f"({len(all_declarations)} declarations, "
            f"{len(public_choice)} direct choice declarations)"
        )
        return 0
    if args.print_current:
        print(current_json(public_choice))
        return 0

    if args.initialize_manifest:
        if args.manifest.exists():
            print(
                "choice-contract: refusing to overwrite existing manifest "
                f"{args.manifest}; use --refresh-manifest",
                file=sys.stderr,
            )
            return 2
        initialized_entries, initialization_errors = reviewed_direct_manifest_entries(
            public_choice
        )
        if initialization_errors:
            print("choice-contract: formal initialization refused:", file=sys.stderr)
            for error in initialization_errors:
                print(f"  - {error}", file=sys.stderr)
            return 1
        initialized_by_name = {
            str(entry.get("name", "")): entry for entry in initialized_entries
        }
        initialized_derived, _ = derived_chosen_inventory(
            all_declarations,
            public_choice,
            initialized_by_name,
            {},
        )
        initialized_derived_entries, derived_initialization_errors = (
            reviewed_derived_manifest_entries(initialized_derived)
        )
        if derived_initialization_errors:
            print("choice-contract: formal initialization refused:", file=sys.stderr)
            for error in derived_initialization_errors:
                print(f"  - {error}", file=sys.stderr)
            return 1
        payload = manifest_payload(
            initialized_entries, initialized_derived_entries
        )
        validation_errors = validate_manifest_shape(initialized_entries)
        validation_errors.extend(
            validate_manifest_references(initialized_entries, all_declarations)
        )
        validation_errors.extend(
            validate_derived_manifest_shape(
                initialized_derived_entries, initialized_entries
            )
        )
        validation_errors.extend(
            validate_derived_manifest_references(
                initialized_derived_entries, all_declarations
            )
        )
        validation_errors.extend(
            validate_reviewed_totals(
                initialized_entries, initialized_derived_entries
            )
        )
        if validation_errors:
            print("choice-contract: formal initialization refused:", file=sys.stderr)
            for error in validation_errors:
                print(f"  - {error}", file=sys.stderr)
            return 1
        write_manifest(args.manifest, payload)
        print(
            "choice-contract: initialized "
            f"{len(initialized_entries)} direct and "
            f"{len(initialized_derived_entries)} derived entries at "
            f"{args.manifest} from the formal reviewed inventory"
        )
        return 0

    try:
        manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    except FileNotFoundError:
        print(
            f"choice-contract: manifest is missing: {args.manifest}; "
            "restore the reviewed manifest or run --initialize-manifest",
            file=sys.stderr,
        )
        return 2
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        print(
            f"choice-contract: cannot read manifest {args.manifest}: {error}",
            file=sys.stderr,
        )
        return 2
    if not isinstance(manifest, dict):
        print("choice-contract: manifest root must be an object", file=sys.stderr)
        return 2

    raw_entries = manifest.get("declarations")
    if not isinstance(raw_entries, list) or not all(isinstance(item, dict) for item in raw_entries):
        print("choice-contract: manifest 'declarations' must be an array of objects", file=sys.stderr)
        return 2
    entries: list[dict[str, object]] = raw_entries

    raw_derived_entries = manifest.get("derived_declarations", [])
    if not isinstance(raw_derived_entries, list) or not all(
        isinstance(item, dict) for item in raw_derived_entries
    ):
        print(
            "choice-contract: manifest 'derived_declarations' must be an array of objects",
            file=sys.stderr,
        )
        return 2
    derived_entries: list[dict[str, object]] = raw_derived_entries

    if args.refresh_manifest:
        refresh_input_errors = validate_manifest_shape(entries)
        refresh_input_errors.extend(
            validate_derived_manifest_shape(derived_entries, entries)
        )
        refresh_input_errors.extend(validate_reviewed_totals(entries, derived_entries))
        if tuple(manifest.get("choice_primitives", [])) != CHOICE_PRIMITIVES:
            refresh_input_errors.append(
                "manifest choice_primitives differ from the checker contract"
            )
        if refresh_input_errors:
            print(
                "choice-contract: refusing to refresh malformed reviewed fields:",
                file=sys.stderr,
            )
            for error in refresh_input_errors:
                print(f"  - {error}", file=sys.stderr)
            return 2
        refreshed_entries = merge_refreshed_direct_entries(public_choice, entries)
        refreshed_by_name = {
            str(entry.get("name", "")): entry for entry in refreshed_entries
        }
        refreshed_derived, _ = derived_chosen_inventory(
            all_declarations,
            public_choice,
            refreshed_by_name,
            {str(entry.get("name", "")): entry for entry in derived_entries},
        )
        refreshed_derived_entries = merge_refreshed_derived_entries(
            refreshed_derived, derived_entries
        )
        payload = manifest_payload(refreshed_entries, refreshed_derived_entries)
        refreshed_errors = validate_manifest_shape(refreshed_entries)
        refreshed_errors.extend(
            validate_manifest_references(
                refreshed_entries, all_declarations
            )
        )
        refreshed_errors.extend(
            validate_derived_manifest_shape(
                refreshed_derived_entries, refreshed_entries
            )
        )
        refreshed_errors.extend(
            validate_derived_manifest_references(
                refreshed_derived_entries, all_declarations
            )
        )
        refreshed_errors.extend(
            validate_reviewed_totals(
                refreshed_entries, refreshed_derived_entries
            )
        )
        write_manifest(args.manifest, payload)
        print(
            "choice-contract: refreshed "
            f"{len(refreshed_entries)} direct and "
            f"{len(refreshed_derived_entries)} derived declarations"
        )
        if refreshed_errors:
            print(
                "choice-contract: refreshed inventory requires review:",
                file=sys.stderr,
            )
            for error in refreshed_errors:
                print(f"  - {error}", file=sys.stderr)
            return 1
        return 0

    entries_by_name = {str(entry.get("name", "")): entry for entry in entries}
    derived_entries_by_name = {
        str(entry.get("name", "")): entry for entry in derived_entries
    }
    derived_inventory, _ = derived_chosen_inventory(
        all_declarations,
        public_choice,
        entries_by_name,
        derived_entries_by_name,
    )
    if args.print_derived_current:
        print(
            json.dumps(
                [item.manifest_metadata() for item in derived_inventory],
                indent=2,
                ensure_ascii=False,
            )
        )
        return 0

    errors: list[str] = []
    if manifest.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"manifest schema_version must be {SCHEMA_VERSION}")
    if manifest.get("source_inventory") != source_inventory():
        errors.append(
            "manifest source_inventory differs from the current Class Field "
            "Theory module set; run --refresh-manifest after reviewing "
            "the module change"
        )
    if tuple(manifest.get("choice_primitives", [])) != CHOICE_PRIMITIVES:
        errors.append("manifest choice_primitives differ from the checker contract")

    errors.extend(validate_manifest_shape(entries))
    errors.extend(validate_manifest_references(entries, all_declarations))
    errors.extend(validate_derived_manifest_shape(derived_entries, entries))
    errors.extend(validate_derived_manifest_references(derived_entries, all_declarations))
    errors.extend(validate_reviewed_totals(entries, derived_entries))

    actual = {inventory_key(declaration) for declaration in public_choice}
    expected = {manifest_key(entry) for entry in entries}
    for key in sorted(actual - expected):
        errors.append(f"unreviewed public choice declaration: {display_key(key)}")
    for key in sorted(expected - actual):
        errors.append(f"stale choice manifest entry: {display_key(key)}")

    actual_derived = {
        derived_inventory_key(item) for item in derived_inventory
    }
    expected_derived = {
        derived_manifest_key(entry) for entry in derived_entries
    }
    for key in sorted(actual_derived - expected_derived):
        errors.append(f"unreviewed derived choice declaration: {display_derived_key(key)}")
    for key in sorted(expected_derived - actual_derived):
        errors.append(f"stale derived choice manifest entry: {display_derived_key(key)}")

    unmarked = unmarked_essential_choices(public_choice, entries_by_name)
    unmarked_derived = unmarked_derived_essential_choices(
        derived_inventory, derived_entries_by_name
    )
    if args.report_unmarked_essential:
        print(
            json.dumps(
                {
                    "unmarked_essential_choice": unmarked,
                    "unmarked_derived_essential_choice": unmarked_derived,
                },
                indent=2,
                ensure_ascii=False,
            )
        )
        return 1 if unmarked or unmarked_derived else 0
    for item in unmarked:
        errors.append(
            f"{item['file']}:{item['line']}: essentially-chosen public object "
            f"{item['name']} does not advertise choice in its name or an Internal namespace"
        )
    for item in unmarked_derived:
        errors.append(
            f"{item['file']}:{item['line']}: essentially-chosen derived public object "
            f"{item['name']} does not advertise choice in its name or an Internal namespace"
        )
    errors.extend(check_quotient_boundary(all_declarations, entries_by_name))

    for declaration in forbidden_public_declarations(all_declarations):
        errors.append(
            f"{declaration.file}:{declaration.line}: forbidden legacy public API exposed: "
            f"{declaration.name}"
        )

    if errors:
        print("choice-contract: FAILED", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1

    object_count = sum(1 for entry in entries if entry.get("role") == "object")
    proof_count = len(entries) - object_count
    derived_canonical_count = sum(
        entry.get("classification") == "result_canonical"
        for entry in derived_entries
    )
    primitive_counts = {
        primitive: sum(primitive in declaration.uses for declaration in public_choice)
        for primitive in CHOICE_PRIMITIVES
    }
    print(
        "choice-contract: OK "
        f"({len(entries)} public declarations: {object_count} objects, {proof_count} proof-only; "
        f"{len(derived_entries)} derived objects, "
        f"{derived_canonical_count} canonical taint boundaries; "
        + ", ".join(f"{primitive}={count}" for primitive, count in primitive_counts.items())
        + ")"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
