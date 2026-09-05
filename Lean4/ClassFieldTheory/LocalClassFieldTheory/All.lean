import ClassFieldTheory.LocalClassFieldTheory.ClassFormation.All
import ClassFieldTheory.LocalClassFieldTheory.Finite.All
import ClassFieldTheory.LocalClassFieldTheory.Infinite.All
import ClassFieldTheory.LocalClassFieldTheory.Kummer.All
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.All

set_option autoImplicit false

/-!
# Local class field theory

This is the canonical root of the complete local class field theory library.
It reaches every supported implementation layer and no examples or contract
tests. Clients that need a smaller dependency closure should import the
semantic owner aggregate for the result they use:

- `LocalClassFieldTheory.Finite.LocalReciprocity` for finite reciprocity;
- `LocalClassFieldTheory.Finite.Existence` for finite existence;
- `LocalClassFieldTheory.Infinite` for absolute and profinite reciprocity;
- `LocalClassFieldTheory.Kummer` for the local Kummer pairing;
- `LocalClassFieldTheory.LubinTateApplication` for Lubin--Tate applications.

Examples and contract tests remain in the separate `ClassFieldTheoryTests`
target.

The principal declarations live in the `LocalClassFieldTheory` namespace.
The abstract class-formation layer uses the `ClassFormation` namespace.

## Headline API

The finite reciprocity isomorphism and continuous Artin map:
- `LocalClassFieldTheory.localReciprocityEquiv`
- `LocalClassFieldTheory.localArtinMap`
- `LocalClassFieldTheory.localArtinMap_surjective`
- `LocalClassFieldTheory.localArtinMap_ker`

Finite local existence:
- `LocalClassFieldTheory.finiteAbelianNormSubgroupOrderIso`

Absolute and profinite reciprocity:
- `LocalClassFieldTheory.absoluteLocalArtinMap`
- `LocalClassFieldTheory.profiniteLocalReciprocity`
-/
