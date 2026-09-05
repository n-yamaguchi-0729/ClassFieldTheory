import ClassFieldTheory.AlgebraicNumberTheory.Adele.All
import ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
import ClassFieldTheory.AlgebraicNumberTheory.Completion.All
import ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
import ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import ClassFieldTheory.AlgebraicNumberTheory.Galois.All
import ClassFieldTheory.AlgebraicNumberTheory.Idele.All
import ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
import ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
import ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
import ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

set_option autoImplicit false

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
