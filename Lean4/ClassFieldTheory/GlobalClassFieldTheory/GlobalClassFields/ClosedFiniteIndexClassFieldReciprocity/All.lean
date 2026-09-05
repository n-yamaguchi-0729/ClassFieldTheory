import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic.All
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue
import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological.All

set_option autoImplicit false

/-!
# Reciprocity for a closed finite-index class field

This facade exports the degree formula and the topological and algebraic
reciprocity equivalences after their command-sized leaves have elaborated.
Keeping the expensive equivalence constructions in separate compiled leaves
prevents downstream ray-class-field consumers from rebuilding the entire
reciprocity layer as one declaration block.
-/
