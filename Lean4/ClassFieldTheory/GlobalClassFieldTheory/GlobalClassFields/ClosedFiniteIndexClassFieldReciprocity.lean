import GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Degree
import GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Topological
import GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.Algebraic
import GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldReciprocity.GlobalNormResidue

/-!
# Reciprocity for a closed finite-index class field

This facade exports the degree formula and the topological and algebraic
reciprocity equivalences after their command-sized leaves have elaborated.
Keeping the expensive equivalence constructions in separate compiled leaves
prevents downstream ray-class-field consumers from rebuilding the entire
reciprocity layer as one declaration block.
-/
