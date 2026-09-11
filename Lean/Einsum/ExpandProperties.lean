import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Einsum.NamedShape
import Einsum.ShapeOperations
import Einsum.ShapeProperties
import Einsum.NamedIndex
import Einsum.UnnamedIndex
import Einsum.TensorExpr
import Einsum.TensorDenotation

namespace ExpandProperties
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex
open UnnamedIndex
open TensorExpr
open TensorDenotation

abbrev Unique := NamedShape.Unique

theorem expand_fuse {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys zs : Is}
  (wt : TExpr Γ xs)
  (xs_ys : xs ⊑ ys)
  (ys_zs : ys ⊑ zs)
  (env : Env (S := S) Γ)
  (idx : NIndex zs) :
  denote (.expand (.expand wt xs_ys) ys_zs) env idx
    =
  denote (.expand wt (IsSubset_trans xs_ys ys_zs)) env idx := by
  simp only [denote]
  apply denote_congr
  apply NIndex.subst_cast_assoc

end ExpandProperties
