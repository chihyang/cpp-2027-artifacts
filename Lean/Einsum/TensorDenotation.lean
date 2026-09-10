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

namespace TensorDenotation
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex
open UnnamedIndex
open TensorExpr

abbrev Unique := NamedShape.Unique

def sumPairs {S : Type} [Semiring S]
  (xs : List Dim)
  (neq : Unique xs)
  (f : Index (fromList xs neq) → S) :
  S :=
  match xs with
  | [] => f Index.empty
  | (_, d) :: xs' =>
    ∑ i : Fin d,
      sumPairs xs' (Unique_cons neq)
        (fun idx => f (Index.cons i idx))

def sum {S : Type} [Semiring S]
  (xs : Is)
  (f : Index xs → S) : S :=
  ∑ i : Index xs, f i

theorem sum_comp {S : Type} [Semiring S]
  {xs ys : Is}
  (hxy : ys ≈ xs)
  (f : Index xs → S) :
  sum xs f = sum ys (f ∘ fun idx => idx →ᵢ hxy) := by
  unfold sum
  rw [← Equiv.sum_comp (Index.eqEquiv hxy)]
  simp only [Function.comp_apply]
  rfl

theorem sum_disjoing_prod_type {S : Type} [Semiring S]
  {xs ys zs : Is}
  (ys_zs : ys ⊥ zs)
  (hxyz : unionIs ys zs (disjointIs_compat ys_zs) ≈ xs)
  (f : Index xs → S) :
  sum xs f =
  sum ys
    (fun idxy =>
      sum zs
        (fun idxz =>
          (f (Index.union ys_zs idxy idxz →ᵢ hxyz)))) := by
  rw [sum_comp hxyz f]
  unfold sum
  simp only
  rw [← Equiv.sum_comp (Index.union_disjoint ys_zs).symm]
  change
    (∑ idx : Index ys × Index zs,
      f (Index.union ys_zs idx.1 idx.2 →ᵢ hxyz)) = _
  exact Fintype.sum_prod_type
    (fun idx => f (Index.union ys_zs idx.1 idx.2 →ᵢ hxyz))

mutual
def denote {S : Type} [Semiring S] {Γ : Context} {xs : Is}
  (wt : TExpr (S := S) Γ xs) (env : Env (S := S) Γ) (idx : Index xs) : S :=
  match wt with
  | .scalar r => r
  | .zero _ => 0
  | .expand wt₁ xs_zs => denote wt₁ env (idx ↓ᵢ xs_zs)
  | .einsum (zs := zs) wts xssCompat zs_xss =>
    let allIdxs := unionIss xssCompat
    let zs_disjoint := minusIs_disjoint
    let zs_union := minusIs_union_eq zs_xss
    sum (allIdxs ∖ zs)
      (fun idx' =>
        denotes wts xssCompat
          (IsSubset_refl (xs := allIdxs))
          env
          ((Index.union zs_disjoint idx idx') →ᵢ
           zs_union))
  | .add wt₁ wt₂ xs_ys =>
    (denote wt₁ env idx) + (denote wt₂ env (idx →ᵢ xs_ys))
  | .scale n wt => n * denote wt env idx
  | .const _ f => f idx
  | .var dims neq v => lookupUnnamed v env (Index.toUnnamed dims neq idx)
  | .let dims neq wt₁ wt₂ =>
    let rhsNamed := denote wt₁ env
    let rhsUnnamed := rhsNamed ∘ (Index.fromUnnamed dims neq)
    denote wt₂ (env , rhsUnnamed) idx

def denotes {S : Type} [Semiring S] {Γ : Context}
  {xss : List Is} {ys : Is}
  (wts : TExprSeq (S := S) Γ xss)
  (xssCompat : IssCompat xss)
  (h : unionIss xssCompat ⊑ ys)
  (env : Env (S := S) Γ) (idx : Index ys) : S :=
  match wts with
  | .nil => 1
  | .cons wt wts' =>
    have h' :=
      IsSubset_trans
        (unionIss_compat_part xssCompat List.mem_cons_self)
        h
    denote wt env (idx ↓ᵢ h') *
    denotes wts'
      (by apply IssCompat_inv_cons ; exact xssCompat)
      (by apply unionIss_compat_tail xssCompat ; exact h)
      env idx
end

theorem denote_congr {S : Type} [Semiring S]
  {Γ : Context} {xs : Is}
  (wt : TExpr Γ xs)
  (env : Env (S := S) Γ)
  (idx₁ idx₂ : Index xs)
  (h : idx₁ ≈ᵢ idx₂) :
  denote wt env idx₁ = denote wt env idx₂ := by
  rw [Index.ext h]

theorem denote_subst_cast_assoc {S : Type} [Semiring S]
  {Γ : Context} {xs ys zs : Is}
  (wt : TExpr Γ xs)
  (env : Env (S := S) Γ)
  (idx : Index zs)
  (xs_ys : xs ⊑ ys)
  (ys_zs : ys ⊑ zs) :
  denote wt env ((idx ↓ᵢ ys_zs) ↓ᵢ xs_ys) =
  denote wt env (idx ↓ᵢ IsSubset_trans xs_ys ys_zs) := by
  apply denote_congr
  apply Index.subst_cast_assoc

theorem denotes_eq_cast {S : Type} [Semiring S]
  {Γ : Context} {xss : Iss} {zs ws : Is}
  (wts : TExprSeq (S := S) Γ xss)
  (xssCompat : IssCompat xss)
  (xss_zs : unionIss xssCompat ⊑ zs)
  (xss_ws : unionIss xssCompat ⊑ ws)
  (zs_ws : zs ≈ ws)
  (env : Env (S := S) Γ)
  (idx : Index zs) :
  denotes wts xssCompat xss_ws env (idx →ᵢ zs_ws) =
  denotes wts xssCompat xss_zs env idx := by
  cases wts with
  | nil => rfl
  | cons wt wts' =>
    simp only [denotes]
    apply congrArg₂ (fun a b => a * b)
    · apply denote_congr
      apply Index.eq_subst_cast
    · apply denotes_eq_cast

theorem denotes_congr {S : Type} [Semiring S]
  {Γ : Context} {xss : Iss} {ys₁ ys₂ zs : Is}
  (wts : TExprSeq (S := S) Γ xss)
  (xssCompat : IssCompat xss)
  (xss_ys₁ : unionIss xssCompat ⊑ ys₁)
  (xss_ys₂ : unionIss xssCompat ⊑ ys₂)
  (ys₁_zs : ys₁ ⊑ zs)
  (ys₂_zs : ys₂ ⊑ zs)
  (env : Env (S := S) Γ)
  (idx : Index zs) :
  denotes wts xssCompat xss_ys₁ env (idx ↓ᵢ ys₁_zs) =
  denotes wts xssCompat xss_ys₂ env (idx ↓ᵢ ys₂_zs) := by
  cases wts with
  | nil => rfl
  | cons wt wts' =>
    simp only [denotes]
    apply congrArg₂ (fun a b => a * b)
    · apply denote_congr
      intro i v h
      unfold Index.subst_cast
      exact congrArg (fun p => idx.get p) (Subsingleton.elim _ _)
    · apply denotes_congr

end TensorDenotation
