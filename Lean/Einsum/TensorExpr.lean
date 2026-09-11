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

namespace TensorExpr
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex
open UnnamedIndex

abbrev Unique := NamedShape.Unique

abbrev UnnamedTensor {S : Type} [Semiring S] (dims : List UpperBound) :=
  UIndex dims → S

inductive Context : Type where
  | nil : Context
  | snoc : Context → List UpperBound → Context

infixl:55 " `, " => Context.snoc

def Env {S : Type} [Semiring S] : Context → Type
  | .nil => Unit
  | Γ `, dims => Env (S := S) Γ × UnnamedTensor (S := S) dims

inductive CtxMem : List UpperBound → Context → Type where
  | here {Γ : Context} {dims : List UpperBound} :
      CtxMem dims (Γ `, dims)
  | there {Γ : Context} {dims dims' : List UpperBound} :
      CtxMem dims Γ → CtxMem dims (Γ `, dims')

infix:50 " ∈ᵘ " => CtxMem

def lookupUnnamed {S : Type} [Semiring S] {Γ : Context} {dims : List UpperBound}
  (v : dims ∈ᵘ Γ) (env : Env (S := S) Γ) : UnnamedTensor (S := S) dims :=
  match v , env with
  | CtxMem.here , (_ , t) => t
  | CtxMem.there v' , (ts , _) => lookupUnnamed v' ts

mutual
inductive TExpr {S : Type} [Semiring S] :
  Context → Is → Type where
  | scalar {Γ : Context} : S → TExpr Γ empty
  | zero {Γ : Context} : (xs : Is) → TExpr Γ xs
  | expand {Γ : Context} {xs zs : Is} :
    TExpr Γ xs →
    xs ⊑ zs →
    TExpr Γ zs
  | einsum {Γ : Context} {xss : List Is} {zs : Is} :
    TExprSeq Γ xss →
    (xssCompat : IssCompat xss) →
    zs ⊑ unionIss xssCompat →
    TExpr Γ zs
  | add {Γ : Context} {xs ys : Is} :
    TExpr Γ xs →
    TExpr Γ ys →
    xs ≈ ys →
    TExpr Γ xs
  | scale {Γ : Context} {xs : Is} :
    ℕ → TExpr Γ xs → TExpr Γ xs
  | const {Γ : Context} :
    (xs : Is) → (NIndex xs → S) → TExpr Γ xs
  | var {Γ : Context} :
    (dims : List Dim) →
    (neq : Unique dims) →
    (dims.map Prod.snd ∈ᵘ Γ) →
    TExpr Γ (fromList dims neq)
  | let {Γ : Context} {xs : Is} :
    (dims : List Dim) →
    (neq : Unique dims) →
    (wt₁ : TExpr Γ (fromList dims neq)) →
    (wt₂ : TExpr (Γ `, (dims.map Prod.snd)) xs) →
    TExpr Γ xs

inductive TExprSeq {S : Type} [Semiring S] :
  Context → List Is → Type where
  | nil {Γ : Context} : TExprSeq Γ []
  | cons {Γ : Context} {xs : Is} {xss : List Is} :
    TExpr Γ xs →
    TExprSeq Γ xss →
    TExprSeq Γ (xs :: xss)
end

notation "⟦⟧" => TExprSeq.nil
infixr:67 " ∷ₜ " => TExprSeq.cons
notation "⟦" x "⟧" => TExprSeq.cons x TExprSeq.nil
notation "⟦" x ", " y "⟧" => TExprSeq.cons x (TExprSeq.cons y TExprSeq.nil)

end TensorExpr
