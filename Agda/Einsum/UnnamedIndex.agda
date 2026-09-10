{-# OPTIONS --without-K #-}
module Einsum.UnnamedIndex where

open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.Fin.Base using (Fin; fromℕ<) renaming (zero to fz; suc to fs)
open import Data.List.Base using (List; []; _∷_; map; allFin; foldl)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_; All)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; z<s; s<s)
open import Data.Nat.Properties using (<-trans; n<1+n; _≟_)
open import Data.Product.Base using (∃-syntax; _×_; proj₁; proj₂; _,_)
open import Data.Vec.Base using (Vec; _∷_; []) renaming (lookup to at)
open import Data.String.Base using (String)
open import Data.Nat using (_≟_; _*_) renaming (_+_ to _ℕ+_)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using
  (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst; inspect; [_])
open Eq.≡-Reasoning
open import Data.Product.Base using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Axiom.UniquenessOfIdentityProofs
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Einsum.NamedShape
open import Einsum.ShapeOperations
open import Einsum.ShapeProperties
open import Einsum.NamedIndex

ℐᵘ⦅_⦆ : (dims : List UpperBound) → Set
ℐᵘ⦅ [] ⦆ = ⊤
ℐᵘ⦅ d ∷ ds ⦆ = Fin d × ℐᵘ⦅ ds ⦆

ℐᵘ-nil : (idx₁ idx₂ : ℐᵘ⦅ [] ⦆) → idx₁ ≡ idx₂
ℐᵘ-nil tt tt = refl

castⁿ :
  (xs : List (Id × UpperBound)) →
  (neq : Unique (map proj₁ xs)) →
  ℐ⦅ fromList xs neq ⦆ →
  ℐᵘ⦅ map proj₂ xs ⦆
castⁿ [] [] x = tt
castⁿ ((x , u) ∷ xs) (x∉xs ∷ neq) idx =
  ⟨ idx {x} {u} (lookupₗ-head=just x u xs) ,
    castⁿ xs neq
      (λ {i} {v} eq →
        idx {i} {v}
          (trans
            (lookupₗ-tail x u xs i (lookupₗ-tail-inv x v xs neq x∉xs i v eq))
            eq)) ⟩

castᵘ :
  (xs : List (Id × UpperBound)) →
  (neq : Unique (map proj₁ xs)) →
  ℐᵘ⦅ map proj₂ xs ⦆ →
  ℐ⦅ fromList xs neq ⦆
castᵘ [] [] tt = λ ()
castᵘ (⟨ x , u ⟩ ∷ xs) (x∉xs ∷ neq) ⟨ uj , idx ⟩ {i} {v} eq with i ≟ x
... | yes i=x = subst (λ n → Fin n) (just-inj eq) uj
... | no  i≠x = castᵘ xs neq idx eq
