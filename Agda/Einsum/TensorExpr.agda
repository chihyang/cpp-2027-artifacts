{-# OPTIONS --without-K #-}
module Einsum.TensorExpr where

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
open import Einsum.UnnamedIndex

infix  4 _∈_
infixl 5 _`,_

data Context : Set where
  ∅   : Context
  _`,_ : Context → List UpperBound → Context

𝕋ᵘ⦅_⦆ : (dims : List UpperBound) → Set
𝕋ᵘ⦅ dims ⦆ = ℐᵘ⦅ dims ⦆ → ℕ

Env : Context → Set
Env ∅ = ⊤
Env (Γ `, Idx) = Env Γ × 𝕋ᵘ⦅ Idx ⦆

data _∈_ : List UpperBound → Context → Set where

  Z : ∀ {Γ A}
      ---------
    → A ∈ Γ `, A

  S_ : ∀ {Γ A B}
    → A ∈ Γ
      ---------
    → A ∈ Γ `, B

lookupᵘ : {Γ : Context} → {ds : List UpperBound} →
  (ds ∈ Γ) → (E : Env Γ) → 𝕋ᵘ⦅ ds ⦆
lookupᵘ {Γ `, x} Z (ts , t) = t
lookupᵘ {Γ `, x} (S v) (ts , t) = lookupᵘ {Γ} v ts

data 𝕋  : Context → Is → Set
data 𝕋𝕊 : {n : ℕ} → Context → Vec Is n → Set

data 𝕋 where
  scalar : {{Γ : Context}}  → (v : ℕ) → 𝕋 Γ empty
  zero   : {{Γ : Context}} → (xs : Is) → 𝕋 Γ xs
  expand : {{Γ : Context}} → {xs zs : Is} →
           (WE : 𝕋 Γ xs) →
           (xs⊑zs : xs ⊑ zs) →
           ----------------
           𝕋 Γ zs
  einsum : {{Γ : Context}} →
           {n : ℕ} →
           {xss : Vec Is n} →
           {zs : Is} →
           (WEs : 𝕋𝕊 Γ xss) →
           (xss∼ : ∼̌ xss) →
           (zs≈xss : zs ⊑ ⨆ xss xss∼) →
           ----------------
           𝕋 Γ zs
  plus   : {{Γ : Context}} → {xs ys : Is} →
          (WE₁ : 𝕋 Γ xs) →
          (WE₂ : 𝕋 Γ ys) →
          (xs₁≈xs₂ : xs ≈ ys) →
          -----------------
          𝕋 Γ xs
  _·_   : {{Γ : Context}} → {xs : Is} →
          (s : ℕ)
          (WE : 𝕋 Γ xs) →
          -----------------
          𝕋 Γ xs
  const : {{Γ : Context}} →
          (xs : Is) →
          (f : (ℐ⦅ xs ⦆ → ℕ)) →
          -----------------
          𝕋 Γ xs
  var   : {{Γ : Context}} →
          (dims : List (Id × UpperBound)) →
          (neq : Unique (map proj₁ dims)) →
          (v : (map proj₂ dims) ∈ Γ) →
          -----------------
          𝕋 Γ (fromList dims neq)
  bind  : {{Γ : Context}} → {xs : Is} →
          (dims : List (Id × UpperBound)) →
          (neq : Unique (map proj₁ dims)) →
          (WE₁ : 𝕋 Γ (fromList dims neq)) →
          (WE₂ : 𝕋 (Γ `, (map proj₂ dims)) xs) →
          -----------------
          𝕋 Γ xs

data 𝕋𝕊 where
  nil  : {Γ : Context} → 𝕋𝕊 Γ []
  cons : {Γ : Context} → {n : ℕ} →
         {xs : Is} → {xss : Vec Is n} →
         𝕋 Γ xs →
         𝕋𝕊 Γ xss →
         ------------------
         𝕋𝕊 Γ (xs ∷ xss)

_⟦_⟧ₜ : {Γ : Context} → {n : ℕ} → {xss : Vec Is n} →
  𝕋𝕊 Γ xss → (i : Fin n) → 𝕋 Γ (at xss i)
_⟦_⟧ₜ {Γ} {n} (cons WE WEs) fz = WE
_⟦_⟧ₜ {Γ} {n} (cons WE WEs) (fs i) = WEs ⟦ i ⟧ₜ
