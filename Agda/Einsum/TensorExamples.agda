{-# OPTIONS --without-K #-}
module Einsum.TensorExamples where

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
open import Einsum.TensorExpr
open import Einsum.TensorDenotation
open import Einsum.ExpandProperties

-- One example
x⁽²⁾ : Is
x⁽²⁾ = (⟨ 0 , 2 ⟩ ∷ []) has ([] ∷ [])

y⁽³⁾ : Is
y⁽³⁾ = (⟨ 1 , 3 ⟩ ∷ []) has ([] ∷ [])

z⁽⁴⁾ : Is
z⁽⁴⁾ = (⟨ 2 , 4 ⟩ ∷ []) has ([] ∷ [])

x⁽²⁾≈y⁽³⁾ : x⁽²⁾ ∼ y⁽³⁾
x⁽²⁾≈y⁽³⁾ zero = ~vn 2
x⁽²⁾≈y⁽³⁾ (suc zero) = ~nv 3
x⁽²⁾≈y⁽³⁾ (suc (suc idx)) = ~n

x⁽²⁾y⁽³⁾ : Is
x⁽²⁾y⁽³⁾ = ∪ x⁽²⁾ y⁽³⁾ x⁽²⁾≈y⁽³⁾

x⁽²⁾y⁽³⁾≈z⁽⁴⁾ : x⁽²⁾y⁽³⁾ ∼ z⁽⁴⁾
x⁽²⁾y⁽³⁾≈z⁽⁴⁾ zero = ~vn 2
x⁽²⁾y⁽³⁾≈z⁽⁴⁾ (suc zero) = ~vn 3
x⁽²⁾y⁽³⁾≈z⁽⁴⁾ (suc (suc zero)) = ~nv 4
x⁽²⁾y⁽³⁾≈z⁽⁴⁾ (suc (suc (suc v))) = ~n

x⁽²⁾y⁽³⁾z⁽⁴⁾ : Is
x⁽²⁾y⁽³⁾z⁽⁴⁾ = ∪ x⁽²⁾y⁽³⁾ z⁽⁴⁾ x⁽²⁾y⁽³⁾≈z⁽⁴⁾

x⁽²⁾⊑x⁽²⁾y⁽³⁾ : x⁽²⁾ ⊑ x⁽²⁾y⁽³⁾
x⁽²⁾⊑x⁽²⁾y⁽³⁾ zero _ eq = eq

x⁽²⁾y⁽³⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾ : x⁽²⁾y⁽³⁾ ⊑ x⁽²⁾y⁽³⁾z⁽⁴⁾
x⁽²⁾y⁽³⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾ zero _ e = e
x⁽²⁾y⁽³⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾ (suc zero) _ e = e

x⁽²⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾ : x⁽²⁾ ⊑ x⁽²⁾y⁽³⁾z⁽⁴⁾
x⁽²⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾ zero _ e = e

x⁽²⁾→v : ℐ⦅ x⁽²⁾ ⦆ → ℕ
x⁽²⁾→v idx with idx {0} {2} refl
... | fz = 3
... | fs fz = 7

Γ : Context
Γ = ∅

E : Env Γ
E = tt

t[3,7] : 𝕋 Γ x⁽²⁾
t[3,7] = const {{Γ}} x⁽²⁾ x⁽²⁾→v

t[[3,3,3],[7,7,7]] : 𝕋 Γ x⁽²⁾y⁽³⁾
t[[3,3,3],[7,7,7]] =
  expand {{Γ}} t[3,7] x⁽²⁾⊑x⁽²⁾y⁽³⁾

t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]] : 𝕋 Γ x⁽²⁾y⁽³⁾z⁽⁴⁾
t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]] =
  expand {{Γ}} t[[3,3,3],[7,7,7]] x⁽²⁾y⁽³⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾

t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]]′ : 𝕋 Γ x⁽²⁾y⁽³⁾z⁽⁴⁾
t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]]′ =
  expand {{Γ}} t[3,7] x⁽²⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾

-- Denotational semantics
id0⁽ˣ⁾ : ℐ⦅ x⁽²⁾ ⦆
id0⁽ˣ⁾ {zero} {2} eq = fz

id1⁽ˣ⁾ : ℐ⦅ x⁽²⁾ ⦆
id1⁽ˣ⁾ {zero} {2} eq = fs fz

teq₀ : ⟦_⟧⦅_⨾_⦆ {{Γ}} t[3,7] E (λ { {x} {v} e → id0⁽ˣ⁾ {x} {v} e }) ≡ 3
teq₀ = refl {x = ⟦_⟧⦅_⨾_⦆ {{Γ}} t[3,7] E (λ { {x} {v} e → id0⁽ˣ⁾ {x} {v} e })}

teq₁ : ⟦_⟧⦅_⨾_⦆ {{Γ}} t[3,7] E (λ { {x} {v} e → id1⁽ˣ⁾ {x} {v} e }) ≡ 7
teq₁ = refl {x = ⟦_⟧⦅_⨾_⦆ {{Γ}} t[3,7] E (λ { {x} {v} e → id1⁽ˣ⁾ {x} {v} e })}

-- Tensor equality
teq₃ : ∀ (idx : ℐ⦅ x⁽²⁾y⁽³⁾z⁽⁴⁾ ⦆) →
  ⟦_⟧⦅_⨾_⦆ {{Γ}} t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]] E (λ {i} {v} e → idx {i} {v} e) ≡
  ⟦_⟧⦅_⨾_⦆ {{Γ}} t[[[3⁽⁴⁾]⁽³⁾],[[7⁽⁴⁾]⁽³⁾]]′ E (λ {i} {v} e → idx {i} {v} e)
teq₃ =
  expand-fuse
    {{Γ}}
    {xs = x⁽²⁾} {ys = x⁽²⁾y⁽³⁾} {zs = x⁽²⁾y⁽³⁾z⁽⁴⁾}
    t[3,7]
    x⁽²⁾⊑x⁽²⁾y⁽³⁾ x⁽²⁾y⁽³⁾⊑x⁽²⁾y⁽³⁾z⁽⁴⁾
    E
