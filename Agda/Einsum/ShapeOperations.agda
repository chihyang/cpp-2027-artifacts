{-# OPTIONS --without-K #-}
module Einsum.ShapeOperations where

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

lookupₗ-head=just :
  (i : Id) → (u : UpperBound) →
  (pairs : List 𝒟) →
  lookupₗ (⟨ i , u ⟩ ∷ pairs) i ≡ just u
lookupₗ-head=just i u pairs with i ≟ i
... | yes i=i = refl
... | no  i≠i = ⊥-elim (i≠i refl)

lookupₗ-fresh :
  (i : Id) →
  (pairs : List 𝒟) →
  All (i ≢_) (map proj₁ pairs) →
  lookupₗ pairs i ≡ nothing
lookupₗ-fresh i [] [] = refl
lookupₗ-fresh i (⟨ j , u ⟩ ∷ pairs) (i≠j ∷ neq) with i ≟ j
... | yes i=j = ⊥-elim (i≠j i=j)
... | no  i≠j' = lookupₗ-fresh i pairs neq

lookupₗ-nothing-all :
  (i : Id) →
  (pairs : List 𝒟) →
  lookupₗ pairs i ≡ nothing →
  All (i ≢_) (map proj₁ pairs)
lookupₗ-nothing-all i [] eq = []
lookupₗ-nothing-all i (⟨ j , u ⟩ ∷ pairs) eq with i ≟ j
lookupₗ-nothing-all i (⟨ j , u ⟩ ∷ pairs) () | yes i=j
... | no i≠j = i≠j ∷ lookupₗ-nothing-all i pairs eq

lookupₗ-tail :
  (i : Id) → (u : UpperBound) →
  (pairs : List 𝒟) →
  (j : Id) →
  j ≢ i →
  lookupₗ (⟨ i , u ⟩ ∷ pairs) j ≡ lookupₗ pairs j
lookupₗ-tail i u pairs j j≠i with j ≟ i
... | yes j=i = ⊥-elim (j≠i j=i)
... | no  _ = refl

lookupₗ-tail-inv :
  (x : Id) →
  (u : UpperBound) →
  (pairs : List 𝒟) →
  (neq : Unique (map proj₁ pairs)) →
  (x∉pairs : All (x ≢_) (map proj₁ pairs)) →
  (i : Id) →
  (v : UpperBound) →
  (eq : lookupₗ pairs i ≡ just u) →
  i ≢ x
lookupₗ-tail-inv x u [] [] [] i v ()
lookupₗ-tail-inv x u (⟨ x' , u' ⟩ ∷ pairs) (x'∉pairs ∷ neq) (x≠x' ∷ x∉pairs) i v eq
  with i ≟ x'
... | yes i=x' = λ i=x → x≠x' (trans (sym i=x) i=x')
... | no  i≠x' = lookupₗ-tail-inv x u pairs neq x∉pairs i v eq

∼-tail : (i : Id) → (u : UpperBound) →
  (pairs₁ pairs₂ : List 𝒟) →
  (nei : All (i ≢_) (map proj₁ pairs₁)) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : ((⟨ i , u ⟩ ∷ pairs₁) has (nei ∷ neq₁)) ∼ (pairs₂ has neq₂)) →
  ((pairs₁ has neq₁) ∼ (pairs₂ has neq₂))
∼-tail i u pairs₁ pairs₂ nei neq₁ neq₂ Γ≈Δ j with j ≟ i
... | no  j≠i = subst (λ v → v ∼ᵢ lookupₗ pairs₂ j) (lookupₗ-tail i u pairs₁ j j≠i) (Γ≈Δ j)
... | yes refl rewrite lookupₗ-fresh i pairs₁ nei with lookupₗ pairs₂ i
... | just v = ~nv v
... | nothing = ~n

∪ₗ : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  List 𝒟
∪ₗ [] pairs₂ neq₁ neq₂ Γ≈Δ = pairs₂
∪ₗ (⟨ id , u ⟩ ∷ pairs₁) pairs₂ (x₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookup (pairs₂ has neq₂) id
... | just x  = ∪ₗ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ x₁ neq₁ neq₂ Γ≈Δ)
... | nothing = ⟨ id , u ⟩ ∷ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ x₁ neq₁ neq₂ Γ≈Δ))

∪ₗ-fresh :
  (i : Id) →
  (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  All (i ≢_) (map proj₁ pairs₁) →
  All (i ≢_) (map proj₁ pairs₂) →
  All (i ≢_) (map proj₁ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ))
∪ₗ-fresh i [] pairs₂ [] neq₂ Γ≈Δ [] i∉pairs₂ = i∉pairs₂
∪ₗ-fresh i (⟨ j , u ⟩ ∷ pairs₁) pairs₂ (j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ (i≠j ∷ i∉pairs₁) i∉pairs₂
  with lookup (pairs₂ has neq₂) j
... | just x =
  ∪ₗ-fresh i pairs₁ pairs₂ neq₁ neq₂
    (∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ)
    i∉pairs₁ i∉pairs₂
... | nothing =
  i≠j ∷
  ∪ₗ-fresh i pairs₁ pairs₂ neq₁ neq₂
    (∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ)
    i∉pairs₁ i∉pairs₂

∪ᵤ : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  Unique (map proj₁ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ))
∪ᵤ [] pairs₂ [] neq₂ Γ≈Δ = neq₂
∪ᵤ (⟨ id , u ⟩ ∷ pairs₁) pairs₂ (x ∷ neq₁) neq₂ Γ≈Δ
  with lookup (pairs₂ has neq₂) id | inspect (lookup (pairs₂ has neq₂)) id
... | just v | [ eq ] = ∪ᵤ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ x neq₁ neq₂ Γ≈Δ)
... | nothing | [ eq ] =
  let Γ≈Δ-tail = (∼-tail id u pairs₁ pairs₂ x neq₁ neq₂ Γ≈Δ)
  in
  ∪ₗ-fresh id pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ-tail x (lookupₗ-nothing-all id pairs₂ eq)
  ∷
  ∪ᵤ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ-tail

∪ : (Γ Δ : Is) → (Γ≈Δ : Γ ∼ Δ) → Is
∪ (pairs₁ has neq₁) (pairs₂ has neq₂) Γ≈Δ =
  (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ) has (∪ᵤ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ)

∩ₗ : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  List 𝒟
∩ₗ [] pairs₂ neq₁ neq₂ Γ≈Δ = []
∩ₗ (⟨ id , u ⟩ ∷ pairs₁) pairs₂ (x₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookup (pairs₂ has neq₂) id
... | just x  = ⟨ id , u ⟩ ∷ ∩ₗ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ x₁ neq₁ neq₂ Γ≈Δ)
... | nothing = (∩ₗ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ x₁ neq₁ neq₂ Γ≈Δ))

∩ₗ-fresh :
  (i : Id) → (v : UpperBound) →
  (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  All (i ≢_) (map proj₁ pairs₁) →
  lookupₗ pairs₂ i ≡ just v →
  All (i ≢_) (map proj₁ (∩ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ))
∩ₗ-fresh i v [] pairs₂ [] neq₂ Γ≈Δ [] eq = []
∩ₗ-fresh i v (⟨ j , u ⟩ ∷ pairs₁) pairs₂ (j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ (i≠j ∷ i∉pairs₁) eq
  with lookup (pairs₂ has neq₂) j | inspect (lookup (pairs₂ has neq₂)) j
... | just x  | [ eq' ] =
  i≠j ∷
  ∩ₗ-fresh i v pairs₁ pairs₂ neq₁ neq₂
    (∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ)
    i∉pairs₁ eq
... | nothing | [ eq' ] =
  ∩ₗ-fresh i v pairs₁ pairs₂ neq₁ neq₂
    (∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ)
    i∉pairs₁ eq

∩ᵤ : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  Unique (map proj₁ (∩ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ))
∩ᵤ [] pairs₂ [] neq₂ Γ≈Δ = []
∩ᵤ (⟨ id , u ⟩ ∷ pairs₁) pairs₂ (id∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookup (pairs₂ has neq₂) id | inspect (lookup (pairs₂ has neq₂)) id
... | nothing | [ eq ] = ∩ᵤ pairs₁ pairs₂ neq₁ neq₂ (∼-tail id u pairs₁ pairs₂ id∉pairs₁ neq₁ neq₂ Γ≈Δ)
... | just v  | [ eq ] =
  let Γ≈Δ-tail = (∼-tail id u pairs₁ pairs₂ id∉pairs₁ neq₁ neq₂ Γ≈Δ)
  in
  ∩ₗ-fresh id v pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ-tail id∉pairs₁ eq
  ∷
  ∩ᵤ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ-tail

∩ : (Γ Δ : Is) → (Γ≈Δ : Γ ∼ Δ) → Is
∩ (pairs₁ has neq₁) (pairs₂ has neq₂) Γ≈Δ =
  (∩ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ) has (∩ᵤ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ)

lookupₗ-∪-tail :
  (i i' : Id) → (u' : UpperBound) →
  (i≠i' : i ≢ i') →
  (pairs₁ pairs₂ : List 𝒟) →
  (i'∉pairs₁ : All (i' ≢_) (map proj₁ pairs₁))
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : ((⟨ i' , u' ⟩ ∷ pairs₁) has (i'∉pairs₁ ∷ neq₁)) ∼ (pairs₂ has neq₂)) →
  let Γ-tail≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)
      Γ-tail≈Δ = ∼-tail i' u' pairs₁ pairs₂ i'∉pairs₁ neq₁ neq₂ Γ≈Δ
  in lookupₗ (∪ₗ (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ) i ≡
     lookupₗ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ-tail≈Δ) i
lookupₗ-∪-tail i i' u' i≠i' pairs₁ pairs₂ i'∉pairs₁ neq₁ neq₂ Γ≈Δ
  with i ≟ i' | lookup (pairs₂ has neq₂) i' | inspect (lookup (pairs₂ has neq₂)) i'
... | yes i=i' | _       | [ eq ] = ⊥-elim (i≠i' i=i')
... | no i≠i'  | just x  | [ eq ] = refl
... | no i≠i'  | nothing | [ eq ] = lookupₗ-tail i' u' _ i i≠i'

lookupₗ-∪-fresh-left :
  (i : Id) →
  (pairs₁ pairs₂ : List 𝒟) →
  (i∉pairs₁ : All (i ≢_) (map proj₁ pairs₁)) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  lookupₗ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ) i ≡ lookupₗ pairs₂ i
lookupₗ-∪-fresh-left i [] pairs₂ [] [] neq₂ Γ≈Δ = refl
lookupₗ-∪-fresh-left i (⟨ j , u ⟩ ∷ pairs₁) pairs₂ (i≠j ∷ i∉pairs₁) (j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookupₗ pairs₂ i | inspect (lookupₗ pairs₂) i | i ≟ j
... | _       | [ eq ] | yes i=j = ⊥-elim (i≠j i=j)
... | nothing | [ eq ] | no i≠j  =
    let Γ≈Δ↓ = ∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ
        IH = lookupₗ-∪-fresh-left i pairs₁ pairs₂ i∉pairs₁ neq₁ neq₂ Γ≈Δ↓
        eq₁ = lookupₗ-∪-tail i j u i≠j pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ
    in trans (trans eq₁ IH) eq
... | just x' | [ eq' ] | no i≠j =
    let Γ≈Δ↓ = ∼-tail j u pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ
        IH = lookupₗ-∪-fresh-left i pairs₁ pairs₂ i∉pairs₁ neq₁ neq₂ Γ≈Δ↓
        eq₁ = lookupₗ-∪-tail i j u i≠j pairs₁ pairs₂ j∉pairs₁ neq₁ neq₂ Γ≈Δ
        eq₂ = trans eq₁ IH
    in trans eq₂ eq'

lookupₗ-∪-head :
  (i : Id) → (u : UpperBound) →
  (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ (⟨ i , u ⟩ ∷ pairs₁))) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : ((⟨ i , u ⟩ ∷ pairs₁) has neq₁) ∼ (pairs₂ has neq₂)) →
  lookupₗ (∪ₗ (⟨ i , u ⟩ ∷ pairs₁) pairs₂ neq₁ neq₂ Γ≈Δ) i ≡ just u
lookupₗ-∪-head i u [] pairs₂ (i∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookupₗ pairs₂ i | inspect (lookupₗ pairs₂) i
... | nothing | [ _ ] = lookupₗ-head=just i u pairs₂
... | just x  | [ eq ] = just-∼ᵢ-= u x (lookupₗ pairs₂ i) eq' eq where
  eq' : just u ∼ᵢ lookupₗ pairs₂ i
  eq' = subst (_∼ᵢ lookupₗ pairs₂ i) (lookupₗ-head=just i u []) (Γ≈Δ i)
lookupₗ-∪-head i u (⟨ j , v ⟩ ∷ pairs₁) pairs₂ ((i≠j ∷ i∉pairs₁) ∷ j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ
  with lookupₗ pairs₂ i | inspect (lookupₗ pairs₂) i | i ≟ j
... | nothing | [ _ ]  | _ = lookupₗ-head=just i u _
... | just x  | [ eq ] | yes i=j = ⊥-elim (i≠j i=j)
... | just x  | [ eq ] | no _ =
    let Γ≈Δ↓ : ((⟨ j , v ⟩ ∷ pairs₁) has (j∉pairs₁ ∷ neq₁)) ∼ (pairs₂ has neq₂)
        Γ≈Δ↓ = (∼-tail i u (⟨ j , v ⟩ ∷ pairs₁) pairs₂ (i≠j ∷ i∉pairs₁) (j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ)
        eq₁ = lookupₗ-∪-fresh-left i (⟨ j , v ⟩ ∷ pairs₁) pairs₂ (i≠j ∷ i∉pairs₁) (j∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ↓

        eq₂ = lookupₗ-head=just i u (⟨ j , v ⟩ ∷ pairs₁)

        u∼ᵢ : just u ∼ᵢ lookupₗ pairs₂ i
        u∼ᵢ = subst (_∼ᵢ lookupₗ pairs₂ i) eq₂ (Γ≈Δ i)

        eq₃ : (lookupₗ pairs₂ i) ≡ just u
        eq₃ = just-∼ᵢ-= u x (lookupₗ pairs₂ i) u∼ᵢ eq
    in trans eq₁ eq₃

lookupₗ-∪ :
  (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (Γ≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)) →
  (i : Id) →
  lookupₗ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ) i ≡
    (_⊔ᵢ_ (lookupₗ pairs₁ i) (lookupₗ pairs₂ i) {Γ≈Δ i})
lookupₗ-∪ [] pairs₂ [] neq₂ Γ≈Δ i = refl
lookupₗ-∪ (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ i with i ≟ i' | Γ≈Δ i
... | yes i=i' | u'∼ᵢ rewrite i=i' | ⊔ᵢ-just-left {u'} {lookupₗ pairs₂ i'} u'∼ᵢ =
    lookupₗ-∪-head i' u' pairs₁ pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ
... | no  i≠i' | Γi∼Δi = trans (trans eq₁ eq₂) (sym eq₃) where
    Γ-tail≈Δ : (pairs₁ has neq₁) ∼ (pairs₂ has neq₂)
    Γ-tail≈Δ = ∼-tail i' u' pairs₁ pairs₂ i'∉pairs₁ neq₁ neq₂ Γ≈Δ

    eq₁ : lookupₗ (∪ₗ (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ Γ≈Δ) i ≡
          lookupₗ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ-tail≈Δ) i
    eq₁ = lookupₗ-∪-tail i i' u' i≠i' pairs₁ pairs₂ i'∉pairs₁ neq₁ neq₂ Γ≈Δ

    eq₂ : lookupₗ (∪ₗ pairs₁ pairs₂ neq₁ neq₂ Γ-tail≈Δ) i ≡
          _⊔ᵢ_ (lookupₗ pairs₁ i) (lookupₗ pairs₂ i) {Γ-tail≈Δ i}
    eq₂ = lookupₗ-∪ pairs₁ pairs₂ neq₁ neq₂ Γ-tail≈Δ i

    eq₃ : _⊔ᵢ_ (lookupₗ pairs₁ i) (lookupₗ pairs₂ i) {Γi∼Δi} ≡
          _⊔ᵢ_ (lookupₗ pairs₁ i) (lookupₗ pairs₂ i) {Γ-tail≈Δ i}
    eq₃ = ⊔ᵢ-irr Γi∼Δi (Γ-tail≈Δ i)

lookup-∪ : (Γ Δ : Is) →
  (Γ≈Δ : Γ ∼ Δ) →
  (i : Id) →
  lookup (∪ Γ Δ Γ≈Δ) i ≡ (_⊔ᵢ_ (lookup Γ i) (lookup Δ i) {Γ≈Δ i})
lookup-∪ (pairs₁ has neq₁) (pairs₂ has neq₂) Γ≈Δ i =
  lookupₗ-∪ pairs₁ pairs₂ neq₁ neq₂ Γ≈Δ i

lookup-∪-just : (Γ Δ : Is) →
  (Γ∼Δ : Γ ∼ Δ) →
  (i : Id) →
  (u : UpperBound) →
  lookup (∪ Γ Δ Γ∼Δ) i ≡ just u →
  (lookup Γ i ≡ just u) ⊎ (lookup Δ i ≡ just u)
lookup-∪-just Γ Δ Γ∼Δ i u eq rewrite lookup-∪ Γ Δ Γ∼Δ i =
  ⊔ᵢ-just-inv (Γ∼Δ i) eq

lookup-∪-nothing : (Γ Δ : Is) →
  (Γ∼Δ : Γ ∼ Δ) →
  (i : Id) →
  lookup (∪ Γ Δ Γ∼Δ) i ≡ nothing →
  (lookup Γ i ≡ nothing) × (lookup Δ i ≡ nothing)
lookup-∪-nothing Γ Δ Γ∼Δ i eq rewrite lookup-∪ Γ Δ Γ∼Δ i =
  ⊔ᵢ-nothing-inv (Γ∼Δ i) eq

∪-∼ : (Γ Δ : Is) →
  (Γ∼Δ : Γ ∼ Δ) →
  (∪ Γ Δ Γ∼Δ ∼ Γ) × (∪ Γ Δ Γ∼Δ ∼ Δ)
∪-∼ Γ Δ Γ∼Δ = left , right where
  left : ∪ Γ Δ Γ∼Δ ∼ Γ
  left i rewrite lookup-∪ Γ Δ Γ∼Δ i =
    ⊔ᵢ-∼ᵢ-left (lookup Γ i) (lookup Δ i) (Γ∼Δ i)

  right : ∪ Γ Δ Γ∼Δ ∼ Δ
  right i rewrite lookup-∪ Γ Δ Γ∼Δ i =
    ⊔ᵢ-∼ᵢ-right (lookup Γ i) (lookup Δ i) (Γ∼Δ i)

∼-∪ : (Γ Δ Ω : Is) →
  (Γ∼Δ : Γ ∼ Δ) →
  (Γ∼Ω : Γ ∼ Ω) →
  (Δ∼Ω : Δ ∼ Ω) →
  Γ ∼ ∪ Δ Ω Δ∼Ω
∼-∪ Γ Δ Ω Γ∼Δ Γ∼Ω Δ∼Ω i
  rewrite lookup-∪ Δ Ω Δ∼Ω i =
  ∼ᵢ-⊔ᵢ-right (Γ∼Δ i) (Γ∼Ω i) {Δ∼Ω i}

⨆ : {n : ℕ} → (Γs : Vec Is n) → (Γs~ : ∼̌ Γs) → Is
head≈⨆ : {n : ℕ} → {Γ : Is} → {Γs : Vec Is n} →
          (Γ∷Γs~ : ∼̌ (Γ ∷ Γs)) → Γ ∼ ⨆ Γs (∼̌-tail Γ∷Γs~)

⨆ {zero} [] Γs~ = empty
⨆ {suc n} (Γ ∷ Γs) Γ∷Γs~ = ∪ Γ (⨆ Γs (∼̌-tail Γ∷Γs~)) (head≈⨆ Γ∷Γs~)

head≈⨆ {zero} {Γ} {[]} Γs~ = ∼-sym {empty} {Γ} (empty∼ Γ)
head≈⨆ {suc n} {Γ} {Δ ∷ Γs} Γ∷Γs~ i =
  let
    Γs∼̌ = ∼̌↘ {n} Γ Δ Γs Γ∷Γs~
    Δ∼Γs = head≈⨆ {Γ = Δ} {Γs = Γs} (∼̌-tail Γ∷Γs~)
    Γ∼Γs = head≈⨆ {Γ = Γ} {Γs = Γs} Γs∼̌
    ⨆Γs = ⨆ Γs (∼̌-tail (∼̌-tail Γ∷Γs~))
    z~s = (Γ∷Γs~ fz (fs fz)) i
    z~ss = Γ∼Γs i
    s~ss = Δ∼Γs i
    eq = lookup-∪ Δ ⨆Γs Δ∼Γs i
  in subst (lookup Γ i ∼ᵢ_) (sym eq) (∼ᵢ-⊔ᵢ-right z~s z~ss {s~ss})

_∖ₗ_ : List 𝒟 → List 𝒟 → List 𝒟
[] ∖ₗ ds₂ = []
(⟨ i , u ⟩ ∷ ds₁) ∖ₗ ds₂ with lookupₗ ds₂ i
... | just _  = ds₁ ∖ₗ ds₂
... | nothing = ⟨ i , u ⟩ ∷ (ds₁ ∖ₗ ds₂)

∖ᵤ-head : (i : Id) → (u : UpperBound) →
  (ds₁ ds₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ (⟨ i , u ⟩ ∷ ds₁))) →
  (neq₂ : Unique (map proj₁ ds₂)) →
  All (i ≢_) (map proj₁ (ds₁ ∖ₗ ds₂))
∖ᵤ-head i u [] ds₂ neq₁ neq₂ = []
∖ᵤ-head i u (⟨ i' , u' ⟩ ∷ ds₁) ds₂ ((i≢i' ∷ i∉ds₁) ∷ (_ ∷ neq₁)) neq₂ with i ≟ i'
... | yes i=i' = ⊥-elim (i≢i' i=i')
... | no  i≠i' with lookupₗ ds₂ i'
... | just _  = ∖ᵤ-head i u ds₁ ds₂ (i∉ds₁ ∷ neq₁) neq₂
... | nothing = i≢i' ∷ ∖ᵤ-head i u ds₁ ds₂ (i∉ds₁ ∷ neq₁) neq₂

_∖ᵤ_ : {ds₁ ds₂ : List 𝒟} →
  (neq₁ : Unique (map proj₁ ds₁)) →
  (neq₂ : Unique (map proj₁ ds₂)) →
  Unique (map proj₁ (ds₁ ∖ₗ ds₂))
_∖ᵤ_ {[]} {ds₂} [] neq₂ = []
_∖ᵤ_ {⟨ i , u ⟩ ∷ ds₁} {ds₂} (x ∷ neq₁) neq₂ with lookupₗ ds₂ i
...  | just _  = neq₁ ∖ᵤ neq₂
...  | nothing = ∖ᵤ-head i u ds₁ ds₂ (x ∷ neq₁) neq₂ ∷ (neq₁ ∖ᵤ neq₂)

_∖_ : Is → Is → Is
(pairs₁ has neq₁) ∖ (pairs₂ has neq₂) = (pairs₁ ∖ₗ pairs₂) has (neq₁ ∖ᵤ neq₂)

∖ₗ-⊥-lookup-nothing : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (i : Id) →
  (eq : lookupₗ pairs₁ i ≡ nothing) →
  (lookupₗ (pairs₁ ∖ₗ pairs₂) i ≡ nothing)
∖ₗ-⊥-lookup-nothing [] pairs₂ neq₁ neq₂ i eq = refl
∖ₗ-⊥-lookup-nothing (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ i eq
  with i ≟ i'
... | yes i=i' rewrite i=i' = ⊥-elim (just≢nothing eq)
... | no i≠i' rewrite lookupₗ-tail i' u' pairs₁ i i≠i'
  with lookupₗ pairs₂ i'
... | just _ =
  ∖ₗ-⊥-lookup-nothing pairs₁ pairs₂ neq₁ neq₂ i eq
... | nothing
  rewrite lookupₗ-tail i' u' (pairs₁ ∖ₗ pairs₂) i i≠i' =
  ∖ₗ-⊥-lookup-nothing pairs₁ pairs₂ neq₁ neq₂ i eq

lookupₗ-∖ᵢ : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (i : Id) →
  lookupₗ (pairs₁ ∖ₗ pairs₂) i ≡ lookupₗ pairs₁ i ∖ᵢ lookupₗ pairs₂ i
lookupₗ-∖ᵢ [] pairs₂ neq₁ neq₂ i = refl
lookupₗ-∖ᵢ (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ i
  with i ≟ i' | lookupₗ pairs₂ i' | inspect (lookupₗ pairs₂) i'
... | yes i=i' | just _ | [ i'∈pairs₂ ] rewrite i=i' | i'∈pairs₂ =
  ∖ₗ-⊥-lookup-nothing pairs₁ pairs₂ neq₁ neq₂ i' (lookupₗ-fresh i' pairs₁ i'∉pairs₁)
... | yes i=i' | nothing | [ i'∉pairs₂ ] rewrite i=i' | i'∉pairs₂ =
  lookupₗ-head=just i' u' (pairs₁ ∖ₗ pairs₂)
... | no i≠i' | just _ | [ i'∈pairs₂ ] rewrite lookupₗ-tail i' u' pairs₁ i i≠i' | i'∈pairs₂ =
  lookupₗ-∖ᵢ pairs₁ pairs₂ neq₁ neq₂ i
... | no i≠i' | nothing | [ i'∉pairs₂ ]
  rewrite lookupₗ-tail i' u' pairs₁ i i≠i'
        | i'∉pairs₂
        | lookupₗ-tail i' u' (pairs₁ ∖ₗ pairs₂) i i≠i' =
  lookupₗ-∖ᵢ pairs₁ pairs₂ neq₁ neq₂ i

lookup-∖ : (Γ Δ : Is) →
  (i : Id) →
  lookup (Γ ∖ Δ) i ≡ lookup Γ i ∖ᵢ lookup Δ i
lookup-∖ (pairs₁ has neq₁) (pairs₂ has neq₂) i =
  lookupₗ-∖ᵢ pairs₁ pairs₂ neq₁ neq₂ i
