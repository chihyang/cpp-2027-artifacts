{-# OPTIONS --without-K #-}
module Einsum.ShapeProperties where

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

_⊑_ : Is → Is → Set
A ⊑ B = ∀ i up → lookup A i ≡ just up → lookup B i ≡ just up

⊑-refl : {Γ : Is} → Γ ⊑ Γ
⊑-refl = λ i up z → z

⊑-trans : {Γ₁ Γ₂ Γ₃ : Is} →
          (Γ₁ ⊑ Γ₂) →
          (Γ₂ ⊑ Γ₃) →
          (Γ₁ ⊑ Γ₃)
⊑-trans Γ₁⊑Γ₂ Γ₂⊑Γ₃ i up x = Γ₂⊑Γ₃ i up (Γ₁⊑Γ₂ i up x)

_≈_ : Is → Is → Set
Γ ≈ Δ = ∀ i → lookup Γ i ≡ lookup Δ i

≈-refl : {Γ : Is} → Γ ≈ Γ
≈-refl _ = refl

≈-sym : {Γ Δ : Is} → Γ ≈ Δ → Δ ≈ Γ
≈-sym Γ≈Δ i = sym (Γ≈Δ i)

≈-trans : {Γ₁ Γ₂ Γ₃ : Is} → Γ₁ ≈ Γ₂ → Γ₂ ≈ Γ₃ → Γ₁ ≈ Γ₃
≈-trans Γ₁≈Γ₂ Γ₂≈Γ₃ i = trans (Γ₁≈Γ₂ i) (Γ₂≈Γ₃ i)

empty-canonical : {xs : Is} → (eq : xs ≈ empty) → xs ≡ empty
empty-canonical {[] has []} eq = refl
empty-canonical {(⟨ x , u ⟩ ∷ xs) has (x∉xs ∷ neq)} eq =
  let lr = eq x
      l-head = lookupₗ-head=just x u xs
  in ⊥-elim (just≢nothing (trans (sym l-head) lr))

empty⇒∏ᶜ≡1 : ∏ᶜ empty ≡ 1
empty⇒∏ᶜ≡1 = refl

≈empty⇒∏ᶜ≡1 : {Γ : Is} → Γ ≈ empty → ∏ᶜ Γ ≡ 1
≈empty⇒∏ᶜ≡1 {Γ} Γ≈empty =
  subst (λ Δ → ∏ᶜ Δ ≡ 1)
    (sym (empty-canonical {xs = Γ} Γ≈empty)) empty⇒∏ᶜ≡1

≈⇒⊑ : {Γ Δ : Is} → Γ ≈ Δ → Γ ⊑ Δ
≈⇒⊑ Γ≈Δ i up x rewrite Γ≈Δ i = x

≈⊑-right : {Γ₂ Δ₁ Δ₂ : Is} → (Δ₁≈Δ₂ : Δ₁ ≈ Δ₂) → (Γ₂⊑Δ₂ : Γ₂ ⊑ Δ₂) → Γ₂ ⊑ Δ₁
≈⊑-right Δ₁≈Δ₂ Γ₂⊑Δ₂ i up x rewrite Δ₁≈Δ₂ i = Γ₂⊑Δ₂ i up x

≈⊑-left : {Γ₂ Δ₁ Δ₂ : Is} → (Δ₁≈Δ₂ : Δ₁ ≈ Δ₂) → (Γ₂⊑Δ₁ : Γ₂ ⊑ Δ₁) → Γ₂ ⊑ Δ₂
≈⊑-left {Γ₂} {Δ₁} {Δ₂} Δ₁≈Δ₂ Γ₂⊑Δ₁ =
  ≈⊑-right {Γ₂} {Δ₂} {Δ₁} (≈-sym {Δ₁} {Δ₂} Δ₁≈Δ₂) Γ₂⊑Δ₁

⊑∼ : {Δ Γ₁ Γ₂ : Is} → (Δ⊑Γ₁ : Δ ⊑ Γ₁) → Γ₁ ∼ Γ₂ → Δ ∼ Γ₂
⊑∼ {Δ} {Γ₁} {Γ₂} Δ⊑Γ₁ Γ₁∼Γ₂ i
  with lookup Δ i   | inspect (lookup Δ) i  |
       lookup Γ₁ i  | inspect (lookup Γ₁) i |
       lookup Γ₂ i  | inspect (lookup Γ₂) i |
       Γ₁∼Γ₂ i
... | nothing | eq1 | just x  | eq2 | just x₁ | eq3 | _ = ~nv x₁
... | nothing | eq1 | just x  | eq2 | nothing | eq3 | _ = ~n
... | nothing | eq1 | nothing | eq2 | just x  | eq3 | _ = ~nv x
... | nothing | eq1 | nothing | eq2 | nothing | eq3 | _ = ~n
... | just x  | eq1 | nothing | eq2 | nothing | eq3 | _ = ~vn x
... | just x  | eq1 | just x₁ | eq2 | nothing | eq3 | _ = ~vn x
... | just x  | [ eq1 ] | nothing | [ eq2 ] | just x₁ | [ eq3 ] | ~nv .x₁ =
  let IH = Δ⊑Γ₁ i x eq1 in
  ⊥-elim (just≢nothing (trans (sym IH) eq2))
... | just x  | [ eq1 ] | just x₁ | [ eq2 ] | just x₂ | [ eq3 ] | ~v .x₁  =
  let IH = Δ⊑Γ₁ i x eq1 in
  just-∼ᵢ (trans (sym IH) eq2)

⊑⇒∼ : {Γ Δ : Is} → Γ ⊑ Δ → Γ ∼ Δ
⊑⇒∼ {Γ} {Δ} Γ⊑Δ = ⊑∼ {Γ} {Δ} {Δ} Γ⊑Δ (∼-refl {Δ})

≈↓⊑ : {Γ₂ Δ₁ Δ₂ : Is} →
      (Δ₁≈Δ₂ : Δ₁ ≈ Δ₂) →
      (Γ₂⊑Δ₂ : Γ₂ ⊑ Δ₂) →
      Σ[ Γ₁ ∈ Is ](Γ₁ ≈ Γ₂) × (Γ₁ ⊑ Δ₁)
≈↓⊑ {Γ₂} {Δ₁} {Δ₂} Δ₁≈Δ₂ Γ₂⊑Δ₂ = Γ₂ , ≈-refl {Γ₂} , ≈⊑-right {Γ₂} {Δ₁} {Δ₂} Δ₁≈Δ₂ Γ₂⊑Δ₂

∼̌-tail⊑ : {n : ℕ} → {Δ Γ : Is} → {Γs : Vec Is n} →
     (Δ⊑Γ : Δ ⊑ Γ) → (~Γs : ∼̌ (Γ ∷ Γs)) → ∼̌ (Δ ∷ Γs)
∼̌-tail⊑ {n} {Δ} {Γ} {Γs} Δ⊑Γ ~Γs fz fz id = ∼ᵢ-refl
∼̌-tail⊑ {n} {Δ} {Γ} {Γs} Δ⊑Γ ~Γs fz (fs j) id =
  ⊑∼ {Δ} {Γ} {at Γs j} Δ⊑Γ (~Γs fz (fs j)) id
∼̌-tail⊑ {n} {Δ} {Γ} {Γs} Δ⊑Γ ~Γs (fs i) fz id =
  ∼-sym {Δ} {at Γs i} (⊑∼ {Δ} {Γ} {at Γs i} Δ⊑Γ (~Γs fz (fs i))) id
∼̌-tail⊑ {n} {Δ} {Γ} {Γs} Δ⊑Γ ~Γs (fs i) (fs j) id = ~Γs (fs i) (fs j) id

∪-comm : {Γ₁ Γ₂ : Is} →
  (Γ₁∼Γ₂ : Γ₁ ∼ Γ₂) →
  (Γ₂∼Γ₁ : Γ₂ ∼ Γ₁) →
  ∪ Γ₁ Γ₂ Γ₁∼Γ₂ ≈ ∪ Γ₂ Γ₁ Γ₂∼Γ₁
∪-comm {Γ₁} {Γ₂} Γ₁∼Γ₂ Γ₂∼Γ₁ i
  rewrite lookup-∪ Γ₁ Γ₂ Γ₁∼Γ₂ i
        | lookup-∪ Γ₂ Γ₁ Γ₂∼Γ₁ i =
  ⊔ᵢ-comm (lookup Γ₁ i) (lookup Γ₂ i) (Γ₁∼Γ₂ i) (Γ₂∼Γ₁ i)

∪-sym : {Γ₁ Γ₂ : Is} →
  (Γ₁≈Γ₂ : Γ₁ ∼ Γ₂) →
  (i : Id) →
  lookup (∪ Γ₁ Γ₂ Γ₁≈Γ₂) i ≡
  lookup (∪ Γ₂ Γ₁ (∼-sym {Γ₁} {Γ₂} Γ₁≈Γ₂)) i
∪-sym {Γ₁} {Γ₂} Γ₁≈Γ₂ =
  ∪-comm {Γ₁} {Γ₂} Γ₁≈Γ₂ (∼-sym {Γ₁} {Γ₂} Γ₁≈Γ₂)

∪-cong : {Γ₁ Γ₂ Δ₁ Δ₂ : Is} →
  (Γ₁≈Γ₂ : Γ₁ ≈ Γ₂) →
  (Δ₁≈Δ₂ : Δ₁ ≈ Δ₂) →
  (Γ₁∼Δ₁ : Γ₁ ∼ Δ₁) →
  (Γ₂∼Δ₂ : Γ₂ ∼ Δ₂) →
  ∪ Γ₁ Δ₁ Γ₁∼Δ₁ ≈ ∪ Γ₂ Δ₂ Γ₂∼Δ₂
∪-cong {Γ₁} {Γ₂} {Δ₁} {Δ₂} Γ₁≈Γ₂ Δ₁≈Δ₂ Γ₁∼Δ₁ Γ₂∼Δ₂ i
  rewrite lookup-∪ Γ₁ Δ₁ Γ₁∼Δ₁ i
        | lookup-∪ Γ₂ Δ₂ Γ₂∼Δ₂ i =
  ⊔ᵢ-cong (Γ₁≈Γ₂ i) (Δ₁≈Δ₂ i) (Γ₁∼Δ₁ i) (Γ₂∼Δ₂ i)

i∈∪ : (Γ₁ Γ₂ : Is) →
      (Γ₁≈Γ₂ : Γ₁ ∼ Γ₂) →
      (i : Id) →
      (up : UpperBound) →
      (lookup Γ₁ i ≡ just up) →
      lookup (∪ Γ₁ Γ₂ Γ₁≈Γ₂) i ≡ just up
i∈∪ Γ₁ Γ₂ Γ₁≈Γ₂ i up i∈Γ₁ rewrite lookup-∪ Γ₁ Γ₂ Γ₁≈Γ₂ i =
  trans (u≡→⊔ᵢ≡ v₁ v₂ v₃ v₁∼ᵢv₃ v₂∼ᵢv₃ i∈Γ₁) (⊔ᵢ-just-left v₂∼ᵢv₃) where
    v₁ = lookup Γ₁ i
    v₂ = just up
    v₃ = lookup Γ₂ i

    v₁∼ᵢv₃ : v₁ ∼ᵢ v₃
    v₁∼ᵢv₃ = Γ₁≈Γ₂ i

    v₂∼ᵢv₃ : v₂ ∼ᵢ v₃
    v₂∼ᵢv₃ = subst (_∼ᵢ lookup Γ₂ i) i∈Γ₁ v₁∼ᵢv₃

∪⇒∈ : (Γ₁ Γ₂ : Is) →
       (Γ₁≈Γ₂ : Γ₁ ∼ Γ₂) →
       (i : Id) →
       (up : UpperBound) →
       ((lookup Γ₁ i ≡ just up) ⊎ (lookup Γ₂ i ≡ just up)) →
       (lookup (∪ Γ₁ Γ₂ Γ₁≈Γ₂) i ≡ just up)
∪⇒∈ Γ₁ Γ₂ Γ₁≈Γ₂ i up (inj₁ i∈Γ₁) = i∈∪ Γ₁ Γ₂ Γ₁≈Γ₂ i up i∈Γ₁
∪⇒∈ Γ₁ Γ₂ Γ₁≈Γ₂ i up (inj₂ i∈Γ₂) rewrite ∪-sym {Γ₁} {Γ₂} Γ₁≈Γ₂ i =
  i∈∪ Γ₂ Γ₁ (∼-sym {Γ₁} {Γ₂} Γ₁≈Γ₂) i up i∈Γ₂

∪⇒⊑ : {Γ₁ Γ₂ Γ₃ : Is} →
       {Γ₂≈Γ₃ : Γ₂ ∼ Γ₃} →
       (Γ₁ ≈ ∪ Γ₂ Γ₃ Γ₂≈Γ₃) →
       (Γ₂ ⊑ Γ₁) × (Γ₃ ⊑ Γ₁)
∪⇒⊑ {Γ₁} {Γ₂} {Γ₃} {Γ₂≈Γ₃} Γ₁≈ =
  let IH = ∪⇒∈ Γ₂ Γ₃ Γ₂≈Γ₃ in
    (λ i up x →
      let IH₁ : lookup (∪ Γ₂ Γ₃ Γ₂≈Γ₃) i ≡ just up
          IH₁ = IH i up (inj₁ x)  in
      trans (Γ₁≈ i) IH₁) ,
    (λ i up x →
      let IH₂ : lookup (∪ Γ₂ Γ₃ Γ₂≈Γ₃) i ≡ just up
          IH₂ = IH i up (inj₂ x) in
      trans (Γ₁≈ i) IH₂)

empty-∪ : (Γ : Is) →
  (empty∼Γ : empty ∼ Γ) →
  ∪ empty Γ empty∼Γ ≈ Γ
empty-∪ Γ empty∼Γ i = trans (lookup-∪ empty Γ empty∼Γ i) refl

∪-empty : (Γ : Is) → (∪ Γ empty (∼-sym {empty} {Γ} (empty∼ Γ)) ≈ Γ)
∪-empty Γ i rewrite lookup-∪ Γ empty (∼-sym {empty} {Γ} (empty∼ Γ)) i =
  ⊔ᵢ-nothing-right′ (lookup Γ i) nothing refl

⊑∪ : {Γ₁ Γ₂ Γ₃ : Is} →
      (Γ₁ ⊑ Γ₂) →
      (Γ₂≈Γ₃ : Γ₂ ∼ Γ₃) →
      Γ₁ ⊑ ∪ Γ₂ Γ₃ Γ₂≈Γ₃
⊑∪ {Γ₁} {Γ₂} {Γ₃} Γ₁⊑Γ₂ Γ₂≈Γ₃ i up i∈Γ₁ =
  ∪⇒∈ Γ₂ Γ₃ Γ₂≈Γ₃ i up (inj₁ (Γ₁⊑Γ₂ i up i∈Γ₁))

⊑∪-cong : {Γ₁ Γ₂ Γ₃ : Is} →
  (Γ₁ ⊑ Γ₂) →
  (Γ₁≈Γ₃ : Γ₁ ∼ Γ₃) →
  (Γ₂≈Γ₃ : Γ₂ ∼ Γ₃) →
  (∪ Γ₁ Γ₃ Γ₁≈Γ₃) ⊑ (∪ Γ₂ Γ₃ Γ₂≈Γ₃)
⊑∪-cong {Γ₁} {Γ₂} {Γ₃} Γ₁⊑Γ₂ Γ₁≈Γ₃ Γ₂≈Γ₃ i rewrite lookup-∪ Γ₁ Γ₃ Γ₁≈Γ₃ i | lookup-∪ Γ₂ Γ₃ Γ₂≈Γ₃ i =
  ⊑⊔ᵢ-cong (Γ₁⊑Γ₂ i) (Γ₁≈Γ₃ i) (Γ₂≈Γ₃ i)

⨆-shrink : {n : ℕ} →
  {xs ys : Is} →
  {Γs : Vec Is n} →
  (xs⊑ys : xs ⊑ ys) →
  (ysΓs∼ : ∼̌ (ys ∷ Γs)) →
  Σ[ xsΓs∼ ∈ ∼̌ (xs ∷ Γs)]
    ((⨆ (xs ∷ Γs) xsΓs∼) ⊑ (⨆ (ys ∷ Γs) ysΓs∼))
⨆-shrink {n} {xs} {ys} {Γs} xs⊑ys ysΓs∼ =
  let xsΓs∼ : ∼̌ (xs ∷ Γs)
      xsΓs∼ = ∼̌-tail⊑ xs⊑ys ysΓs∼

      Γs∼ : ∼̌ Γs
      Γs∼ = ∼̌-tail ysΓs∼
  in
  xsΓs∼ ,
  ⊑∪-cong {xs} {ys} {⨆ Γs Γs∼} xs⊑ys
    (head≈⨆ {n = n} {Γ = xs} {Γs = Γs} xsΓs∼)
    (head≈⨆ {n = n} {Γ = ys} {Γs = Γs} ysΓs∼)

⨆⇒⊑ : {n : ℕ} →
  (Γs : Vec Is n) →
  (Γs~ : ∼̌ Γs) →
  (i : Fin n) →
  (at Γs i) ⊑ ⨆ Γs Γs~
⨆⇒⊑ {suc n} (Γ ∷ Γs) Γs~ fz = ⊑∪ {Γ} {Γ} {⨆ Γs (∼̌-tail Γs~)} (⊑-refl {Γ}) (head≈⨆ {n} {Γ} {Γs} Γs~)
⨆⇒⊑ {suc n} (Γ ∷ Γs) Γs~ (fs i) id up x rewrite ∪-sym {Γ} {⨆ Γs (∼̌-tail Γs~)} (head≈⨆ {n} {Γ} {Γs} Γs~) id =
  let IH = ⨆⇒⊑ Γs (∼̌-tail Γs~) i in
  ⊑∪ {at Γs i} {⨆ Γs (∼̌-tail Γs~)} {Γ} IH (∼-sym {Γ} {⨆ Γs (∼̌-tail Γs~)} (head≈⨆ {n} {Γ} {Γs} Γs~)) id up x

⨆⇒⊑-trans : {n : ℕ} →
  {Γs : Vec Is n} →
  {Γ : Is} →
  {Γs~ : ∼̌ Γs} →
  (⨆ Γs Γs~ ⊑ Γ) →
  (i : Fin n) →
  (at Γs i) ⊑ Γ
⨆⇒⊑-trans {n} {Γs} {Γ} {Γs~} ⨆Γs i =
  ⊑-trans {at Γs i} {⨆ Γs Γs~} {Γ} (⨆⇒⊑ Γs Γs~ i) ⨆Γs

⨆≈⇒⊑ : {n : ℕ} →
  {Γs : Vec Is n} →
  {Γ : Is} →
  (Γs~ : ∼̌ Γs) →
  (Γ ≈ ⨆ Γs Γs~) →
  (i : Fin n) →
  (at Γs i) ⊑ Γ
⨆≈⇒⊑ {suc n} {Γ₀ ∷ Γs'} {Γ} Γs~ Γ≈Γs fz =
  let IH = ∪⇒⊑ {Γ} {Γ₀} {⨆ Γs' (∼̌-tail Γs~)} {head≈⨆ Γs~} Γ≈Γs in
  proj₁ IH
⨆≈⇒⊑ {suc n} {Γ₀ ∷ Γs'} {Γ} Γs~ Γ≈Γs (fs i) =
  let IH = ∪⇒⊑ {Γ} {Γ₀} {⨆ Γs' (∼̌-tail Γs~)} {head≈⨆ Γs~} Γ≈Γs in
  ⨆⇒⊑-trans {Γs = Γs'} {Γ = Γ} {Γs~ = ∼̌-tail Γs~} (proj₂ IH) i

⨆-part∼subset : {n : ℕ} →
  (Γs : Vec Is n) →
  (Γs~ : ∼̌ Γs) →
  {Δ : Is} →
  Δ ⊑ ⨆ Γs Γs~ →
  (i : Fin n) →
  at Γs i ∼ Δ
⨆-part∼subset Γs Γs~ {Δ} Δ⊑Γs i =
  ⊑∼ {at Γs i} {⨆ Γs Γs~} {Δ}
    (⨆⇒⊑ Γs Γs~ i)
    (∼-sym {Δ} {⨆ Γs Γs~}
      (⊑⇒∼ {Δ} {⨆ Γs Γs~} Δ⊑Γs))

⨆-tail⊑ : {n : ℕ} →
  {Γ : Is} →
  {Γs : Vec Is n} →
  (Γs~ : ∼̌ (Γ ∷ Γs)) →
  {Δ : Is} →
  ⨆ (Γ ∷ Γs) Γs~ ⊑ Δ →
  ⨆ Γs (∼̌-tail Γs~) ⊑ Δ
⨆-tail⊑ {n} {Γ} {Γs} Γs~ {Δ} ΓΓs⊑Δ =
  let
    v = (∪⇒⊑ {⨆ (Γ ∷ Γs) Γs~} {Γ} {⨆ Γs (∼̌-tail Γs~)}
          {head≈⨆ Γs~} (≈-refl {⨆ (Γ ∷ Γs) Γs~}))
  in
  ⊑-trans
    {⨆ Γs (∼̌-tail Γs~)}
    {⨆ (Γ ∷ Γs) Γs~}
    {Δ} (proj₂ v) ΓΓs⊑Δ

-- disjoint between two relations
_⊥ᵢ_ : (Γ Δ : Is) → Set
Γ ⊥ᵢ Δ = (i : Id) → (lookup Γ i ≡ nothing) ⊎ (lookup Δ i ≡ nothing)

⊥ᵢ-comm : (Γ Δ : Is) → (Γ⊥Δ : Γ ⊥ᵢ Δ) → Δ ⊥ᵢ Γ
⊥ᵢ-comm Γ Δ Γ⊥Δ i with Γ⊥Δ i
... | inj₁ x = inj₂ x
... | inj₂ y = inj₁ y

empty-⊥-any : (Γ : Is) → empty ⊥ᵢ Γ
empty-⊥-any Γ i = inj₁ refl

any-⊥-empty : (Γ : Is) → Γ ⊥ᵢ empty
any-⊥-empty Γ = ⊥ᵢ-comm empty Γ (empty-⊥-any Γ)

⊥ᵢ⇒∼ : (Γ Δ : Is) → (Γ⊥Δ : Γ ⊥ᵢ Δ) → Γ ∼ Δ
⊥ᵢ⇒∼ Γ Δ Γ⊥Δ i with Γ⊥Δ i
... | inj₁ x rewrite x = nothing-∼ (lookup Δ i)
... | inj₂ y rewrite y = ∼ᵢ-sym (nothing-∼ (lookup Γ i))

∖ₗ-⊥-lookup-just : (pairs₁ pairs₂ : List 𝒟) →
  (neq₁ : Unique (map proj₁ pairs₁)) →
  (neq₂ : Unique (map proj₁ pairs₂)) →
  (i : Id) →
  (u : UpperBound) →
  (eq : lookupₗ pairs₂ i ≡ just u) →
  (lookupₗ (pairs₁ ∖ₗ pairs₂) i ≡ nothing)
∖ₗ-⊥-lookup-just [] pairs₂ neq₁ neq₂ i u eq = refl
∖ₗ-⊥-lookup-just (⟨ i' , u' ⟩ ∷ pairs₁) pairs₂ (i'∉pairs₁ ∷ neq₁) neq₂ i u eq
  with i ≟ i'
... | yes i=i' rewrite (sym i=i') | eq =
  ∖ₗ-⊥-lookup-nothing pairs₁ pairs₂ neq₁ neq₂ i (lookupₗ-fresh i pairs₁ i'∉pairs₁)
... | no  i≠i' rewrite lookupₗ-tail i' u' pairs₁ i i≠i'
  with lookupₗ pairs₂ i'
... | just _ =
  ∖ₗ-⊥-lookup-just pairs₁ pairs₂ neq₁ neq₂ i u eq
... | nothing
  rewrite lookupₗ-tail i' u' (pairs₁ ∖ₗ pairs₂) i i≠i' =
  ∖ₗ-⊥-lookup-just pairs₁ pairs₂ neq₁ neq₂ i u eq

∖-⊥-lookup : (Γ Δ : Is) →
  (i : Id) →
  (u : UpperBound) →
  (eq : lookup Δ i ≡ just u) →
  (lookup (Γ ∖ Δ) i ≡ nothing)
∖-⊥-lookup (pairs₁ has neq₁) (pairs₂ has neq₂) i u eq =
  ∖ₗ-⊥-lookup-just pairs₁ pairs₂ neq₁ neq₂ i u eq

⊥-∖ : (Γ Δ : Is) → Γ ⊥ᵢ (Δ ∖ Γ)
⊥-∖ Γ Δ i with lookup Γ i | inspect (lookup Γ) i
... | nothing | [ eq ] = inj₁ refl
... | just u  | [ eq ] = inj₂ (∖-⊥-lookup Δ Γ i u eq)

∖-⊥ : (Γ Δ : Is) → (Γ ∖ Δ) ⊥ᵢ Δ
∖-⊥ Γ Δ = ⊥ᵢ-comm Δ (Γ ∖ Δ) (⊥-∖ Δ Γ)

∖⇒⊑ : (Γ Δ : Is) → (Γ ∖ Δ) ⊑ Γ
∖⇒⊑ Γ Δ i up eq rewrite lookup-∖ Γ Δ i = proj₁ (∖ᵢ-just-inv eq)

lookup-∖-just : (Γ Δ : Is) →
  (i : Id) →
  (up : UpperBound) →
  lookup Γ i ≡ just up →
  lookup Δ i ≡ nothing →
  lookup (Γ ∖ Δ) i ≡ just up
lookup-∖-just Γ Δ i up Γi Δi
  rewrite lookup-∖ Γ Δ i | Γi | Δi = refl

lookup-∖-nothing : (Γ Δ : Is) →
  (i : Id) →
  lookup Γ i ≡ nothing →
  lookup (Γ ∖ Δ) i ≡ nothing
lookup-∖-nothing Γ Δ i Γi
  rewrite lookup-∖ Γ Δ i | Γi = refl

∖-≈-empty : (Γ Δ : Is) → Γ ≈ Δ → (Γ ∖ Δ) ≈ empty
∖-≈-empty Γ Δ Γ≈Δ i
  rewrite lookup-∖ Γ Δ i | Γ≈Δ i = ∖ᵢ-refl

∖-refl-empty : (Γ : Is) → (Γ ∖ Γ) ≈ empty
∖-refl-empty Γ = ∖-≈-empty Γ Γ (≈-refl {Γ})

∖-∪-≈-aux :
  (a b : Maybe UpperBound) →
  (c : Maybe UpperBound) →
  c ≡ a ∖ᵢ b →
  ((up : UpperBound) → b ≡ just up → a ≡ just up) →
  (p : c ∼ᵢ b) →
  a ≡ _⊔ᵢ_ c b {p}
∖-∪-≈-aux (just x) (just y) c cEq b⊑a p rewrite cEq =
  b⊑a y refl
∖-∪-≈-aux (just x) nothing c cEq b⊑a p rewrite cEq =
  sym (⊔ᵢ-nothing-right′ (just x) nothing {p} refl)
∖-∪-≈-aux nothing (just y) c cEq b⊑a p rewrite cEq =
  ⊥-elim (just≢nothing (sym (b⊑a y refl)))
∖-∪-≈-aux nothing nothing c cEq b⊑a p rewrite cEq =
  sym (⊔ᵢ-nothing-right′ nothing nothing {p} refl)

∖-∪-≈ : (Γ Δ : Is) →
  (Δ⊑Γ : Δ ⊑ Γ) →
  let Ω = Γ ∖ Δ
  in Γ ≈ ∪ Ω Δ (⊥ᵢ⇒∼ Ω Δ (∖-⊥ Γ Δ))
∖-∪-≈ Γ Δ Δ⊑Γ i
  rewrite lookup-∪ (Γ ∖ Δ) Δ (⊥ᵢ⇒∼ (Γ ∖ Δ) Δ (∖-⊥ Γ Δ)) i =
  ∖-∪-≈-aux (lookup Γ i) (lookup Δ i) (lookup (Γ ∖ Δ) i)
    (lookup-∖ Γ Δ i)
    (Δ⊑Γ i)
    (⊥ᵢ⇒∼ (Γ ∖ Δ) Δ (∖-⊥ Γ Δ) i)
