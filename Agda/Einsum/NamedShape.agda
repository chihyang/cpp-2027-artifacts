{-# OPTIONS --without-K #-}
module Einsum.NamedShape where

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

open Decidable⇒UIP (≡-dec _≟_)

UpperBound : Set
UpperBound = ℕ

proof-irr-Maybe :
  {a b : Maybe UpperBound} →
  (p q : a ≡ b) →
  p ≡ q
proof-irr-Maybe {a} {b} p q = ≡-irrelevant p q

Id : Set
Id = ℕ

𝒟 : Set
𝒟 = Id × UpperBound

record Is : Set where
  constructor _has_
  field
    Pairs : List 𝒟
    isNoDup : Unique (map proj₁ Pairs)

∏ₗ : (xs : List 𝒟) → ℕ
∏ₗ [] = 1
∏ₗ (⟨ _ , u ⟩ ∷ xs) = u * (∏ₗ xs)

∏ᶜ : (xs : Is) → ℕ
∏ᶜ (pairs has _) = ∏ₗ pairs

empty : Is
empty = [] has []

just-inj : {A : Set} {x1 x2 : A} → just x1 ≡ just x2 → x1 ≡ x2
just-inj refl = refl

just≢nothing : {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢nothing ()

lookupₗ : List 𝒟 → Id → Maybe UpperBound
lookupₗ [] id = nothing
lookupₗ (⟨ id' , u ⟩ ∷ rest) id with id ≟ id'
... | yes id'=id = just u
... | no id≠id = lookupₗ rest id

lookup : Is → Id → Maybe UpperBound
lookup Γ id = lookupₗ (Is.Pairs Γ) id

lookup-empty : {x : Id} → lookup empty x ≡ nothing
lookup-empty {x} = refl

fromList : (dims : List (Id × UpperBound)) → (neq : Unique (map proj₁ dims)) → Is
fromList dims neq = dims has neq

fromSingleton : Id × UpperBound → Is
fromSingleton dim = fromList (dim ∷ []) ([] ∷ [])

data _∼ᵢ_ : Maybe UpperBound → Maybe UpperBound → Set where
  ~n  : nothing ∼ᵢ nothing
  ~v  : (v : UpperBound) →
        -------------------
        just v ∼ᵢ just v
  ~nv : (v : UpperBound) →
        -------------------
        nothing ∼ᵢ just v
  ~vn : (v : UpperBound) →
        -------------------
        just v ∼ᵢ nothing

∼ᵢ-inv-≡ : {u₁ u₂ : UpperBound} →
  just u₁ ∼ᵢ just u₂ →
  u₁ ≡ u₂
∼ᵢ-inv-≡ (~v u) = refl

-- prove that ∼ᵢ is reflexive, symmetric
∼ᵢ-refl : {v : Maybe UpperBound} → v ∼ᵢ v
∼ᵢ-refl {just x} = ~v x
∼ᵢ-refl {nothing} = ~n

∼ᵢ-sym : {v₁ v₂ : Maybe UpperBound} → v₁ ∼ᵢ v₂ → v₂ ∼ᵢ v₁
∼ᵢ-sym ~n = ~n
∼ᵢ-sym (~v v) = ~v v
∼ᵢ-sym (~nv v) = ~vn v
∼ᵢ-sym (~vn v) = ~nv v

just-∼ᵢ : {v1 v2 : Maybe UpperBound} → (eq : v1 ≡ v2) → v1 ∼ᵢ v2
just-∼ᵢ {nothing} {nothing} eq = ~n
just-∼ᵢ {just x} {just x₁} eq rewrite just-inj eq = ~v x₁

nothing-∼ : (a : Maybe UpperBound) → nothing ∼ᵢ a
nothing-∼ (just x) = ~nv x
nothing-∼ nothing = ~n

∼-nothing : (a : Maybe UpperBound) → a ∼ᵢ nothing
∼-nothing a = ∼ᵢ-sym (nothing-∼ a)

∼-just-or : {u : UpperBound} →
  {v₁ v₂ : Maybe UpperBound} →
  v₁ ≡ just u →
  v₁ ∼ᵢ v₂ →
  (v₂ ≡ just u) ⊎ (v₂ ≡ nothing)
∼-just-or refl (~v u) = inj₁ refl
∼-just-or refl (~vn u) = inj₂ refl

∼-just-≡ : {u : UpperBound} →
  {v : Maybe UpperBound} →
  just u ∼ᵢ v →
  v ≢ nothing →
  v ≡ just u
∼-just-≡ (~v u) v≢nothing = refl
∼-just-≡ (~vn u) v≢nothing = ⊥-elim (v≢nothing refl)

u∼ᵢu'→= : (u u' : UpperBound) →
  (just u ∼ᵢ just u') →
  u ≡ u'
u∼ᵢu'→= u u' (~v .u) = refl

just-∼ᵢ-= : (u u' : UpperBound) →
  (mu' : Maybe UpperBound) →
  (p : just u ∼ᵢ mu') →
  (q : mu' ≡ just u') →
  mu' ≡ just u
just-∼ᵢ-= u u' (just x) p q with x ≟ u'
... | yes x=u' rewrite x=u' = cong just (u∼ᵢu'→= u' u (∼ᵢ-sym p))
... | no  x≠u' = ⊥-elim (x≠u' (just-inj q))

_⊔ᵢ_ : (v₁ v₂ : Maybe UpperBound) → {v₁~v₂ : v₁ ∼ᵢ v₂} → Maybe UpperBound
(just u ⊔ᵢ v₂) {~v .u} = just u
(just u ⊔ᵢ v₂) {~vn .u} = just u
nothing ⊔ᵢ v₂ = v₂

⊔ᵢ-just-left : {u : UpperBound} →
  {v : Maybe UpperBound} →
  (p : just u ∼ᵢ v) →
  (_⊔ᵢ_ (just u) v {p}) ≡ just u
⊔ᵢ-just-left {u} {v} (~v .u) = refl
⊔ᵢ-just-left {u} {v} (~vn .u) = refl

⊔ᵢ-refl : {v₁ : Maybe UpperBound} →
  (v₁~v₁ : v₁ ∼ᵢ v₁) →
  _⊔ᵢ_ v₁ v₁ {v₁~v₁} ≡ v₁
⊔ᵢ-refl {just x} p rewrite ⊔ᵢ-just-left p = refl
⊔ᵢ-refl {nothing} _ = refl

⊔ᵢ-refl′ : {v₁ : Maybe UpperBound} → _⊔ᵢ_ v₁ v₁ {∼ᵢ-refl} ≡ v₁
⊔ᵢ-refl′ = ⊔ᵢ-refl ∼ᵢ-refl

⊔ᵢ-irr : {v₁ v₂ : Maybe UpperBound} →
  (p q : v₁ ∼ᵢ v₂) →
  (_⊔ᵢ_ v₁ v₂ {p}) ≡ (_⊔ᵢ_ v₁ v₂ {q})
⊔ᵢ-irr {just x} {just x'} p q rewrite ⊔ᵢ-just-left p | ⊔ᵢ-just-left q = refl
⊔ᵢ-irr {just x} {nothing} (~vn .x) (~vn .x) = refl
⊔ᵢ-irr {nothing} {just x} p q = refl
⊔ᵢ-irr {nothing} {nothing} p q = refl

⊔ᵢ-cong : {v₁ v₂ w₁ w₂ : Maybe UpperBound} →
  v₁ ≡ v₂ →
  w₁ ≡ w₂ →
  (v₁∼w₁ : v₁ ∼ᵢ w₁) →
  (v₂∼w₂ : v₂ ∼ᵢ w₂) →
  _⊔ᵢ_ v₁ w₁ {v₁∼w₁} ≡ _⊔ᵢ_ v₂ w₂ {v₂∼w₂}
⊔ᵢ-cong refl refl v₁∼w₁ v₂∼w₂ = ⊔ᵢ-irr v₁∼w₁ v₂∼w₂

⊔ᵢ-comm : (v₁ v₂ : Maybe UpperBound) →
  (v₁~v₂ : v₁ ∼ᵢ v₂) →
  (v₂~v₁ : v₂ ∼ᵢ v₁) →
  (_⊔ᵢ_ v₁ v₂ {v₁~v₂} ≡ _⊔ᵢ_ v₂ v₁ {v₂~v₁})
⊔ᵢ-comm (just x) (just x₁) v₁~v₂ v₂~v₁
  rewrite ⊔ᵢ-just-left v₁~v₂ | ⊔ᵢ-just-left v₂~v₁ =
  cong just (∼ᵢ-inv-≡ v₁~v₂)
⊔ᵢ-comm (just x) nothing v₁~v₂ v₂~v₁ rewrite ⊔ᵢ-just-left v₁~v₂ = refl
⊔ᵢ-comm nothing (just x) v₁~v₂ v₂~v₁ rewrite ⊔ᵢ-just-left v₂~v₁ = refl
⊔ᵢ-comm nothing nothing v₁~v₂ v₂~v₁ = refl

⊔ᵢ-comm′ : (v₁ v₂ : Maybe UpperBound) →
  (v₁~v₂ : v₁ ∼ᵢ v₂) →
  (_⊔ᵢ_ v₁ v₂ {v₁~v₂} ≡ _⊔ᵢ_ v₂ v₁ {∼ᵢ-sym v₁~v₂})
⊔ᵢ-comm′ v₁ v₂ v₁~v₂ = ⊔ᵢ-comm v₁ v₂ v₁~v₂ (∼ᵢ-sym v₁~v₂)

⊔ᵢ-just-right : {u : UpperBound} →
  {v : Maybe UpperBound} →
  (p : v ∼ᵢ just u) →
  _⊔ᵢ_ v (just u) {p} ≡ just u
⊔ᵢ-just-right {u} {v} p
  rewrite ⊔ᵢ-comm′ v (just u) p | ⊔ᵢ-just-left (∼ᵢ-sym p) = refl

⊔ᵢ-nothing-left :
  (v₁ v₂ : Maybe UpperBound) →
  {v₁~v₂ : v₁ ∼ᵢ v₂} →
  v₁ ≡ nothing →
  _⊔ᵢ_ v₁ v₂ {v₁~v₂} ≡ v₂
⊔ᵢ-nothing-left v₁ v₂ {v₁~v₂} v₁≡nothing rewrite v₁≡nothing = refl

⊔ᵢ-nothing-right : (v₁ : Maybe UpperBound) →
  (v₁~nothing : v₁ ∼ᵢ nothing) →
  _⊔ᵢ_ v₁ nothing {v₁~nothing} ≡ v₁
⊔ᵢ-nothing-right (just x) (~vn .x) = refl
⊔ᵢ-nothing-right nothing ~n = refl

⊔ᵢ-nothing-right′ :
  (v₁ v₂ : Maybe UpperBound) →
  {v₁~v₂ : v₁ ∼ᵢ v₂} →
  v₂ ≡ nothing →
  _⊔ᵢ_ v₁ v₂ {v₁~v₂} ≡ v₁
⊔ᵢ-nothing-right′ v₁ v₂ {v₁~v₂} v₂≡nothing rewrite v₂≡nothing =
  ⊔ᵢ-nothing-right v₁ v₁~v₂

⊔ᵢ-∼ᵢ-left : (v₁ v₂ : Maybe UpperBound) →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ∼ᵢ v₁
⊔ᵢ-∼ᵢ-left v₁ v₂ ~n = ~n
⊔ᵢ-∼ᵢ-left v₁ v₂ (~v v) = ~v v
⊔ᵢ-∼ᵢ-left v₁ v₂ (~nv v) = ~vn v
⊔ᵢ-∼ᵢ-left v₁ v₂ (~vn v) = ~v v

⊔ᵢ-∼ᵢ-right : (v₁ v₂ : Maybe UpperBound) →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ∼ᵢ v₂
⊔ᵢ-∼ᵢ-right v₁ v₂ ~n = ~n
⊔ᵢ-∼ᵢ-right v₁ v₂ (~v v) = ~v v
⊔ᵢ-∼ᵢ-right v₁ v₂ (~nv v) = ~v v
⊔ᵢ-∼ᵢ-right v₁ v₂ (~vn v) = ~vn v

∼ᵢ-⊔ᵢ-left :
  {a b c : Maybe UpperBound} →
  (a≈b : a ∼ᵢ b) →
  (a≈c : a ∼ᵢ c) →
  {b≈c : b ∼ᵢ c} →
  ((a ⊔ᵢ b) {a≈b}) ∼ᵢ c
∼ᵢ-⊔ᵢ-left {a = nothing} ~n a≈c = a≈c
∼ᵢ-⊔ᵢ-left {a = nothing} (~nv v) a≈c {b≈c} = b≈c
∼ᵢ-⊔ᵢ-left (~vn v) a≈c = a≈c
∼ᵢ-⊔ᵢ-left (~v v) a≈c = a≈c

∼ᵢ-⊔ᵢ-right :
  {a b c : Maybe UpperBound} →
  (a≈b : a ∼ᵢ b) →
  (a≈c : a ∼ᵢ c) →
  {b≈c : b ∼ᵢ c} →
  a ∼ᵢ ((b ⊔ᵢ c) {b≈c})
∼ᵢ-⊔ᵢ-right {a = nothing} ~n a≈c = a≈c
∼ᵢ-⊔ᵢ-right {a = nothing} (~nv v) a≈c {~v .v} = ~nv v
∼ᵢ-⊔ᵢ-right {a = nothing} (~nv v) a≈c {~vn .v} = ~nv v
∼ᵢ-⊔ᵢ-right (~vn v) a≈c = a≈c
∼ᵢ-⊔ᵢ-right (~v v) a≈c {~v .v} = ~v v
∼ᵢ-⊔ᵢ-right (~v v) a≈c {~vn .v} = ~v v

⊔ᵢ-just-inv : {v₁ v₂ : Maybe UpperBound} →
  {u : UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ≡ just u →
  (v₁ ≡ just u) ⊎ (v₂ ≡ just u)
⊔ᵢ-just-inv ~n eq = ⊥-elim (just≢nothing (sym eq))
⊔ᵢ-just-inv (~v v) eq = inj₁ eq
⊔ᵢ-just-inv (~nv v) eq = inj₂ eq
⊔ᵢ-just-inv (~vn v) eq = inj₁ eq

⊔ᵢ-nothing-inv : {v₁ v₂ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ≡ nothing →
  (v₁ ≡ nothing) × (v₂ ≡ nothing)
⊔ᵢ-nothing-inv ~n eq = refl , refl
⊔ᵢ-nothing-inv (~v v) eq = ⊥-elim (just≢nothing eq)
⊔ᵢ-nothing-inv (~nv v) eq = ⊥-elim (just≢nothing eq)
⊔ᵢ-nothing-inv (~vn v) eq = ⊥-elim (just≢nothing eq)

nothing-⊔ᵢ-just : (a b : Maybe UpperBound) →
  (v : UpperBound) →
  (eq : a ≡ nothing) →
  (a∼b : a ∼ᵢ b) →
  (_⊔ᵢ_ a b {a∼b} ≡ just v) →
  (b ≡ just v)
nothing-⊔ᵢ-just nothing (just x) v eq a∼b a⊔ᵢb = a⊔ᵢb

just-⊔ᵢ-nothing : (a b : Maybe UpperBound) →
  (v : UpperBound) →
  (eq : b ≡ nothing) →
  (a∼b : a ∼ᵢ b) →
  (_⊔ᵢ_ a b {a∼b} ≡ just v) →
  (a ≡ just v)
just-⊔ᵢ-nothing (just x) nothing v eq (~vn .x) a⊔ᵢb = a⊔ᵢb

⊔ᵢ-assoc : {v₁ v₂ v₃ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  (v₂∼v₃ : v₂ ∼ᵢ v₃) →
  (v₁∼v₃ : v₁ ∼ᵢ v₃) →
  (v₁₂∼v₃ : _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ∼ᵢ v₃) →
  let v₁∼v₂₃ = ∼ᵢ-sym (∼ᵢ-⊔ᵢ-left v₂∼v₃ (∼ᵢ-sym v₁∼v₂) {∼ᵢ-sym v₁∼v₃})
  in
  _⊔ᵢ_ (_⊔ᵢ_ v₁ v₂ {v₁∼v₂}) v₃ {v₁₂∼v₃} ≡
  _⊔ᵢ_ v₁ (_⊔ᵢ_ v₂ v₃ {v₂∼v₃}) {v₁∼v₂₃}
⊔ᵢ-assoc {v₁ = nothing} v₁∼v₂ v₂∼v₃ v₁∼v₃ v₁₂∼v₃ =
  ⊔ᵢ-irr v₁₂∼v₃ v₂∼v₃
⊔ᵢ-assoc {v₁ = just u} v₁∼v₂ v₂∼v₃ v₁∼v₃ v₁₂∼v₃
  rewrite ⊔ᵢ-just-left v₁∼v₂ | ⊔ᵢ-just-left v₁₂∼v₃ |
  ⊔ᵢ-just-left (∼ᵢ-sym (∼ᵢ-⊔ᵢ-left v₂∼v₃ (∼ᵢ-sym v₁∼v₂) {∼ᵢ-sym v₁∼v₃})) =
  refl

⊔ᵢ-right-twice : {v₁ v₂ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  (v₁₂∼v₂ : _⊔ᵢ_ v₁ v₂ {v₁∼v₂} ∼ᵢ v₂) →
  _⊔ᵢ_ (_⊔ᵢ_ v₁ v₂ {v₁∼v₂}) v₂ {v₁₂∼v₂} ≡
  _⊔ᵢ_ v₁ v₂ {v₁∼v₂}
⊔ᵢ-right-twice {v₁ = nothing} {just x} v₁∼v₂ v₁₂∼v₂
  rewrite ⊔ᵢ-just-left v₁₂∼v₂ = refl
⊔ᵢ-right-twice {v₁ = nothing} {nothing} v₁∼v₂ v₁₂∼v₂ = refl
⊔ᵢ-right-twice {v₁ = just u} v₁∼v₂ v₁₂∼v₂
  rewrite ⊔ᵢ-just-left v₁∼v₂ | ⊔ᵢ-just-left v₁₂∼v₂ = refl

u≡→⊔ᵢ≡ : (u v w : Maybe UpperBound) →
  (p : u ∼ᵢ w) →
  (q : v ∼ᵢ w) →
  (u≡v : u ≡ v) →
  _⊔ᵢ_ u w {p} ≡ _⊔ᵢ_ v w {q}
u≡→⊔ᵢ≡ (just x) (just x₁) w p q u≡v rewrite ⊔ᵢ-just-left p | ⊔ᵢ-just-left q = u≡v
u≡→⊔ᵢ≡ nothing nothing w p q u≡v = refl

⊑⊔ᵢ-cong : {v₁ v₂ v₃ : Maybe UpperBound} →
  ((up : UpperBound) → v₁ ≡ just up → v₂ ≡ just up) →
  (v₁≈v₃ : v₁ ∼ᵢ v₃) →
  (v₂≈v₃ : v₂ ∼ᵢ v₃) →
  (up : UpperBound) →
  ((v₁ ⊔ᵢ v₃) {v₁≈v₃} ≡ just up) →
  ((v₂ ⊔ᵢ v₃) {v₂≈v₃} ≡ just up)
⊑⊔ᵢ-cong h (~v v) v₂≈v₃ up eq rewrite sym eq | h v refl =
  ⊔ᵢ-just-left v₂≈v₃
⊑⊔ᵢ-cong h (~vn v) v₂≈v₃ up eq rewrite sym eq | h v refl =
  ⊔ᵢ-just-left v₂≈v₃
⊑⊔ᵢ-cong h (~nv v) (~v .v) up eq rewrite sym eq = refl
⊑⊔ᵢ-cong h (~nv v) (~nv .v) up eq rewrite sym eq = refl
⊑⊔ᵢ-cong h ~n v₂≈v₃ up ()

_⊓ᵤ_ : (v₁ v₂ : Maybe UpperBound) → {v₁~v₂ : v₁ ∼ᵢ v₂} → Maybe UpperBound
(just u ⊓ᵤ v₂) {~v .u} = just u
(just u ⊓ᵤ v₂) {~vn .u} = nothing
nothing ⊓ᵤ v₂ = nothing

_∖ᵢ_ : Maybe UpperBound → Maybe UpperBound → Maybe UpperBound
just up ∖ᵢ nothing = just up
_       ∖ᵢ _       = nothing

∖ᵢ-refl : {a : Maybe UpperBound} → a ∖ᵢ a ≡ nothing
∖ᵢ-refl {just x} = refl
∖ᵢ-refl {nothing} = refl

∖ᵢ-nothing-left : (v : Maybe UpperBound) → nothing ∖ᵢ v ≡ nothing
∖ᵢ-nothing-left v = refl

∖ᵢ-nothing-right : (v : Maybe UpperBound) → v ∖ᵢ nothing ≡ v
∖ᵢ-nothing-right (just u) = refl
∖ᵢ-nothing-right nothing = refl

∖ᵢ-just-inv : {v₁ v₂ : Maybe UpperBound} →
  {u : UpperBound} →
  v₁ ∖ᵢ v₂ ≡ just u →
  (v₁ ≡ just u) × (v₂ ≡ nothing)
∖ᵢ-just-inv {just u} {nothing} eq = eq , refl
∖ᵢ-just-inv {just u} {just v} eq = ⊥-elim (just≢nothing (sym eq))
∖ᵢ-just-inv {nothing} {nothing} eq = ⊥-elim (just≢nothing (sym eq))
∖ᵢ-just-inv {nothing} {just v} eq = ⊥-elim (just≢nothing (sym eq))

∖ᵢ-just-right : (v : Maybe UpperBound) → (u : UpperBound) →
  v ∖ᵢ just u ≡ nothing
∖ᵢ-just-right (just v) u = refl
∖ᵢ-just-right nothing u = refl

∖ᵢ-∼ᵢ-left : {v₁ v₂ : Maybe UpperBound} → (v₁ ∖ᵢ v₂) ∼ᵢ v₁
∖ᵢ-∼ᵢ-left {just u} {nothing} = ~v u
∖ᵢ-∼ᵢ-left {just u} {just v} = ~nv u
∖ᵢ-∼ᵢ-left {nothing} {v₂} = ~n

∖ᵢ-∼ᵢ-right : {v₁ v₂ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  (v₁ ∖ᵢ v₂) ∼ᵢ v₂
∖ᵢ-∼ᵢ-right ~n = ~n
∖ᵢ-∼ᵢ-right (~v v) = ~nv v
∖ᵢ-∼ᵢ-right (~nv v) = ~nv v
∖ᵢ-∼ᵢ-right (~vn v) = ~vn v

∖ᵢ-∼ᵢ-of-∼ᵢ : {v₁ v₂ v₃ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  (v₁∼v₃ : v₁ ∼ᵢ v₃) →
  (v₂∼v₃ : v₂ ∼ᵢ v₃) →
  (v₁ ∖ᵢ v₂) ∼ᵢ v₃
∖ᵢ-∼ᵢ-of-∼ᵢ ~n v₁∼v₃ v₂∼v₃ = nothing-∼ _
∖ᵢ-∼ᵢ-of-∼ᵢ (~v v) v₁∼v₃ v₂∼v₃ = nothing-∼ _
∖ᵢ-∼ᵢ-of-∼ᵢ (~nv v) v₁∼v₃ v₂∼v₃ = nothing-∼ _
∖ᵢ-∼ᵢ-of-∼ᵢ (~vn v) v₁∼v₃ v₂∼v₃ = v₁∼v₃

∖ᵢ-⊔ᵢ-self-left : {v₁ v₂ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  v₁ ∖ᵢ (_⊔ᵢ_ v₁ v₂ {v₁∼v₂}) ≡ nothing
∖ᵢ-⊔ᵢ-self-left ~n = refl
∖ᵢ-⊔ᵢ-self-left (~v v) = refl
∖ᵢ-⊔ᵢ-self-left (~nv v) = refl
∖ᵢ-⊔ᵢ-self-left (~vn v) = refl

⊔ᵢ-∖ᵢ-right : {v₁ v₂ : Maybe UpperBound} →
  (v₁∼v₂ : v₁ ∼ᵢ v₂) →
  (_⊔ᵢ_ v₁ v₂ {v₁∼v₂}) ∖ᵢ (v₁ ∖ᵢ v₂) ≡ v₂
⊔ᵢ-∖ᵢ-right ~n = refl
⊔ᵢ-∖ᵢ-right (~v v) = refl
⊔ᵢ-∖ᵢ-right (~nv v) = refl
⊔ᵢ-∖ᵢ-right (~vn v) = refl

_∼_ : (Γ Δ : Is) → Set
Γ ∼ Δ = (i : Id) → (lookup Γ i) ∼ᵢ (lookup Δ i)

∼-refl : {Γ : Is} → Γ ∼ Γ
∼-refl {Γ} i = ∼ᵢ-refl

∼-sym : {Γ Δ : Is} → Γ ∼ Δ → Δ ∼ Γ
∼-sym {Γ} {Δ} Γ∼Δ i = ∼ᵢ-sym (Γ∼Δ i)

≡→∼ : {xs ys : Is} →
  xs ≡ ys → xs ∼ ys
≡→∼ {xs} refl = ∼-refl {xs}

empty∼ : (Γ : Is) → empty ∼ Γ
empty∼ Γ i with lookup Γ i
...           | just v = ~nv v
...           | nothing = ~n

∼empty : (Γ : Is) → Γ ∼ empty
∼empty Γ i with lookup Γ i
...           | just v = ~vn v
...           | nothing = ~n

∼̌ : {n : ℕ} → (Γs : Vec Is n) → Set
∼̌ {n} Γs = (i j : Fin n) → ((at Γs i) ∼ (at Γs j))

∼̌-empty : ∼̌ []
∼̌-empty ()

∼̌-singleton : {Γ : Is} → ∼̌ (Γ ∷ [])
∼̌-singleton {Γ} fz fz = ∼-refl {Γ}

∼̌-two : {Γ Δ : Is} →
  Γ ∼ Δ →
  ∼̌ (Γ ∷ Δ ∷ [])
∼̌-two {Γ} {Δ} Γ∼Δ fz fz = ∼-refl {Γ}
∼̌-two {Γ} {Δ} Γ∼Δ fz (fs fz) = Γ∼Δ
∼̌-two {Γ} {Δ} Γ∼Δ (fs fz) fz = ∼-sym {Γ} {Δ} Γ∼Δ
∼̌-two {Γ} {Δ} Γ∼Δ (fs fz) (fs fz) = ∼-refl {Δ}

∼̌-two-inv : {Γ Δ : Is} →
  ∼̌ (Γ ∷ Δ ∷ []) →
  Γ ∼ Δ
∼̌-two-inv ΓΔ∼ = ΓΔ∼ fz (fs fz)

∼̌-empty-any : {n : ℕ} → {Γs : Vec Is n} →
  ∼̌ Γs →
  ∼̌ (empty ∷ Γs)
∼̌-empty-any {Γs = Γs} Γs∼ fz fz = ∼-refl {empty}
∼̌-empty-any {Γs = Γs} Γs∼ fz (fs j) = empty∼ (at Γs j)
∼̌-empty-any {Γs = Γs} Γs∼ (fs i) fz = ∼empty (at Γs i)
∼̌-empty-any {Γs = Γs} Γs∼ (fs i) (fs j) = Γs∼ i j

∼̌-tail : {n : ℕ} → {Γ : Is} → {Γs : Vec Is n} →
     (~Γs : ∼̌ (Γ ∷ Γs)) → ∼̌ Γs
∼̌-tail {n} {Γ} {Γs} ~Γs = λ i j id → ~Γs (fs i) (fs j) id

∼̌↘ : {n : ℕ} → (Γ Δ : Is) → (Γs : Vec Is n) →
      (Γ∷Δ∷Γs~ : ∼̌ (Γ ∷ Δ ∷ Γs)) →
      ∼̌ (Γ ∷ Γs)
∼̌↘ Γ Δ Γs Γ∷Δ∷Γs~ fz fz = Γ∷Δ∷Γs~ fz fz
∼̌↘ Γ Δ Γs Γ∷Δ∷Γs~ fz (fs j) = Γ∷Δ∷Γs~ fz (fs (fs j))
∼̌↘ Γ Δ Γs Γ∷Δ∷Γs~ (fs i) fz = Γ∷Δ∷Γs~ (fs (fs i)) fz
∼̌↘ Γ Δ Γs Γ∷Δ∷Γs~ (fs i) (fs j) = Γ∷Δ∷Γs~ (fs (fs i)) (fs (fs j))
