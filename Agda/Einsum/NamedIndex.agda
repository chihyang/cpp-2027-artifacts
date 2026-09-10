{-# OPTIONS --without-K #-}
module Einsum.NamedIndex where

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

postulate
  funext : ∀ {A : Set} {B : A → Set} {f g : (a : A) → B a}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

  funext-imp : ∀ {A : Set} {B : A → Set} {f g : {a : A} → B a}
    → (∀ {x : A} → f {x} ≡ g {x})
      -----------------------
    → (λ {x} → f {x}) ≡ (λ {x} → g {x})

-- Index and index calculus
ℐ⦅_⦆ : Is → Set
ℐ⦅ xs ⦆ = {x : Id} → {v : UpperBound} → lookup xs x ≡ just v → Fin v

idx-proof-irr : {xs : Is} {x : Id} {v : UpperBound}
  (idx : ℐ⦅ xs ⦆) →
  (p q : lookup xs x ≡ just v) →
  idx p ≡ idx q
idx-proof-irr idx p q = cong idx (proof-irr-Maybe p q)

ℐ⦅empty⦆ : ℐ⦅ empty ⦆
ℐ⦅empty⦆ {x} {v} xv = ⊥-elim (just≢nothing (sym xv))

ℐ⦅singleton⦆ : (dim : 𝒟) → Fin (proj₂ dim) → ℐ⦅ fromSingleton dim ⦆
ℐ⦅singleton⦆ ⟨ i , u ⟩ idx {x} {v} xv with x ≟ i
... | yes x=i rewrite x=i = subst Fin (just-inj xv) idx
... | no  x≠i = ⊥-elim (just≢nothing (sym xv))

_≈ᵢ_ : {xs : Is} → ℐ⦅ xs ⦆ → ℐ⦅ xs ⦆ → Set
_≈ᵢ_ {xs} idx₁ idx₂ = ∀ {x v} (xv : lookup xs x ≡ just v) → idx₁ xv ≡ idx₂ xv

≈ᵢ→≡ : {xs : Is} → {idx₁ idx₂ : ℐ⦅ xs ⦆} → (_≈ᵢ_ {xs} idx₁ idx₂) → (_≡_ {A = ℐ⦅ xs ⦆} idx₁ idx₂)
≈ᵢ→≡ {xs} {idx₁} {idx₂} idx₁≈ᵢidx₂ =
  let f : {x : Id} → _≡_ {A = {v : UpperBound} → lookup xs x ≡ just v → Fin v} (idx₁ {x}) (idx₂ {x})
      f {x} = let g : {v : UpperBound} → _≡_ {A = lookup xs x ≡ just v → Fin v} (idx₁ {x} {v}) (idx₂ {x} {v})
                  g {v} = let h : (xv : lookup xs x ≡ just v) → _≡_ {A = Fin v} (idx₁ {x} {v} xv) (idx₂ {x} {v} xv)
                              h = idx₁≈ᵢidx₂
                      in funext h
            in funext-imp g
  in funext-imp f

ℐ-nil : (neq : Unique []) →
  (idx₁ idx₂ : ℐ⦅ fromList [] neq ⦆) →
  _≡_ {A = ℐ⦅ fromList [] neq ⦆}
    (λ {x} {v} xv → idx₁ {x} {v} xv)
    (λ {x} {v} xv → idx₂ {x} {v} xv)
ℐ-nil [] idx₁ idx₂ =
  ≈ᵢ→≡ {fromList [] []} {idx₁} {idx₂} (λ ())

_↓ᵢ_ : {xs zs : Is} → (idx : ℐ⦅ zs ⦆) → (xs⊑zs : xs ⊑ zs)  → ℐ⦅ xs ⦆
(idx ↓ᵢ xs⊑zs) {x} {v} xv = idx {x} {v} (xs⊑zs x v xv)

_→ᵢ_ : {xs zs : Is} → (idx : ℐ⦅ xs ⦆) → (xs≈zs : xs ≈ zs) → ℐ⦅ zs ⦆
(idx →ᵢ xs≈zs) {x} {v} zv = idx {x} {v} (trans (xs≈zs x) zv)

_≈ᵢ[_]_ : {xs ys : Is} →
  ℐ⦅ xs ⦆ →
  (xs≈ys : xs ≈ ys) →
  ℐ⦅ ys ⦆ →
  Set
_≈ᵢ[_]_ {xs} {ys} idx₁ xs≈ys idx₂ =
  _≈ᵢ_ {ys} (_→ᵢ_ {xs} {ys} idx₁ xs≈ys) idx₂

≈ᵢ-heter-refl : {xs : Is} →
  {idx₁ idx₂ : ℐ⦅ xs ⦆} →
  _≈ᵢ_ {xs} idx₁ idx₂ →
  _≈ᵢ[_]_ {xs} {xs} idx₁ (≈-refl {xs}) idx₂
≈ᵢ-heter-refl {xs} {idx₁} {idx₂} idx₁≈idx₂ {x} {v} xv =
  idx₁≈idx₂ {x} {v} xv

↓ᵢ-heter : {xs ys zs : Is} →
  (idx : ℐ⦅ zs ⦆) →
  (xs≈ys : xs ≈ ys) →
  (xs⊑zs : xs ⊑ zs) →
  (ys⊑zs : ys ⊑ zs) →
  _≈ᵢ[_]_ {xs} {ys}
    (_↓ᵢ_ {xs} {zs} idx xs⊑zs) xs≈ys
    (_↓ᵢ_ {ys} {zs} idx ys⊑zs)
↓ᵢ-heter {xs} {ys} {zs} idx xs≈ys xs⊑zs ys⊑zs {x} {v} yv =
  idx-proof-irr {zs} idx
    (xs⊑zs x v (trans (xs≈ys x) yv))
    (ys⊑zs x v yv)

→ᵢ-heter : {xs ys zs : Is} →
  (idx : ℐ⦅ xs ⦆) →
  (ys≈zs : ys ≈ zs) →
  (xs≈ys : xs ≈ ys) →
  (xs≈zs : xs ≈ zs) →
  _≈ᵢ[_]_ {ys} {zs}
    (_→ᵢ_ {xs} {ys} idx xs≈ys) ys≈zs
    (_→ᵢ_ {xs} {zs} idx xs≈zs)
→ᵢ-heter {xs} {ys} {zs} idx ys≈zs xs≈ys xs≈zs {x} {v} zv =
  idx-proof-irr {xs} idx
    (trans (xs≈ys x) (trans (ys≈zs x) zv))
    (trans (xs≈zs x) zv)

→ᵢ-heter-left : {xs ys zs : Is} →
  {idx₁ : ℐ⦅ xs ⦆} →
  {idx₂ : ℐ⦅ ys ⦆} →
  (xs≈ys : xs ≈ ys) →
  (_≈ᵢ[_]_ {xs} {ys} idx₁ xs≈ys idx₂) →
  (xs≈zs : xs ≈ zs) →
  (zs≈ys : zs ≈ ys) →
  _≈ᵢ[_]_ {zs} {ys}
    (_→ᵢ_ {xs} {zs} idx₁ xs≈zs) zs≈ys idx₂
→ᵢ-heter-left {xs} {ys} {zs} {idx₁} {idx₂}
  xs≈ys idx₁≈idx₂ xs≈zs zs≈ys {x} {v} yv =
  trans
    (idx-proof-irr {xs} idx₁
      (trans (xs≈zs x) (trans (zs≈ys x) yv))
      (trans (xs≈ys x) yv))
    (idx₁≈idx₂ {x} {v} yv)

→ᵢ-heter-cong : {xs ys zs : Is} →
  {idx₁ : ℐ⦅ xs ⦆} →
  {idx₂ : ℐ⦅ ys ⦆} →
  (xs≈ys : xs ≈ ys) →
  (_≈ᵢ[_]_ {xs} {ys} idx₁ xs≈ys idx₂) →
  (xs≈zs : xs ≈ zs) →
  (ys≈zs : ys ≈ zs) →
  _≈ᵢ_ {zs}
    (_→ᵢ_ {xs} {zs} idx₁ xs≈zs)
    (_→ᵢ_ {ys} {zs} idx₂ ys≈zs)
→ᵢ-heter-cong {xs} {ys} {zs} {idx₁} {idx₂}
  xs≈ys idx₁≈idx₂ xs≈zs ys≈zs {x} {v} zv =
  trans
    (idx-proof-irr {xs} idx₁
      (trans (xs≈zs x) zv)
      (trans (xs≈ys x) (trans (ys≈zs x) zv)))
    (idx₁≈idx₂ {x} {v} (trans (ys≈zs x) zv))

↓ᵢ-heter-cong : {xs ys zs : Is} →
  {idx₁ : ℐ⦅ xs ⦆} →
  {idx₂ : ℐ⦅ ys ⦆} →
  (xs≈ys : xs ≈ ys) →
  (_≈ᵢ[_]_ {xs} {ys} idx₁ xs≈ys idx₂) →
  (zs⊑xs : zs ⊑ xs) →
  (zs⊑ys : zs ⊑ ys) →
  _≈ᵢ_ {zs}
    (_↓ᵢ_ {zs} {xs} idx₁ zs⊑xs)
    (_↓ᵢ_ {zs} {ys} idx₂ zs⊑ys)
↓ᵢ-heter-cong {xs} {ys} {zs} {idx₁} {idx₂}
  xs≈ys idx₁≈idx₂ zs⊑xs zs⊑ys {x} {v} zv =
  trans
    (idx-proof-irr {xs} idx₁
      (zs⊑xs x v zv)
      (trans (xs≈ys x) (zs⊑ys x v zv)))
    (idx₁≈idx₂ {x} {v} (zs⊑ys x v zv))

≈⇒ℐ↔ℐ : {xs ys : Is} → xs ≈ ys → ℐ⦅ xs ⦆ ↔ ℐ⦅ ys ⦆
≈⇒ℐ↔ℐ {xs} {ys} xs≈ys =
  mk↔ₛ′ to-index from-index right-inverse left-inverse
  where
  to-index : ℐ⦅ xs ⦆ → ℐ⦅ ys ⦆
  to-index idx = _→ᵢ_ {xs} {ys} idx xs≈ys

  from-index : ℐ⦅ ys ⦆ → ℐ⦅ xs ⦆
  from-index idx = _→ᵢ_ {ys} {xs} idx (≈-sym {xs} {ys} xs≈ys)

  left-pointwise : (idx : ℐ⦅ xs ⦆) →
    _≈ᵢ_ {xs} (from-index (to-index idx)) idx
  left-pointwise idx {x} {v} xv =
    idx-proof-irr {xs} idx
      (trans (xs≈ys x) (trans (sym (xs≈ys x)) xv)) xv

  left-inverse : (idx : ℐ⦅ xs ⦆) →
    _≡_ {A = ℐ⦅ xs ⦆} (from-index (to-index idx)) idx
  left-inverse idx =
    ≈ᵢ→≡ {xs} {from-index (to-index idx)} {idx}
      (left-pointwise idx)

  right-pointwise : (idx : ℐ⦅ ys ⦆) →
    _≈ᵢ_ {ys} (to-index (from-index idx)) idx
  right-pointwise idx {x} {v} xv =
    idx-proof-irr {ys} idx
      (trans (sym (xs≈ys x)) (trans (xs≈ys x) xv)) xv

  right-inverse : (idx : ℐ⦅ ys ⦆) →
    _≡_ {A = ℐ⦅ ys ⦆} (to-index (from-index idx)) idx
  right-inverse idx =
    ≈ᵢ→≡ {ys} {to-index (from-index idx)} {idx}
      (right-pointwise idx)

ℐ-∪-aux : (a b : Maybe UpperBound) →
  (v : UpperBound) →
  (a⊥b : (a ≡ nothing) ⊎ (b ≡ nothing)) →
  (a∼b : a ∼ᵢ b) →
  (_⊔ᵢ_ a b {a∼b} ≡ just v) →
  (a ≡ just v → Fin v) →
  (b ≡ just v → Fin v) →
  Fin v
ℐ-∪-aux a b v (inj₁ a≡nothing) a∼b a⊔b idx₁ idx₂ =
  idx₂ (nothing-⊔ᵢ-just a b v a≡nothing a∼b a⊔b)
ℐ-∪-aux a b v (inj₂ b≡nothing) a∼b a⊔b idx₁ idx₂ =
  idx₁ (just-⊔ᵢ-nothing a b v b≡nothing a∼b a⊔b)

ℐ-∪ : (xs ys : Is) →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (idx₁ : ℐ⦅ xs ⦆) →
  (idx₂ : ℐ⦅ ys ⦆) →
  let xs≈ys = ⊥ᵢ⇒∼ xs ys xs⊥ys in
  ℐ⦅ ∪ xs ys xs≈ys ⦆
ℐ-∪ xs ys xs⊥ys idx₁ idx₂ {x} {v} xv rewrite lookup-∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) x =
  ℐ-∪-aux (lookup xs x) (lookup ys x) v (xs⊥ys x)
    (⊥ᵢ⇒∼ xs ys xs⊥ys x) xv
    (idx₁ {x} {v}) (idx₂ {x} {v})

ℐ-∪′ : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  ℐ⦅ xs ⦆ × ℐ⦅ ys ⦆ →
  ℐ⦅ ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ⦆
ℐ-∪′ {xs} {ys} xs⊥ys idx =
  ℐ-∪ xs ys xs⊥ys (proj₁ idx) (proj₂ idx)

ℐ-split : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  ℐ⦅ ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ⦆ →
  ℐ⦅ xs ⦆ × ℐ⦅ ys ⦆
ℐ-split {xs} {ys} xs⊥ys idx =
  let
    xs∪ys = ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)
    xs⊑xs∪ys , ys⊑xs∪ys =
      ∪⇒⊑ {xs∪ys} {xs} {ys} {⊥ᵢ⇒∼ xs ys xs⊥ys} (≈-refl {xs∪ys})
  in
  _↓ᵢ_ {xs} {xs∪ys} idx xs⊑xs∪ys ,
  _↓ᵢ_ {ys} {xs∪ys} idx ys⊑xs∪ys

ℐ-∪-left : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (idx₁ : ℐ⦅ xs ⦆) →
  (idx₂ : ℐ⦅ ys ⦆) →
  {x : Id} →
  {v : UpperBound} →
  (xv : lookup xs x ≡ just v) →
  (xv∪ : lookup (∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) x ≡ just v) →
  ℐ-∪ xs ys xs⊥ys idx₁ idx₂ xv∪ ≡ idx₁ xv
ℐ-∪-left {xs} {ys} xs⊥ys idx₁ idx₂ {x} {v} xv xv∪
  rewrite lookup-∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) x
  with xs⊥ys x
... | inj₁ xs≡nothing = ⊥-elim (just≢nothing (trans (sym xv) xs≡nothing))
... | inj₂ ys≡nothing =
  idx-proof-irr {xs} idx₁ _ xv

ℐ-∪-right : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (idx₁ : ℐ⦅ xs ⦆) →
  (idx₂ : ℐ⦅ ys ⦆) →
  {x : Id} →
  {v : UpperBound} →
  (yv : lookup ys x ≡ just v) →
  (xv∪ : lookup (∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) x ≡ just v) →
  ℐ-∪ xs ys xs⊥ys idx₁ idx₂ xv∪ ≡ idx₂ yv
ℐ-∪-right {xs} {ys} xs⊥ys idx₁ idx₂ {x} {v} yv xv∪
  rewrite lookup-∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) x
  with xs⊥ys x
... | inj₁ xs≡nothing =
  idx-proof-irr {ys} idx₂ _ yv
... | inj₂ ys≡nothing = ⊥-elim (just≢nothing (trans (sym yv) ys≡nothing))

ℐ-split-∪ : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (idx : ℐ⦅ xs ⦆ × ℐ⦅ ys ⦆) →
  ℐ-split {xs} {ys} xs⊥ys (ℐ-∪′ {xs} {ys} xs⊥ys idx) ≡ idx
ℐ-split-∪ {xs} {ys} xs⊥ys ⟨ idx₁ , idx₂ ⟩ =
  let
    idx∪ = ℐ-∪ xs ys xs⊥ys idx₁ idx₂
    idxs = ℐ-split {xs} {ys} xs⊥ys idx∪

    left : _≈ᵢ_ {xs} (proj₁ idxs) idx₁
    left {x} {v} xv =
      ℐ-∪-left {xs} {ys} xs⊥ys idx₁ idx₂ xv _

    right : _≈ᵢ_ {ys} (proj₂ idxs) idx₂
    right {x} {v} yv =
      ℐ-∪-right {xs} {ys} xs⊥ys idx₁ idx₂ yv _
  in
  cong₂ ⟨_,_⟩
    (≈ᵢ→≡ {xs} {proj₁ idxs} {idx₁} left)
    (≈ᵢ→≡ {ys} {proj₂ idxs} {idx₂} right)

ℐ-∪-split : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (idx : ℐ⦅ ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ⦆) →
  _≡_ {A = ℐ⦅ ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ⦆}
    (ℐ-∪′ {xs} {ys} xs⊥ys (ℐ-split {xs} {ys} xs⊥ys idx)) idx
ℐ-∪-split {xs} {ys} xs⊥ys idx =
  ≈ᵢ→≡ {xs∪ys} {ℐ-∪′ {xs} {ys} xs⊥ys idxs} {idx} pointwise
  where
  xs∪ys : Is
  xs∪ys = ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)

  idxs : ℐ⦅ xs ⦆ × ℐ⦅ ys ⦆
  idxs = ℐ-split {xs} {ys} xs⊥ys idx

  pointwise : _≈ᵢ_ {xs∪ys} (ℐ-∪′ {xs} {ys} xs⊥ys idxs) idx
  pointwise {x} {v} xv
    with lookup-∪-just xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) x v xv
  ... | inj₁ xvx =
    trans
      (ℐ-∪-left {xs} {ys} xs⊥ys (proj₁ idxs) (proj₂ idxs) xvx xv)
      (idx-proof-irr {xs∪ys} idx _ xv)
  ... | inj₂ xvy =
    trans
      (ℐ-∪-right {xs} {ys} xs⊥ys (proj₁ idxs) (proj₂ idxs) xvy xv)
      (idx-proof-irr {xs∪ys} idx _ xv)

ℐ-∪↔× : {xs ys : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  ℐ⦅ ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ⦆ ↔ (ℐ⦅ xs ⦆ × ℐ⦅ ys ⦆)
ℐ-∪↔× {xs} {ys} xs⊥ys =
  mk↔ₛ′
    (ℐ-split {xs} {ys} xs⊥ys)
    (ℐ-∪′ {xs} {ys} xs⊥ys)
    (ℐ-split-∪ {xs} {ys} xs⊥ys)
    (ℐ-∪-split {xs} {ys} xs⊥ys)

ℐ-∪-heter : {xs ys zs ws : Is} →
  {idx₁ : ℐ⦅ xs ⦆} →
  {idx₂ : ℐ⦅ ys ⦆} →
  {idx₃ : ℐ⦅ zs ⦆} →
  {idx₄ : ℐ⦅ ws ⦆} →
  (xs≈ys : xs ≈ ys) →
  (zs≈ws : zs ≈ ws) →
  (_≈ᵢ[_]_ {xs} {ys} idx₁ xs≈ys idx₂) →
  (_≈ᵢ[_]_ {zs} {ws} idx₃ zs≈ws idx₄) →
  (xs⊥zs : xs ⊥ᵢ zs) →
  (ys⊥ws : ys ⊥ᵢ ws) →
  _≈ᵢ[_]_
    {∪ xs zs (⊥ᵢ⇒∼ xs zs xs⊥zs)}
    {∪ ys ws (⊥ᵢ⇒∼ ys ws ys⊥ws)}
    (ℐ-∪ xs zs xs⊥zs idx₁ idx₃)
    (∪-cong {Γ₁ = xs} {Γ₂ = ys} {Δ₁ = zs} {Δ₂ = ws}
      xs≈ys zs≈ws
      (⊥ᵢ⇒∼ xs zs xs⊥zs) (⊥ᵢ⇒∼ ys ws ys⊥ws))
    (ℐ-∪ ys ws ys⊥ws idx₂ idx₄)
ℐ-∪-heter {xs} {ys} {zs} {ws} {idx₁} {idx₂} {idx₃} {idx₄}
  xs≈ys zs≈ws idx₁≈idx₂ idx₃≈idx₄ xs⊥zs ys⊥ws {x} {v} xvw
  with lookup-∪-just ys ws (⊥ᵢ⇒∼ ys ws ys⊥ws) x v xvw
... | inj₁ yv =
  trans
    (ℐ-∪-left {xs} {zs} xs⊥zs idx₁ idx₃ {x} {v}
      (trans (xs≈ys x) yv)
      (trans
        (∪-cong {Γ₁ = xs} {Γ₂ = ys} {Δ₁ = zs} {Δ₂ = ws} xs≈ys zs≈ws
          (⊥ᵢ⇒∼ xs zs xs⊥zs) (⊥ᵢ⇒∼ ys ws ys⊥ws) x)
        xvw))
    (trans
      (idx₁≈idx₂ {x} {v} yv)
      (sym (ℐ-∪-left {ys} {ws} ys⊥ws idx₂ idx₄ {x} {v} yv xvw)))
... | inj₂ wv =
  trans
    (ℐ-∪-right {xs} {zs} xs⊥zs idx₁ idx₃ {x} {v}
      (trans (zs≈ws x) wv)
      (trans
        (∪-cong {Γ₁ = xs} {Γ₂ = ys} {Δ₁ = zs} {Δ₂ = ws} xs≈ys zs≈ws
          (⊥ᵢ⇒∼ xs zs xs⊥zs) (⊥ᵢ⇒∼ ys ws ys⊥ws) x)
        xvw))
    (trans
      (idx₃≈idx₄ {x} {v} wv)
      (sym (ℐ-∪-right {ys} {ws} ys⊥ws idx₂ idx₄ {x} {v} wv xvw)))

_≈→ᵢ_ : {xs zs : Is} → {idx₁ idx₂ : ℐ⦅ xs ⦆} →
  (idx₁≈ᵢidx₂ : _≈ᵢ_ {xs} idx₁ idx₂) → (xs≈zs : xs ≈ zs) →
  (_≈ᵢ_ {zs} (_→ᵢ_ {xs} {zs} idx₁ xs≈zs) (_→ᵢ_ {xs} {zs} idx₂ xs≈zs))
_≈→ᵢ_ {xs} {idx₁} {idx₂} idx₁≈ᵢidx₂ xs≈zs {x} {v} xv = idx₁≈ᵢidx₂ (trans (xs≈zs x) xv)

↓ᵢ-cong : {xs zs : Is} {idx₁ idx₂ : ℐ⦅ zs ⦆} →
  _≈ᵢ_ {zs} idx₁ idx₂ → (xs⊑zs : xs ⊑ zs) →
  _≈ᵢ_ {xs} (_↓ᵢ_ {xs} {zs} idx₁ xs⊑zs)
    (_↓ᵢ_ {xs} {zs} idx₂ xs⊑zs)
↓ᵢ-cong {idx₁ = idx₁} {idx₂ = idx₂} idx₁≈idx₂ xs⊑zs {x} {v} xv =
  idx₁≈idx₂ {x} {v} (xs⊑zs x v xv)

→ᵢ↓ᵢ : {xs ys zs : Is} →
  (idx : ℐ⦅ ys ⦆) →
  (ys≈zs : ys ≈ zs) →
  (xs⊑ys : xs ⊑ ys) →
  (xs⊑zs : xs ⊑ zs) →
  _≈ᵢ_ {xs}
    (_↓ᵢ_ {xs} {zs} (_→ᵢ_ {ys} {zs} idx ys≈zs) xs⊑zs)
    (_↓ᵢ_ {xs} {ys} idx xs⊑ys)
→ᵢ↓ᵢ {xs} {ys} {zs} idx ys≈zs xs⊑ys xs⊑zs {x} {v} xv =
  idx-proof-irr {ys} idx
    (trans (ys≈zs x) (xs⊑zs x v xv))
    (xs⊑ys x v xv)

→ᵢ-cong : {xs zs : Is} {idx₁ idx₂ : ℐ⦅ xs ⦆} → _≈ᵢ_ {xs} idx₁ idx₂ → (xs≈zs : xs ≈ zs) →
          _≈ᵢ_ {zs} (_→ᵢ_ {xs} {zs} idx₁ xs≈zs) (_→ᵢ_ {xs} {zs} idx₂ xs≈zs)
→ᵢ-cong {idx₁ = idx₁} {idx₂ = idx₂} idx₁≈idx₂ xs≈zs {x} {v} zv =
  idx₁≈idx₂ {x} {v} (trans (xs≈zs x) zv)

↓ᵢ-assoc : {xs ys zs : Is} → (idx : ℐ⦅ zs ⦆) → (xs⊑ys : xs ⊑ ys) → (ys⊑zs : ys ⊑ zs) →
           _≈ᵢ_ {xs = xs}
             (_↓ᵢ_ {xs} {ys} (_↓ᵢ_ {ys} {zs} idx ys⊑zs) xs⊑ys)
             (_↓ᵢ_ {xs} {zs} idx (⊑-trans {xs} {ys} {zs} xs⊑ys ys⊑zs))
↓ᵢ-assoc idx xs⊑ys ys⊑zs {x} {v} xv = refl

idx-comm : {xs ys : Is} →
  (xs⊑ys₁ xs⊑ys₂ : xs ⊑ ys) →
  (idx : ℐ⦅ ys ⦆) →
  _≈ᵢ_ {xs = xs} (_↓ᵢ_ {xs} {ys} idx xs⊑ys₁) (_↓ᵢ_ {xs} {ys} idx xs⊑ys₂)
idx-comm {ys = ys} xs⊑ys₁ xs⊑ys₂ idx {x} {v} xv = idx-proof-irr {ys} idx (xs⊑ys₁ x v xv) (xs⊑ys₂ x v xv)

ℐ-cons : {x : Id} →
  {d : UpperBound} →
  {xs : List 𝒟} →
  {x∉xs : All (x ≢_) (map proj₁ xs)} →
  {neq : Unique (map proj₁ xs)} →
  Fin d →
  ℐ⦅ fromList xs neq ⦆ →
  ℐ⦅ fromList (⟨ x , d ⟩ ∷ xs) (x∉xs ∷ neq) ⦆
ℐ-cons {x} {d} {xs} {x∉xs} {neq} i idx {y} {v} yv with y ≟ x
... | yes y=x rewrite y=x = subst Fin (just-inj yv) i
... | no  y≠x = idx yv

ℐ-head : {x : Id} →
  {d : UpperBound} →
  {xs : List 𝒟} →
  {x∉xs : All (x ≢_) (map proj₁ xs)} →
  {neq : Unique (map proj₁ xs)} →
  ℐ⦅ fromList (⟨ x , d ⟩ ∷ xs) (x∉xs ∷ neq) ⦆ →
  Fin d
ℐ-head {x} {d} {xs} idx = idx {x} {d} (lookupₗ-head=just x d xs)

ℐ-tail : {x : Id} →
  {d : UpperBound} →
  {xs : List 𝒟} →
  {x∉xs : All (x ≢_) (map proj₁ xs)} →
  {neq : Unique (map proj₁ xs)} →
  ℐ⦅ fromList (⟨ x , d ⟩ ∷ xs) (x∉xs ∷ neq) ⦆ →
  ℐ⦅ fromList xs neq ⦆
ℐ-tail {x} {d} {xs} {x∉xs} {neq} idx {y} {v} yv =
  idx {y} {v}
    (trans
      (lookupₗ-tail x d xs y
        (lookupₗ-tail-inv x v xs neq x∉xs y v yv))
      yv)

ℐ-empty-∪ : {ys : Is} →
  (idx : ℐ⦅ ys ⦆) →
  _≈ᵢ_ {xs = ∪ empty ys (⊥ᵢ⇒∼ empty ys (empty-⊥-any ys))}
    (ℐ-∪ empty ys (empty-⊥-any ys) (λ {x} {v} xv → ℐ⦅empty⦆ {x} {v} xv) idx)
    (_→ᵢ_ {ys} {∪ empty ys (⊥ᵢ⇒∼ empty ys (empty-⊥-any ys))} idx (λ i → refl))
ℐ-empty-∪ {ys} idx {x} {v} xv =
  idx-proof-irr {ys} {x} {v} idx
    (nothing-⊔ᵢ-just nothing (lookup ys x) v refl
      (⊥ᵢ⇒∼ empty ys (empty-⊥-any ys) x) xv)
    (trans refl xv)

idx-cong : {xs ys₁ ys₂ zs : Is} →
  (xs⊑ys₁ : xs ⊑ ys₁) →
  (xs⊑ys₂ : xs ⊑ ys₂) →
  (ys₁⊑zs : ys₁ ⊑ zs) →
  (ys₂⊑zs : ys₂ ⊑ zs) →
  (idx : ℐ⦅ zs ⦆) →
  _≈ᵢ_ {xs = xs}
    (_↓ᵢ_ {xs} {ys₁} (_↓ᵢ_ {ys₁} {zs} idx ys₁⊑zs) xs⊑ys₁)
    (_↓ᵢ_ {xs} {ys₂} (_↓ᵢ_ {ys₂} {zs} idx ys₂⊑zs) xs⊑ys₂)
idx-cong {xs} {ys₁} {ys₂} {zs} xs⊑ys₁ xs⊑ys₂ ys₁⊑zs ys₂⊑zs idx =
  (idx-comm {xs} {zs}
    (⊑-trans {xs} {ys₁} {zs} xs⊑ys₁ ys₁⊑zs)
    (⊑-trans {xs} {ys₂} {zs} xs⊑ys₂ ys₂⊑zs) idx)
