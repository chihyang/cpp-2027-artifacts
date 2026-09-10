{-# OPTIONS --without-K #-}
module Einsum.ExpandProperties where

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

∏-cong : {{Γ : Context}} →
  {n : ℕ} →
  {xss : Vec Is n} →
  {ys₁ ys₂ zs : Is} →
  (WEs : 𝕋𝕊 Γ xss) →
  (xss∼ : ∼̌ xss) →
  (xss⊑ys₁ : ⨆ xss xss∼ ⊑ ys₁) →
  (xss⊑ys₂ : ⨆ xss xss∼ ⊑ ys₂) →
  (ys₁⊑zs : ys₁ ⊑ zs) →
  (ys₂⊑zs : ys₂ ⊑ zs) →
  (env : Env Γ) →
  (idx : ℐ⦅ zs ⦆) →
  ∏ {xss = xss} {zs = ys₁} WEs xss∼ xss⊑ys₁ env (_↓ᵢ_ {ys₁} {zs} idx ys₁⊑zs) ≡
  ∏ {xss = xss} {zs = ys₂} WEs xss∼ xss⊑ys₂ env (_↓ᵢ_ {ys₂} {zs} idx ys₂⊑zs)
∏-cong {n = zero} {xss = []} {ys₁} {ys₂} {zs}
  nil xss∼ xss⊑ys₁ xss⊑ys₂ ys₁⊑zs ys₂⊑zs env idx = refl
∏-cong {suc n} {xs ∷ xss} {ys₁} {ys₂} {zs}
  (cons WE WEs) xss∼ xss⊑ys₁ xss⊑ys₂ ys₁⊑zs ys₂⊑zs env idx =
  let p = idx-cong {xs} {ys₁} {ys₂} {zs}
            (⨆⇒⊑-trans {Γs = xs ∷ xss} {Γ = ys₁} {Γs~ = xss∼} xss⊑ys₁ fz)
            (⨆⇒⊑-trans {Γs = xs ∷ xss} {Γ = ys₂} {Γs~ = xss∼} xss⊑ys₂ fz)
            ys₁⊑zs ys₂⊑zs idx
      xs∼xss = head≈⨆ {Γ = xs} {Γs = xss} xss∼
      Γ₁ = ∪ xs (⨆ xss (∼̌-tail {Γ = xs} {Γs = xss} xss∼)) xs∼xss
      Γ₃ = ⨆ xss (∼̌-tail {Γ = xs} {Γs = xss} xss∼)

      xs⊑xss = (proj₂ (∪⇒⊑ {Γ₁} {xs} {Γ₃} {xs∼xss} (≈-refl {Γ₁})))
  in
  cong₂ _*_
    {x = ⟦ WE ⟧⦅ env ⨾ _ ⦆} {y = ⟦ WE ⟧⦅ env ⨾ _ ⦆}
    (⟦⟧-cong WE env p)
    (∏-cong {ys₁ = ys₁} {ys₂ = ys₂} {zs = zs}
      WEs (∼̌-tail {Γ = xs} {Γs = xss} xss∼)
      (⊑-trans {Γ₃} {Γ₁} {ys₁} xs⊑xss xss⊑ys₁)
      (⊑-trans {Γ₃} {Γ₁} {ys₂} xs⊑xss xss⊑ys₂)
      ys₁⊑zs ys₂⊑zs env idx)

-- Expand fuses
expand-fuse :
  {{Γ : Context}} →
  {xs ys zs : Is} →
  (WT : 𝕋 Γ xs) →
  (xs⊑ys : xs ⊑ ys) →
  (ys⊑zs : ys ⊑ zs) →
  (env : Env Γ) →
  (idx : ℐ⦅ zs ⦆) →
  ⟦ expand {xs = ys} {zs = zs}
      (expand {xs = xs} {zs = ys} WT xs⊑ys) ys⊑zs ⟧⦅ env ⨾ idx ⦆
    ≡
  ⟦ expand {xs = xs} {zs = zs} WT
      (⊑-trans {xs} {ys} {zs} xs⊑ys ys⊑zs) ⟧⦅ env ⨾ idx ⦆
expand-fuse {xs = xs} {ys} {zs} WT xs⊑ys ys⊑zs env idx =
  let
    zs↓ys = _↓ᵢ_ {ys} {zs} idx ys⊑zs
    ys↓xs = (_↓ᵢ_ {xs} {ys} zs↓ys xs⊑ys)
    xs⊑zs = ⊑-trans {xs} {ys} {zs} xs⊑ys ys⊑zs
    zs↓xs = _↓ᵢ_ {xs} {zs} idx xs⊑zs
  in
  ⟦⟧-cong WT env
    (↓ᵢ-assoc {xs} {ys} {zs} idx xs⊑ys ys⊑zs)
