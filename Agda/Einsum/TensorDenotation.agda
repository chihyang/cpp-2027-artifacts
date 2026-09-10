{-# OPTIONS --without-K #-}
module Einsum.TensorDenotation where

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

-- Denotational semantics
∑ₗ :
  (ih : List 𝒟) →
  (neqₕ : Unique (map proj₁ ih)) →
  (f : ℐ⦅ ih has neqₕ ⦆ → ℕ) →
  ℕ
∑ₗ [] [] f = f (λ {i} {u} iu → ℐ⦅empty⦆ {i} {u} iu)
∑ₗ (⟨ i , u ⟩ ∷ ih) (i∉ih ∷ neqₕ) f =
  foldl f' 0 (allFin u) where
    f' : ℕ → Fin u → ℕ
    f' acc idx = acc ℕ+ ∑ₗ ih neqₕ
      (λ idx' → f (λ {x} {v} xv →
        ℐ-cons {x = i} {d = u} {xs = ih}
          {x∉xs = i∉ih} {neq = neqₕ} idx idx' {x} {v} xv))

∑ : (i⋯ : Is) →
    (f : ℐ⦅ i⋯ ⦆ → ℕ) →
    ℕ
∑ (pairs has neq) f = ∑ₗ pairs neq f

∏ : {{Γ : Context}} →
    {n : ℕ} →
    {xss : Vec Is n} →
    {zs : Is} →
    (WEs : 𝕋𝕊 Γ xss) →
    (xss∼ : ∼̌ xss) →
    -- NOTE: here we use ⊑ rather than ≈ for the purpose of recursion. In
    -- fact, in an einsum, ⨆ xss∼ ≈ ds ∪ zs.
    (⨆ xss xss∼ ⊑ zs) →
    (E : Env Γ) →
    (idx : ℐ⦅ zs ⦆) →
    ℕ

einsum-iterator :
  {{Γ : Context}} →
  {n : ℕ} →
  {xss : Vec Is n} →
  {zs : Is} →
  (WEs : 𝕋𝕊 Γ xss) →
  (xss∼ : ∼̌ xss) →
  (zs⊑xss : zs ⊑ ⨆ xss xss∼) →
  (env : Env Γ) →
  (idx : ℐ⦅ zs ⦆) →
  (idx' : ℐ⦅ ⨆ xss xss∼ ∖ zs ⦆) →
  ℕ
einsum-iterator {xss = xss} {zs = zs} WEs xss∼ zs⊑xss env idx idx' =
  let ⊔xss : Is
      ⊔xss = ⨆ xss xss∼

      i⋯ : Is
      i⋯ = ⊔xss ∖ zs

      ds⊥zs : i⋯ ⊥ᵢ zs
      ds⊥zs = ∖-⊥ ⊔xss zs

      ds∼zs : i⋯ ∼ zs
      ds∼zs = ⊥ᵢ⇒∼ i⋯ zs ds⊥zs

      ds∪zs : Is
      ds∪zs = ∪ i⋯ zs ds∼zs

      ℐ⦅ds∪zs⦆ : ℐ⦅ i⋯ ⦆ → ℐ⦅ ds∪zs ⦆
      ℐ⦅ds∪zs⦆ idx' = ℐ-∪ i⋯ zs ds⊥zs idx' idx

      ds∪zs≈xss : ds∪zs ≈ ⊔xss
      ds∪zs≈xss = ≈-sym {⊔xss} {ds∪zs} (∖-∪-≈ ⊔xss zs zs⊑xss)
  in
  ∏ {xss = xss} {zs = ⊔xss} WEs xss∼
    (⊑-refl {⊔xss}) env (_→ᵢ_ {xs = ds∪zs} {zs = ⊔xss} (ℐ⦅ds∪zs⦆ idx') ds∪zs≈xss)

⟦_⟧⦅_⨾_⦆ : {{Γ : Context}} → {xs : Is} →
  (WT : 𝕋 Γ xs) → (E : Env Γ) → (idx : ℐ⦅ xs ⦆) → ℕ
⟦ scalar v ⟧⦅ env ⨾ idx ⦆ = v
⟦ zero xs ⟧⦅ env ⨾ idx ⦆ = 0
⟦ expand {xs = xs} {zs = zs} we xs⊑zs ⟧⦅ env ⨾ idx ⦆ =
  ⟦ we ⟧⦅ env ⨾ _↓ᵢ_ {xs} {zs} idx xs⊑zs ⦆
⟦ einsum {xss = xss} {zs = zs} WEs xss∼ zs⊑xss ⟧⦅ env ⨾ idx ⦆ =
  ∑ (⨆ xss xss∼ ∖ zs) (einsum-iterator {xss = xss} {zs = zs} WEs xss∼ zs⊑xss env idx)
⟦ plus {xs = xs} {ys = ys} wt₁ wt₂ xs₁≈xs₂ ⟧⦅ env ⨾ idx ⦆ =
  ⟦ wt₁ ⟧⦅ env ⨾ idx ⦆ ℕ+ ⟦ wt₂ ⟧⦅ env ⨾ _→ᵢ_ {xs} {ys} idx xs₁≈xs₂ ⦆
⟦ s · wt ⟧⦅ env ⨾ idx ⦆ = s * ⟦ wt ⟧⦅ env ⨾ idx ⦆
⟦ const xs f ⟧⦅ env ⨾ idx ⦆ = f idx
⟦ var dims neq v ⟧⦅ env ⨾ idx ⦆ = lookupᵘ v env (castⁿ dims neq idx)
⟦ bind dims neq we₁ we₂ ⟧⦅ env ⨾ idx ⦆ =
  let t = ⟦_⟧⦅_⨾_⦆ we₁ env in
  ⟦_⟧⦅_⨾_⦆ {{_}} we₂ ⟨ env , (λ idx' → t (castᵘ dims neq idx')) ⟩ idx

∏ {zero} {xss = []} {zs} nil xss∼ xss⊑zs env idx = 1
∏ {suc n} {xs ∷ xss} {zs} (cons WE WEs) xss∼ xss⊑zs env idx =
  let Γ₁ = ∪ xs (⨆ xss (∼̌-tail {Γ = xs} {Γs = xss} xss∼)) (head≈⨆ {Γ = xs} {Γs = xss} xss∼)
      Γ₂ = xs
      Γ₃ = ⨆ xss (∼̌-tail {Γ = xs} {Γs = xss} xss∼)

      xs⊑zs : xs ⊑ zs
      xs⊑zs = ⨆⇒⊑-trans {Γs = xs ∷ xss} {Γ = zs} {Γs~ = xss∼} xss⊑zs fz

      xs⊑xss : ⨆ xss (∼̌-tail {Γ = xs} {Γs = xss} xss∼) ⊑
                  ∪ xs Γ₃ (head≈⨆ {Γ = xs} {Γs = xss} xss∼)
      xs⊑xss = proj₂
        (∪⇒⊑ {Γ₁} {Γ₂} {Γ₃} {Γ₂≈Γ₃ = head≈⨆ {Γ = xs} {Γs = xss} xss∼} (≈-refl {Γ₁}))
  in
  ⟦ WE ⟧⦅ env ⨾ _↓ᵢ_ {Γ₂} {zs} idx xs⊑zs ⦆ *
  (∏ {xss = xss} {zs = zs} WEs (∼̌-tail {Γ = xs} {Γs = xss} xss∼)
    (⊑-trans {Γ₃} {∪ xs Γ₃ (head≈⨆ {Γ = xs} {Γs = xss} xss∼)} {zs} xs⊑xss xss⊑zs) env idx)

⟦⟧-cong : {{Γ : Context}} →
          {xs : Is} →
          (wt : 𝕋 Γ xs) → (env : Env Γ) → {idx₁ idx₂ : ℐ⦅ xs ⦆} →
          _≈ᵢ_ {xs = xs} idx₁ idx₂ → (⟦ wt ⟧⦅ env ⨾ idx₁ ⦆) ≡ (⟦ wt ⟧⦅ env ⨾ idx₂ ⦆)
⟦⟧-cong {xs = xs} wt env {idx₁} {idx₂} idx₁≈idx₂
  rewrite (≈ᵢ→≡ {xs} {idx₁} {idx₂} idx₁≈idx₂) = refl
