{-# OPTIONS --without-K #-}
module Einsum.EinsumProperties where

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

record SRel (xs ys zs ws : Is) : Set where
  constructor xyzw-mk
  field
    xy : xs ∼ ys
    xz : xs ∼ zs
    yz : ys ∼ zs
    xw : xs ∼ ws
    yw : ys ∼ ws
    zw : zs ∼ ws
    x-xy : xs ⊑ ∪ xs ys xy
    y-xy : ys ⊑ ∪ xs ys xy
    xzs : ∼̌ (xs ∷ zs ∷ [])
    xy-z : ∼̌ ((∪ xs ys xy) ∷ zs ∷ [])
    wyz-xz : (ws ∖ (ys ∖ zs)) ⊑ ⨆ (xs ∷ zs ∷ []) xzs

∪≈⨆-two : {xs ys : Is} →
  (xs~ys : xs ∼ ys) →
  (xys~ : ∼̌ (xs ∷ ys ∷ [])) →
  ∪ xs ys xs~ys ≈ ⨆ (xs ∷ ys ∷ []) xys~
∪≈⨆-two {xs} {ys} xs~ys xys~ =
  ∪-cong
    {Γ₁ = xs} {Γ₂ = xs}
    {Δ₁ = ys} {Δ₂ = ⨆ (ys ∷ []) (∼̌-tail xys~)}
    (≈-refl {xs})
    ys≈⨆ys
    xs~ys
    (head≈⨆ xys~)
  where
  ys≈⨆ys : ys ≈ ⨆ (ys ∷ []) (∼̌-tail xys~)
  ys≈⨆ys i =
    sym (trans
      (lookup-∪ ys empty (head≈⨆ (∼̌-tail xys~)) i)
      (⊔ᵢ-nothing-right (lookup ys i) (head≈⨆ (∼̌-tail xys~) i)))

∖-reduce-∼ :
  {xs ys zs ws : Is} →
  (xs~ys : xs ∼ ys) →
  (xs~zs : xs ∼ zs) →
  (ys~zs : ys ∼ zs) →
  (xz~ : ∼̌ (xs ∷ zs ∷ [])) →
  (xys~zs : ∪ xs ys xs~ys ∼ zs) →
  (ws~xyzs : ws ⊑ ⨆ ((∪ xs ys xs~ys) ∷ zs ∷ []) (∼̌-two xys~zs)) →
  (ws ∖ (ys ∖ zs)) ⊑ ⨆ (xs ∷ zs ∷ []) xz~
∖-reduce-∼ {xs} {ys} {zs} {ws}
  xs~ys xs~zs ys~zs xz~ xys~zs ws~xyzs i up wi
  with ∖ᵢ-just-inv
    (trans (sym (lookup-∖ ws (ys ∖ zs) i)) wi)
... | wi' , ys∖zs-i
  with lookup-∪-just (∪ xs ys xs~ys) zs xys~zs i up
    (trans
      (∪≈⨆-two {xs = ∪ xs ys xs~ys} {ys = zs}
        xys~zs (∼̌-two xys~zs) i)
      (ws~xyzs i up wi'))
... | inj₂ zi = ⨆⇒⊑ (xs ∷ zs ∷ []) xz~ (fs fz) i up zi
... | inj₁ xysi with lookup-∪-just xs ys xs~ys i up xysi
...   | inj₁ xi = ⨆⇒⊑ (xs ∷ zs ∷ []) xz~ fz i up xi
...   | inj₂ yi with ∼-just-or yi (ys~zs i)
...     | inj₁ zi = ⨆⇒⊑ (xs ∷ zs ∷ []) xz~ (fs fz) i up zi
...     | inj₂ zi =
  ⊥-elim (just≢nothing
    (trans (sym (lookup-∖-just ys zs i up yi zi)) ys∖zs-i))

∖-shrink-∼ : {xs ys zs ws : Is} →
  xs ∼ ys →
  (xs ∖ zs) ∼ (ys ∖ ws)
∖-shrink-∼ {xs} {ys} {zs} {ws} xs∼ys =
  ∼-sym {ys ∖ ws} {xs ∖ zs}
    (⊑∼ {ys ∖ ws} {ys} {xs ∖ zs}
      (∖⇒⊑ ys ws)
      (∼-sym {xs ∖ zs} {ys}
        (⊑∼ {xs ∖ zs} {xs} {ys}
           (∖⇒⊑ xs zs) xs∼ys)))

xyzw-relations : {xs ys zs ws : Is} →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (xys∼zs : ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ∼ zs) →
  (ws⊑xyzs : ws ⊑
    ⨆ ((∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) ∷ zs ∷ []) (∼̌-two xys∼zs)) →
  SRel xs ys zs ws
xyzw-relations {xs} {ys} {zs} {ws} xs⊥ys xys∼zs ws⊑xyzs =
  let xy : xs ∼ ys
      xy = ⊥ᵢ⇒∼ xs ys xs⊥ys

      xys : Is
      xys = ∪ xs ys xy

      xy⊑xys : (xs ⊑ xys) × (ys ⊑ xys)
      xy⊑xys = ∪⇒⊑ {xys} {xs} {ys} {xy} (≈-refl {xys})

      x_xy : xs ⊑ xys
      x_xy = proj₁ xy⊑xys

      y_xy : ys ⊑ xys
      y_xy = proj₂ xy⊑xys

      xz : xs ∼ zs
      xz = ⊑∼ {xs} {xys} {zs} x_xy xys∼zs

      yz : ys ∼ zs
      yz = ⊑∼ {ys} {xys} {zs} y_xy xys∼zs

      xy_z : ∼̌ (xys ∷ zs ∷ [])
      xy_z = ∼̌-two xys∼zs

      xys∼ws : xys ∼ ws
      xys∼ws =
        ⨆-part∼subset (xys ∷ zs ∷ []) xy_z {Δ = ws} ws⊑xyzs fz

      xw : xs ∼ ws
      xw = ⊑∼ {xs} {xys} {ws} x_xy xys∼ws

      yw : ys ∼ ws
      yw = ⊑∼ {ys} {xys} {ws} y_xy xys∼ws

      zw : zs ∼ ws
      zw =
        ⨆-part∼subset (xys ∷ zs ∷ []) xy_z {Δ = ws} ws⊑xyzs (fs fz)

      xzs : ∼̌ (xs ∷ zs ∷ [])
      xzs = ∼̌-two xz

      wyz_xz : (ws ∖ (ys ∖ zs)) ⊑ ⨆ (xs ∷ zs ∷ []) xzs
      wyz_xz =
        ∖-reduce-∼ {xs} {ys} {zs} {ws} xy xz yz xzs xys∼zs ws⊑xyzs
  in
  xyzw-mk xy xz yz xw yw zw x_xy y_xy xzs xy_z wyz_xz

einsum-expand-comm-eq :
  {{Γ : Context}} →
  {xs ys zs ws : Is} →
  (wt₁ : 𝕋 Γ xs) →
  (wt₂ : 𝕋 Γ zs) →
  (xyzw_rels : SRel xs ys zs ws) →
  (xys_zs : ∪ xs ys (SRel.xy xyzw_rels) ∼ zs) →
  (ws_xyzs : ws ⊑ ⨆ (∪ xs ys (SRel.xy xyzw_rels) ∷ zs ∷ []) (∼̌-two xys_zs)) →
  (env : Env Γ) →
  (idx : ℐ⦅ ws ⦆ ) →
  Set
einsum-expand-comm-eq {{Γ}} {xs} {ys} {zs} {ws}
  wt₁ wt₂ xyzw_rels xys_zs ws_xyzs env idx =
  let
    xys = ∪ xs ys (SRel.xy xyzw_rels)
    fs = ys ∖ (∪ zs ws (SRel.zw xyzw_rels))
    us = ws ∖ (ys ∖ zs)
    us⊑ws : us ⊑ ws
    us⊑ws = ∖⇒⊑ ws (ys ∖ zs)
    f : ℕ
    f = ∏ᶜ fs
  in
    ⟦ einsum {xss = xys ∷ zs ∷ []} {zs = ws}
        (cons (expand {xs} {xys} wt₁ (SRel.x-xy xyzw_rels)) (cons wt₂ nil))
        (SRel.xy-z xyzw_rels)
        ws_xyzs ⟧⦅ env ⨾ idx ⦆ ≡
    ⟦ expand {xs = us} {zs = ws}
        (f ·
         einsum
           (cons wt₁ (cons wt₂ nil))
           (SRel.xzs xyzw_rels)
           (SRel.wyz-xz xyzw_rels))
        us⊑ws ⟧⦅ env ⨾ idx ⦆

einsum-expand-comm :
  {{Γ : Context}} →
  {xs ys zs ws : Is} →
  (wt₁ : 𝕋 Γ xs) →
  (wt₂ : 𝕋 Γ zs) →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (xys∼zs : ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ∼ zs) →
  (ws⊑xyzs : ws ⊑ ⨆ ((∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) ∷ zs ∷ []) (∼̌-two xys∼zs)) →
  (env : Env Γ) →
  (idx : ℐ⦅ ws ⦆) →
  let
    xyzw_rels : SRel xs ys zs ws
    xyzw_rels = xyzw-relations xs⊥ys xys∼zs ws⊑xyzs
  in
    einsum-expand-comm-eq {{Γ}} {xs} {ys} {zs} {ws}
      wt₁ wt₂ xyzw_rels xys∼zs ws⊑xyzs env idx
einsum-expand-comm {xs = xs} {ys} {zs} {ws}
  wt₁ wt₂ xs⊥ys xys∼zs ws⊑xyzs env idx = {!!}

einsum-expand-summation-free-comm-eq :
  {{Γ : Context}} →
  {xs ys zs ws : Is} →
  (wt₁ : 𝕋 Γ xs) →
  (wt₂ : 𝕋 Γ zs) →
  (xyzw_rels : SRel xs ys zs ws) →
  (xys∼zs : ∪ xs ys (SRel.xy xyzw_rels) ∼ zs) →
  (ws≈xyzs : ws ≈
    ⨆ ((∪ xs ys (SRel.xy xyzw_rels)) ∷ zs ∷ []) (∼̌-two xys∼zs)) →
  (env : Env Γ) →
  (idx : ℐ⦅ ws ⦆) →
  Set
einsum-expand-summation-free-comm-eq {{Γ}} {xs} {ys} {zs} {ws}
  wt₁ wt₂ xyzw_rels xys∼zs ws≈xyzs env idx =
  let
    xys = ∪ xs ys (SRel.xy xyzw_rels)
    xyzs = ⨆ (xys ∷ zs ∷ []) (∼̌-two xys∼zs)
    xzs = ⨆ (xs ∷ zs ∷ []) (SRel.xzs xyzw_rels)

    ws⊑xyzs : ws ⊑ xyzs
    ws⊑xyzs = ≈⇒⊑ {Γ = ws} {Δ = xyzs} ws≈xyzs

    xzs⊑xyzs : xzs ⊑ xyzs
    xzs⊑xyzs =
      let
        xz = SRel.xz xyzw_rels
        x-xy = SRel.x-xy xyzw_rels
        xz⊑xyz = ⊑∪-cong {Γ₁ = xs} {Γ₂ = xys} {Γ₃ = zs}
          x-xy xz xys∼zs
        xzs⊑xz = ≈⇒⊑
          {Γ = xzs} {Δ = ∪ xs zs xz}
          (≈-sym {∪ xs zs xz} {xzs}
            (∪≈⨆-two {xs = xs} {ys = zs} xz (SRel.xzs xyzw_rels)))
        xyz⊑xyzs = ≈⇒⊑
          {Γ = ∪ xys zs xys∼zs} {Δ = xyzs}
          (∪≈⨆-two {xs = xys} {ys = zs} xys∼zs (∼̌-two xys∼zs))
      in
      ⊑-trans {xzs} {∪ xs zs xz} {xyzs} xzs⊑xz
        (⊑-trans {∪ xs zs xz} {∪ xys zs xys∼zs} {xyzs}
          xz⊑xyz xyz⊑xyzs)

    xzs⊑ws : xzs ⊑ ws
    xzs⊑ws = ≈⊑-right {Γ₂ = xzs} {Δ₁ = ws} {Δ₂ = xyzs}
      ws≈xyzs xzs⊑xyzs
  in
    ⟦ einsum {xss = xys ∷ zs ∷ []} {zs = ws}
        (cons (expand {xs} {xys} wt₁ (SRel.x-xy xyzw_rels)) (cons wt₂ nil))
        (∼̌-two xys∼zs)
        ws⊑xyzs ⟧⦅ env ⨾ idx ⦆ ≡
    ⟦ expand {xs = xzs} {zs = ws}
        (einsum {xss = xs ∷ zs ∷ []} {zs = xzs}
          (cons wt₁ (cons wt₂ nil))
          (SRel.xzs xyzw_rels)
          (⊑-refl {xzs}))
        xzs⊑ws ⟧⦅ env ⨾ idx ⦆

einsum-expand-summation-free-comm :
  {{Γ : Context}} →
  {xs ys zs ws : Is} →
  (wt₁ : 𝕋 Γ xs) →
  (wt₂ : 𝕋 Γ zs) →
  (xs⊥ys : xs ⊥ᵢ ys) →
  (xys∼zs : ∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys) ∼ zs) →
  (ws≈xyzs : ws ≈ ⨆ ((∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) ∷ zs ∷ []) (∼̌-two xys∼zs)) →
  (env : Env Γ) →
  (idx : ℐ⦅ ws ⦆) →
  let
    xyzs = ⨆ ((∪ xs ys (⊥ᵢ⇒∼ xs ys xs⊥ys)) ∷ zs ∷ []) (∼̌-two xys∼zs)
    xyzw_rels : SRel xs ys zs ws
    xyzw_rels = xyzw-relations xs⊥ys xys∼zs (≈⇒⊑ {ws} {xyzs} ws≈xyzs)
  in
    einsum-expand-summation-free-comm-eq {{Γ}} {xs} {ys} {zs} {ws}
      wt₁ wt₂ xyzw_rels xys∼zs ws≈xyzs env idx
einsum-expand-summation-free-comm = {!!}
