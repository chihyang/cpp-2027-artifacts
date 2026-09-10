import Mathlib.Data.List.Nodup
import Einsum.NamedShape
import Einsum.ShapeOperations

namespace ShapeProperties
open NamedShape
open ShapeOperations

abbrev Unique := NamedShape.Unique

def IsSubset (xs ys : Is) : Prop :=
  ∀ i , ∀ up , lookup xs i = some up → lookup ys i = some up

infix:60 " ⊑ " => IsSubset

theorem IsSubset_refl {xs : Is} : xs ⊑ xs := by
  intro i up h
  exact h

theorem IsSubset_trans {xs ys zs : Is}
  (xs_ys : xs ⊑ ys) (ys_zs : ys ⊑ zs) :
  xs ⊑ zs := by
  intro i up h
  exact ys_zs i up (xs_ys i up h)

def IsEq (xs ys : Is) : Prop :=
  ∀ i , lookup xs i = lookup ys i

def IsRelEquiv : Equivalence IsEq := {
  refl := by
    intro xs i
    rfl
  symm := by
    intro xs ys h i
    exact Eq.symm (h i)
  trans := by
    intro x y z h1 h2 i
    exact Eq.trans (h1 i) (h2 i)
}

instance : Setoid Is where
  r := IsEq
  iseqv := IsRelEquiv

instance : Symmetric IsEq := fun _ _ h => IsRelEquiv.symm h

instance : Transitive IsEq := fun _ _ _ h1 h2 => IsRelEquiv.trans h1 h2

lemma IsEq_empty_eq {xs : Is} (xs_empty : xs ≈ empty) :
  xs = empty := by
  rcases xs with ⟨pairs, noDup⟩
  cases pairs with
  | nil => rfl
  | cons dim pairs =>
    have h := xs_empty dim.1
    rw [lookup_mk] at h
    rw [lookupPairs_head] at h
    unfold lookup empty at h
    simp only [lookupPairs_empty_none] at h
    contradiction

lemma empty_prod_one {xs : Is} (xs_empty : xs ≈ empty) :
  xs.prod = 1 := by
  simp only [IsEq_empty_eq xs_empty]
  rfl

@[congr]
theorem lookup_congr {xs ys : Is} (h : xs ≈ ys) (i : Id) :
  lookup xs i = lookup ys i := h i

lemma IsEq_subset {xs ys : Is} (xs_ys : xs ≈ ys) :
  xs ⊑ ys := by
  intro i up h
  simpa [← lookup_congr xs_ys i] using h

lemma IsEq_subset_right {xs ys zs : Is} (ys_zs : ys ≈ zs)
  (xs_ys : xs ⊑ zs) :
  xs ⊑ ys := by
  intro i up h
  simpa [ys_zs i] using xs_ys i up h

lemma IsEq_subset_left {xs ys zs : Is} (ys_zs : ys ≈ zs)
  (xs_ys : xs ⊑ ys) :
  xs ⊑ zs := by
  intro i up h
  simpa [← ys_zs i] using xs_ys i up h

lemma IsSubset_compat_trans {xs ys zs : Is}
  (xs_ys : xs ⊑ ys) (ys_zs : ys ∼ zs) :
  xs ∼ zs := by
  intro i
  cases hxs : lookup xs i with
  | none => exact compatVal_none_any (lookup zs i)
  | some up => simpa [xs_ys i up hxs] using ys_zs i

lemma IsSubset_compat {xs ys : Is}
  (xs_ys : xs ⊑ ys) :
  xs ∼ ys := by
  apply IsSubset_compat_trans xs_ys IsCompat_refl

lemma IsSubset_unionIss_compat_inv {xs ys : Is} {xss : Iss}
  (xs_ys : xs ⊑ ys) (hys : IssCompat (ys :: xss)) :
  IssCompat (xs :: xss) := by
  intro zs ws zs_in ws_in
  rcases List.mem_cons.mp zs_in with h1 | h2
  · rcases List.mem_cons.mp ws_in with h1' | h2'
    · subst h1 h1'
      simp_all only [List.mem_cons, true_or]
      exact IsCompat_refl
    · rw [h1]
      apply IsSubset_compat_trans
      · exact xs_ys
      · apply hys
        · subst h1
          simp_all only [List.mem_cons, true_or, or_true]
        · subst h1
          simp_all only [List.mem_cons, true_or, or_true]
  · rcases List.mem_cons.mp ws_in with h1' | h2'
    · rw [h1']
      apply IsCompat_symm
      · apply IsSubset_compat_trans
        · exact xs_ys
        · subst h1'
          simp_all only [List.mem_cons, or_true, true_or]
          apply hys
          · simp_all only [List.mem_cons, true_or]
          · simp_all only [List.mem_cons, or_true]
    · apply hys
      · simp_all only [List.mem_cons, or_true]
      · simp_all only [List.mem_cons, or_true]

theorem unionIs_comm {xs ys : Is}
  (xs_ys : xs ∼ ys) (ys_xs : ys ∼ xs) :
  (unionIs xs ys xs_ys) ≈ (unionIs ys xs ys_xs) := by
  intro i
  rw [lookup_unionIs_eq xs ys xs_ys i]
  rw [lookup_unionIs_eq ys xs ys_xs i]
  exact joinVal_comm (lookup xs i) (lookup ys i) (xs_ys i) (ys_xs i)

theorem unionIs_equiv {xs ys zs ws : Is}
  (xs_ys : xs ≈ ys) (zs_ws : zs ≈ ws)
  (xs_zs : xs ∼ zs) (ys_ws : ys ∼ ws) :
  unionIs xs zs xs_zs ≈ unionIs ys ws ys_ws := by
  intro i
  simp only [lookup_unionIs_eq]
  simp only [xs_ys i, zs_ws i]

lemma unionIs_subset {xs ys : Is}
  (xs_ys : xs ∼ ys) :
  (xs ⊑ unionIs xs ys xs_ys) ∧ (ys ⊑ unionIs xs ys xs_ys) := by
  constructor
  · intro i up h
    rw [lookup_unionIs_eq xs ys xs_ys i]
    simp_all only
    rfl
  · intro i up h
    rw [lookup_unionIs_eq xs ys xs_ys i]
    simp_all only
    apply joinVal_some_right

lemma unionIs_empty_left_equiv {xs : Is} (empty_xs : empty ∼ xs) :
  unionIs empty xs empty_xs ≈ xs := by
  intro i
  rw [lookup_unionIs_eq empty xs empty_xs i]
  rfl

lemma IsSubset_unionIs_dist {xs ys zs : Is}
  (xs_ys : xs ⊑ ys)
  (xs_zs : xs ∼ zs) (ys_zs : ys ∼ zs) :
  (unionIs xs zs xs_zs) ⊑ (unionIs ys zs ys_zs) := by
  intro i up h
  rw [lookup_unionIs_eq ys zs ys_zs i]
  rw [lookup_unionIs_eq xs zs xs_zs i] at h
  have h' := xs_zs i
  have h'' := ys_zs i
  have h''' := joinVal_some_inv h' h
  rcases h''' with h1 | h2
  · have eq := xs_ys i up h1
    simp_all only
  · simp_all only
    apply joinVal_some_right

lemma IsSubset_unionIss_dist {acc₁ acc₂ : Is} {xss : Iss}
  (acc₁_acc₂ : acc₁ ⊑ acc₂)
  (h₁ : IssCompat (acc₁ :: xss))
  (h₂ : IssCompat (acc₂ :: xss)) :
  (unionIssAcc acc₁ xss h₁) ⊑ (unionIssAcc acc₂ xss h₂) := by
  induction xss generalizing acc₁ acc₂ with
  | nil =>
      simpa [unionIssAcc] using acc₁_acc₂
  | cons xs xss ih =>
      dsimp [unionIssAcc]
      apply ih
      exact IsSubset_unionIs_dist acc₁_acc₂
        (h₁ acc₁ xs List.mem_cons_self
          (List.mem_cons_of_mem acc₁ List.mem_cons_self))
        (h₂ acc₂ xs List.mem_cons_self
          (List.mem_cons_of_mem acc₂ List.mem_cons_self))

lemma unionIss_singleton {xs : Is} :
  xs ≈ unionIss (xss := [xs]) (by exact IssCompat_singleton) := by
  exact IsRelEquiv.symm
    (unionIs_empty_left_equiv (IsCompat_empty_any : empty ∼ xs))

lemma unionIssAcc_compat_acc {acc : Is} {xss : Iss}
  (compat : IssCompat (acc :: xss)) :
  acc ⊑ unionIssAcc acc xss compat := by
  induction xss generalizing acc with
  | nil =>
      exact IsSubset_refl
  | cons xs xss ih =>
      dsimp [unionIssAcc]
      apply IsSubset_trans
      · exact (unionIs_subset
          (compat acc xs List.mem_cons_self
            (List.mem_cons_of_mem acc List.mem_cons_self))).left
      · apply ih

lemma unionIss_compat_part {xs : Is} {xss : Iss}
  (compat : IssCompat xss) (h : xs ∈ xss) :
  xs ⊑ unionIss compat := by
  induction xss with
  | nil => contradiction
  | cons ys xss' ih =>
      rcases List.mem_cons.mp h with h_head | h_tail
      · rw [h_head]
        unfold unionIss
        dsimp [unionIssAcc]
        apply IsSubset_trans
        · exact IsEq_subset
            (unionIs_empty_left_equiv (IsCompat_empty_any : empty ∼ ys))
        · apply unionIssAcc_compat_acc
      · unfold unionIss
        dsimp [unionIssAcc]
        exact IsSubset_trans
          (ih (IssCompat_inv_cons ys xss' compat) h_tail)
          (IsSubset_unionIss_dist
            (by
              intro i up h_empty
              unfold lookup empty at h_empty
              cases h_empty)
            (IssCompat_empty_any (IssCompat_inv_cons ys xss' compat))
            (IssCompat_unionIs_cons empty ys xss'
              (IssCompat_empty_any compat)))

lemma unionIss_subset_compat_part {xs ys : Is} {xss : Iss}
  (compat : IssCompat xss) (h : ys ⊑ unionIss compat)
  (hIn : xs ∈ xss) :
  xs ∼ ys := by
  apply IsSubset_compat_trans
  · exact unionIss_compat_part compat hIn
  · exact IsCompat_symm (IsSubset_compat h)

lemma unionIss_compat_tail {xs zs : Is} {xss : Iss}
  (compat : IssCompat (xs :: xss))
  (compat' : IssCompat xss)
  (h : unionIss compat ⊑ zs) :
  unionIss compat' ⊑ zs := by
  have tailFull : unionIss compat' ⊑ unionIss compat := by
    unfold unionIss
    exact IsSubset_unionIss_dist
      (acc₁ := empty)
      (acc₂ := unionIs empty xs (IsCompat_empty_any : empty ∼ xs))
      (xss := xss)
      (by
        intro i up h_empty
        unfold lookup empty at h_empty
        cases h_empty)
      (IssCompat_empty_any compat')
      (IssCompat_unionIs_cons empty xs xss (IssCompat_empty_any compat))
  exact IsSubset_trans tailFull h

lemma unionIss_two_eq {xs ys : Is}
  (xs_ys : xs ∼ ys) :
  unionIss (IssCompat_two xs_ys) =
  unionIs xs ys xs_ys := by
  simp only [unionIss, unionIs, unionIssAcc, empty]
  constructor

lemma unionIss_two_eq' {xs ys : Is}
  (xs_ys : IssCompat [xs, ys]) :
  unionIss xs_ys =
  unionIs xs ys (IssCompat_two_inv xs_ys) := by
  simp only [unionIss, unionIs, unionIssAcc, empty]
  constructor

def disjointIs (xs ys : Is) : Prop :=
  (i : Id) → (lookup xs i = none) ∨ (lookup ys i = none)

infix:70 " ⊥ " => disjointIs

theorem disjointIs_comm {xs ys : Is} (xs_disjoint_ys : xs ⊥ ys) :
  ys ⊥ xs := by
  intro i
  have h := xs_disjoint_ys i
  rcases h with h1 | h2
  · simp_all only [or_true]
  · simp_all only [true_or]

lemma disjointIs_empty_any {xs : Is} : empty ⊥ xs := by
  intro i
  apply Or.inl
  rfl

lemma disjointIs_any_empty {xs : Is} : xs ⊥ empty := by
  intro i
  apply Or.inr
  rfl

theorem disjointIs_compat {xs ys : Is} (xs_disjoint_ys : xs ⊥ ys) :
  xs ∼ ys := by
  intro i
  have h := xs_disjoint_ys i
  rcases h with h1 | h2
  · rw [h1]
    apply compatVal_none_any
  · rw [h2]
    apply compatVal_any_none

theorem minusIs_disjoint {xs ys : Is} :
  (xs ⊥ (ys ∖ xs)) := by
  intro i
  cases hxs : lookup xs i with
  | none => exact Or.inl rfl
  | some up =>
    apply Or.inr
    rw [lookup_minusIs_eq]
    rw [hxs]
    rw [minusVal_some_right]

theorem minusIs_subset {xs ys : Is} :
  (xs ∖ ys) ⊑ xs := by
  intro i up h
  rw [lookup_minusIs_eq] at h
  exact (minusVal_some_inv h).1

lemma minusIs_some_none_some {xs ys : Is} {i : Id} {up : UpperBound}
  (h : lookup xs i = some up)
  (h' : lookup ys i = none) :
  lookup (xs ∖ ys) i = some up := by
  rw [lookup_minusIs_eq]
  rw [h']
  rw [minusVal_none_right]
  exact h

lemma minusIs_none_none {xs ys : Is} {i : Id}
  (h : lookup xs i = none) :
  lookup (xs ∖ ys) i = none := by
  rw [lookup_minusIs_eq]
  rw [h]
  rw [minusVal_none_left]

theorem minusIs_union_eq {xs ys : Is}
  (xs_ys : xs ⊑ ys) :
  unionIs xs (ys ∖ xs) (disjointIs_compat minusIs_disjoint) ≈ ys := by
  intro i
  rw [lookup_unionIs_eq]
  by_cases h : lookup ys i = none
  · have hxy : (lookup (ys ∖ xs) i) = none :=
      minusIs_none_none h
    simp_all only
    rw [joinVal_none_right]
    by_cases h' : lookup xs i = none
    · exact h'
    · obtain ⟨b , hEq'⟩ := Option.ne_none_iff_exists'.mp h'
      simp_all only [reduceCtorEq, not_false_eq_true]
      have hV := xs_ys i b hEq'
      simp_all only [reduceCtorEq]
  · obtain ⟨a , hEq⟩ := Option.ne_none_iff_exists'.mp h
    simp_all only
    by_cases h' : lookup xs i = none
    · simp_all only
      rw [joinVal_none_left]
      exact minusIs_some_none_some hEq h'
    · obtain ⟨b , hEq'⟩ := Option.ne_none_iff_exists'.mp h'
      simp_all only
      rw [joinVal_some_left]
      have hV := xs_ys i b hEq'
      simp_all only [reduceCtorEq, not_false_eq_true, Option.some.injEq]

theorem minusIs_eq_empty {xs ys : Is}
  (xs_ys : xs ≈ ys) :
  (xs ∖ ys) ≈ empty := by
  intro i
  simp only [lookup_minusIs_eq]
  simp only [lookup_empty_none]
  simp only [xs_ys i]
  simp only [minusVal_refl]

theorem minusIs_refl_empty {xs : Is} :
  (xs ∖ xs) ≈ empty := by
  apply minusIs_eq_empty
  simp only [Setoid.refl]

end ShapeProperties
