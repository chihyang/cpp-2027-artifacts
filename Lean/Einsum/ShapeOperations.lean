import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Einsum.NamedShape

namespace ShapeOperations
open NamedShape

abbrev Unique := NamedShape.Unique

def unionPairs (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) : List Dim :=
  match xs with
  | [] => ys
  | (x, up) :: xs' =>
    if h : (ys.map Prod.fst).contains x then
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      unionPairs xs' ys hx' hy
    else
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      (x, up) :: unionPairs xs' ys hx' hy

lemma unionPairs_not_mem_key (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) {x : Id}
  (x_notin_xs : x ∉ xs.map Prod.fst)
  (x_notin_ys : x ∉ ys.map Prod.fst) :
  x ∉ (unionPairs xs ys hx hy).map Prod.fst := by
  induction xs with
  | nil =>
      unfold unionPairs
      exact x_notin_ys
  | cons dim xs ih =>
      unfold unionPairs
      split
      · exact ih _ (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))
      · change x ∉ dim.1 :: (unionPairs xs ys _ hy).map Prod.fst
        intro x_mem
        rcases List.mem_cons.mp x_mem with x_eq_dim | x_mem_tail
        · exact x_notin_xs (by simp [x_eq_dim])
        · exact ih _
            (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))
            x_mem_tail

lemma unionPairs_nodup (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) :
  Unique (unionPairs xs ys hx hy) := by
  unfold Unique
  unfold Unique at hx
  unfold Unique at hy
  induction xs with
  | nil =>
    unfold unionPairs
    exact hy
  | cons dim xs ih =>
    unfold unionPairs
    split
    · apply ih
    · apply List.nodup_cons.2
      constructor
      · apply unionPairs_not_mem_key
        · exact fun dim_mem_xs => (List.nodup_cons.1 hx).1 dim_mem_xs
        · simpa using ‹¬(ys.map Prod.fst).contains dim.1›
      · apply ih

def unionIs (xs ys : Is) (h : xs ∼ ys) : Is :=
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    { pairs := unionPairs xpairs ypairs xnodup ynodup
      noDup := unionPairs_nodup xpairs ypairs xnodup ynodup }

lemma unionPairs_subset_refl (xs ys : List Dim)
  (hx : Unique xs)
  (hy : Unique ys)
  (hxy : ∀ id, id ∈ xs.map Prod.fst → id ∈ ys.map Prod.fst) :
  unionPairs xs ys hx hy = ys := by
  induction xs with
  | nil =>
      rfl
  | cons dim xs ih =>
      unfold unionPairs
      split
      · apply ih
        intro id id_mem
        exact hxy id (List.mem_cons_of_mem dim.1 id_mem)
      · have : (ys.map Prod.fst).contains dim.1 = true := by
          simpa using hxy dim.1 (by simp)
        contradiction

lemma unionPairs_refl (xs : List Dim)
  (hx : Unique xs) :
  unionPairs xs xs hx hx = xs := by
  exact unionPairs_subset_refl xs xs hx hx (by
    intro id id_mem
    exact id_mem)

lemma lookupPairs_head
  (i : Id) (u : UpperBound)
  (xs : List Dim) :
  lookupPairs ((i , u) :: xs) i = some u := by
  unfold lookupPairs
  simp only [BEq.rfl, List.find?_cons_of_pos, Option.map_some]

lemma lookupPairs_tail
  (i : Id) (u : UpperBound)
  (xs : List Dim)
  (i' : Id)
  (h : i ≠ i') :
  lookupPairs ((i , u) :: xs) i' = lookupPairs xs i' := by
  unfold lookupPairs
  simp_all only [ne_eq,
    beq_iff_eq, not_false_eq_true,
    List.find?_cons_of_neg]

lemma lookupPairs_not_mem_none {xs : List Dim} {i : Id}
  (h : i ∉ xs.map Prod.fst) :
  lookupPairs xs i = none := by
  induction xs with
  | nil => rfl
  | cons dim xs ih =>
    cases dim with
    | mk id up =>
        have hid : id ≠ i := by
          intro hid
          exact h (by simp [hid])
        have htail : i ∉ xs.map Prod.fst := by
          intro i_mem
          exact h (List.mem_cons_of_mem id i_mem)
        rw [lookupPairs_tail id up xs i hid]
        exact ih htail

@[simp]
lemma lookupPairs_empty_none {i : Id} :
  lookupPairs [] i = none := by
  apply lookupPairs_not_mem_none
  simp only [List.map_nil, List.not_mem_nil, not_false_eq_true]

@[simp]
lemma lookup_empty_none {i : Id} :
  lookup empty i = none := by
  unfold lookup empty
  simp only [lookupPairs_empty_none]

lemma IsCompat_tail
  (i : Id) (u : UpperBound)
  (xs ys : List Dim)
  (hxi : Unique ((i , u) :: xs))
  (hx : Unique xs)
  (hy : Unique ys)
  (h : Is.mk ((i , u) :: xs) hxi ∼ Is.mk ys hy) :
  Is.mk xs hx ∼ Is.mk ys hy := by
  intro i'
  by_cases hi : i = i'
  · rw [← hi]
    have i_notin_xs : i ∉ xs.map Prod.fst := by
      unfold Unique at hxi
      exact (List.nodup_cons.1 hxi).1
    have lookup_xs_i : lookup (Is.mk xs hx) i = none := by
      exact lookupPairs_not_mem_none i_notin_xs
    rw [lookup_xs_i]
    apply compatVal_none_any
  · have hi' : i ≠ i' := hi
    simpa [lookup_mk, lookupPairs_tail i u xs i' hi'] using h i'

lemma lookupPairs_contain_some
  (xs : List Dim)
  (id : Id)
  (hin : (xs.map Prod.fst).contains id = true) :
  lookupPairs xs id ≠ none := by
  induction xs with
  | nil => contradiction
  | cons dim xs ih =>
    cases dim with
    | mk id' up =>
      by_cases h : id = id'
      · rw [h]
        rw [lookupPairs_head]
        simp only [ne_eq, reduceCtorEq, not_false_eq_true]
      · rw [lookupPairs_tail id' up xs id]
        · apply ih
          simp_all only [List.contains_eq_mem, List.mem_map,
            Prod.exists, exists_and_right, exists_eq_right,
            decide_eq_true_eq, ne_eq, forall_exists_index,
            List.map_cons, List.mem_cons, false_or,
            List.decide_mem_cons, Bool.or_eq_true, beq_iff_eq,
            decide_true]
        · simp only [ne_eq]
          intro eq
          exact (h eq.symm)

lemma lookupPairs_compat_some
  (xs ys : List Dim)
  (neq₁ : Unique xs)
  (neq₂ : Unique ys)
  (hxy : Is.mk xs neq₁ ∼ Is.mk ys neq₂)
  (id : Id) (u : UpperBound)
  (h : lookupPairs xs id = some u)
  (hin : (ys.map Prod.fst).contains id = true) :
  lookupPairs ys id = some u := by
  have hn := lookupPairs_contain_some ys id hin
  rw [CompatVal_some_eq (v := lookupPairs ys id)]
  · rw [← h]
    exact hxy id
  · exact hn

lemma lookupPairs_unionPairs_eq
  (pairs₁ pairs₂ : List Dim)
  (neq₁ : Unique pairs₁)
  (neq₂ : Unique pairs₂)
  (hxy : Is.mk pairs₁ neq₁ ∼ Is.mk pairs₂ neq₂)
  (i : Id) :
  lookupPairs (unionPairs pairs₁ pairs₂ neq₁ neq₂) i =
  (joinVal (lookupPairs pairs₁ i) (lookupPairs pairs₂ i) (hxy i)) := by
  induction pairs₁ with
  | nil =>
    unfold unionPairs
    simp [lookupPairs, joinVal]
  | cons dim xs ih =>
    unfold unionPairs
    split
    · rename_i heq
      by_cases hi : i = dim.1
      · rw [hi] at ih
        simp only
        rw [hi]
        cases dim with
        | mk id up =>
          simp only at hi
          simp only [lookupPairs_head]
          rw [joinVal_some_left]
          rw [ih]
          · have hEq : lookupPairs pairs₂ i = some up := by
              apply lookupPairs_compat_some ((id , up) :: xs) pairs₂ neq₁ neq₂ hxy
              · rw [hi]
                rw [lookupPairs_head]
              · rw [hi]
                exact heq
            simp only
            rw [hi] at hEq
            subst hi
            simp_all only
            rw [joinVal_some_right]
          · apply IsCompat_tail id up xs pairs₂ neq₁
            exact hxy
      · simp only
        cases dim with
        | mk id up =>
          have hid : id ≠ i := fun h => hi h.symm
          rw [ih]
          · simp [lookupPairs_tail, hid]
          · apply IsCompat_tail id up xs pairs₂ neq₁
            exact hxy
    · by_cases hi : i = dim.1
      · rw [hi] at ih
        simp only [Prod.mk.eta]
        rw [hi]
        rw [lookupPairs_head]
        have h' := Prod.mk.eta (p := dim)
        cases dim with
        | mk id up =>
          simp only [lookupPairs_head]
          rw [joinVal_some_left]
      · simp only [Prod.mk.eta]
        rw [lookupPairs_tail]
        · cases dim with
          | mk id up =>
            have hid : id ≠ i := fun h => hi h.symm
            rw [ih]
            · simp [lookupPairs_tail, hid]
            · apply IsCompat_tail id up xs pairs₂
              exact hxy
        · simp only [ne_eq]
          intro eq
          exact (hi eq.symm)

theorem lookup_unionIs_eq (xs ys : Is)
  (hxy : xs ∼ ys)
  (id : Id) :
  lookup (unionIs xs ys hxy) id =
  (joinVal (lookup xs id) (lookup ys id) (hxy id)) := by
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    exact lookupPairs_unionPairs_eq xpairs ypairs xnodup ynodup hxy id

theorem lookup_unionIs_some (xs ys : Is) (h : xs ∼ ys)
  (id : Id) (up : UpperBound)
  (hEq : lookup (unionIs xs ys h) id = some up) :
  lookup xs id = some up ∨ lookup ys id = some up := by
  rw [lookup_unionIs_eq] at hEq
  exact joinVal_some_inv (h id) hEq

theorem lookup_unionIs_none (xs ys : Is) (h : xs ∼ ys)
  (id : Id) (hEq : lookup (unionIs xs ys h) id = none) :
  lookup xs id = none ∧ lookup ys id = none := by
  rw [lookup_unionIs_eq] at hEq
  exact joinVal_none_inv (h id) hEq

theorem unionIs_compat_args (xs ys : Is) (h : xs ∼ ys) :
  unionIs xs ys h ∼ xs ∧ unionIs xs ys h ∼ ys:= by
  constructor
  · intro i
    rw [lookup_unionIs_eq]
    apply joinVal_compat_left
  · intro i
    rw [lookup_unionIs_eq]
    apply joinVal_compat_right

lemma unionIs_part_full {xs ys zs : Is}
  (xs_compat_ys : xs ∼ ys)
  (xs_compat_zs : xs ∼ zs)
  (ys_compat_zs : ys ∼ zs) :
  (xs ∼ (unionIs ys zs ys_compat_zs)) := by
  intro i
  rw [lookup_unionIs_eq]
  apply compatVal_symm
  · apply joinVal_compat_of_compat
    · have h := IsCompat_symm xs_compat_ys
      exact h i
    · have h := IsCompat_symm xs_compat_zs
      exact h i

lemma IssCompat_unionIs_cons (acc xs : Is) (xss : Iss)
  (compat : IssCompat (acc :: xs :: xss)) :
  IssCompat
    (unionIs acc xs
      (compat acc xs List.mem_cons_self
        (List.mem_cons_of_mem acc List.mem_cons_self)) :: xss) := by
  let acc' :=
    unionIs acc xs
      (compat acc xs List.mem_cons_self
        (List.mem_cons_of_mem acc List.mem_cons_self))
  intro ys zs ys_in zs_in
  rcases List.mem_cons.mp ys_in with rfl | ys_in_tail
  · rcases List.mem_cons.mp zs_in with rfl | zs_in_tail
    · exact IsCompat_refl
    · apply IsCompat_symm
      · apply unionIs_part_full
        · apply compat zs acc
          · simp_all only [List.mem_cons, or_true, true_or]
          · simp_all only [List.mem_cons, or_true, true_or]
        · apply compat zs xs
          · simp_all only [List.mem_cons, or_true, true_or]
          · simp_all only [List.mem_cons, or_true, true_or]
  · rcases List.mem_cons.mp zs_in with rfl | zs_in_tail
    · apply unionIs_part_full
      · apply compat ys acc
        · simp_all only [List.mem_cons, or_true, true_or]
        · simp_all only [List.mem_cons, or_true, true_or]
      · apply compat ys xs
        · simp_all only [List.mem_cons, or_true, true_or]
        · simp_all only [List.mem_cons, or_true, true_or]
    · apply compat ys zs
      · simp_all only [List.mem_cons, or_true]
      · simp_all only [List.mem_cons, or_true]

def unionIssAcc (acc : Is) (xss : Iss)
  (compat : IssCompat (acc :: xss)) : Is :=
  match xss with
  | [] => acc
  | xs :: xss' =>
    have acc_in : acc ∈ acc :: xs :: xss' := List.mem_cons_self
    have xs_in : xs ∈ acc :: xs :: xss' :=
      List.mem_cons_of_mem acc List.mem_cons_self
    let acc' := unionIs acc xs (compat acc xs acc_in xs_in)
    have compat' : IssCompat (acc' :: xss') :=
      IssCompat_unionIs_cons acc xs xss' compat
    unionIssAcc acc' xss' compat'

def unionIss {xss : Iss} (compat : IssCompat xss) : Is :=
  unionIssAcc empty xss (IssCompat_empty_any compat)

def intersectVal (v₁ v₂ : Option UpperBound) (h : CompatVal v₁ v₂) : Option UpperBound :=
  match v₁ , v₂ with
  | some u , some _ => some u
  | _ , _ => none

theorem intersectVal_refl {u : Option UpperBound} {compat : u ∼ᵢ u} :
  intersectVal u u compat = u := by
  match u with
  | some _ => rfl
  | none => rfl

theorem intersectVal_comm (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v2_comp_v1 : v₂ ∼ᵢ v₁) :
  intersectVal v₁ v₂ v1_comp_v2 = intersectVal v₂ v₁ v2_comp_v1 := by
  match v₁ , v₂ with
  | none , none => rfl
  | some u , none => rfl
  | none , some u => rfl
  | some u₁ , some u₂ =>
    have u1_u2_eq := by exact compatVal_inv_eq v1_comp_v2
    subst u1_u2_eq
    simp_all only

theorem intersectVal_irrl (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v1_comp_v2' : v₁ ∼ᵢ v₂) :
  intersectVal v₁ v₂ v1_comp_v2 = intersectVal v₁ v₂ v1_comp_v2' := by
  match v₁ , v₂ with
  | none , none => rfl
  | some u , none => rfl
  | none , some u => rfl
  | some u₁ , some u₂ =>
    have u1_u2_eq := by exact compatVal_inv_eq v1_comp_v2
    subst u1_u2_eq
    simp_all only

lemma intersectVal_none_left (v : Option UpperBound)
  (p : none ∼ᵢ v) :
  intersectVal none v p = none := by
  rfl

lemma intersectVal_none_right (v : Option UpperBound)
  (p : v ∼ᵢ none) :
  intersectVal v none p = none := by
  rw [intersectVal_comm v none p (compatVal_symm p)]
  rfl

lemma intersectVal_some_left (u : UpperBound) (v : Option UpperBound)
  (p : some u ∼ᵢ v) :
  intersectVal (some u) v p = v := by
  match p with
  | CompatVal.vv _ => rfl
  | CompatVal.vn _ => rfl

theorem intersectVal_compat_left (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  intersectVal v₁ v₂ v1_comp_v2 ∼ᵢ v₁ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.vv v
  | nv v => exact CompatVal.nn
  | vn v => exact CompatVal.nv v

theorem intersectVal_compat_right (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  intersectVal v₁ v₂ v1_comp_v2 ∼ᵢ v₂ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.vv v
  | nv v => exact CompatVal.nv v
  | vn v => exact CompatVal.nn

theorem intersectVal_compat_of_compat {v₁ v₂ v₃ : Option UpperBound}
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v1_comp_v3 : v₁ ∼ᵢ v₃)
  (v2_comp_v3 : v₂ ∼ᵢ v₃) :
  intersectVal v₁ v₂ v1_comp_v2 ∼ᵢ v₃ := by
  cases v1_comp_v2 <;> cases v1_comp_v3 <;> cases v2_comp_v3 <;>
    simp [intersectVal]
  all_goals constructor

def intersectPairs (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) : List Dim :=
  match xs with
  | [] => []
  | (x, up) :: xs' =>
    if h : (ys.map Prod.fst).contains x then
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      (x, up) :: intersectPairs xs' ys hx' hy
    else
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      intersectPairs xs' ys hx' hy

lemma intersectPairs_not_mem_key (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) {x : Id}
  (x_notin_xs : x ∉ xs.map Prod.fst) :
  x ∉ (intersectPairs xs ys hx hy).map Prod.fst := by
  induction xs with
  | nil =>
    unfold intersectPairs
    simp only [List.map_nil, List.not_mem_nil, not_false_eq_true]
  | cons dim xs ih =>
    unfold intersectPairs
    split
    · change x ∉ dim.1 :: (intersectPairs xs ys _ hy).map Prod.fst
      intro x_mem
      rcases List.mem_cons.mp x_mem with x_eq_dim | x_mem_tail
      · exact x_notin_xs (by simp [x_eq_dim])
      · exact ih _
          (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))
          x_mem_tail
    · exact ih _ (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))

lemma intersectPairs_nodup (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) :
  Unique (intersectPairs xs ys hx hy) := by
  unfold Unique
  unfold Unique at hx
  unfold Unique at hy
  induction xs with
  | nil =>
    unfold intersectPairs NamedShape.Unique
    simp only [List.map_nil, List.nodup_nil]
  | cons dim xs ih =>
    unfold intersectPairs
    split
    · apply List.nodup_cons.2
      constructor
      · apply intersectPairs_not_mem_key
        exact fun dim_mem_xs => (List.nodup_cons.1 hx).1 dim_mem_xs
      · apply ih
    · apply ih

def intersectIs (xs ys : Is) (h : xs ∼ ys) : Is :=
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    { pairs := intersectPairs xpairs ypairs xnodup ynodup
      noDup := intersectPairs_nodup xpairs ypairs xnodup ynodup }

lemma lookupPairs_intersectPairs_eq
  (pairs₁ pairs₂ : List Dim)
  (neq₁ : Unique pairs₁)
  (neq₂ : Unique pairs₂)
  (hxy : Is.mk pairs₁ neq₁ ∼ Is.mk pairs₂ neq₂)
  (i : Id) :
  lookupPairs (intersectPairs pairs₁ pairs₂ neq₁ neq₂) i =
  (intersectVal (lookupPairs pairs₁ i) (lookupPairs pairs₂ i) (hxy i)) := by
  induction pairs₁ with
  | nil =>
    unfold intersectPairs
    simp only [lookupPairs_empty_none]
    rw [intersectVal_none_left]
  | cons dim xs ih =>
    unfold intersectPairs
    split
    · rename_i hNe
      by_cases hEq : i = dim.1
      · obtain ⟨x, u⟩ := dim
        rw [hEq]
        rw [lookupPairs_head]
        have hL : lookupPairs (⟨x, u⟩ :: xs) x = some u := by
          rw [lookupPairs_head]
        have hPairs2 : lookupPairs pairs₂ x ≠ none := by
          apply lookupPairs_contain_some
          exact hNe
        have hL2 : lookupPairs pairs₂ x = some u := by
          apply CompatVal_some_eq
          · rw [← hL]
            apply hxy
          · exact hPairs2
        simp_all only
        rw [intersectVal_refl]
      · rw [lookupPairs_tail]
        · obtain ⟨x, u⟩ := dim
          simp only at hEq
          have hXs : lookupPairs (⟨x, u⟩ :: xs) i = lookupPairs xs i := by
            apply lookupPairs_tail
            simp only [ne_eq]
            intro a
            exact hEq a.symm
          simp only [hXs]
          rw [ih]
          apply IsCompat_tail x u xs pairs₂ neq₁
          exact hxy
        · simp only [ne_eq]
          intro a
          exact hEq a.symm
    · by_cases hEq : dim.1 = i
      · simp only
        rw [← hEq]
        obtain ⟨x, u⟩ := dim
        subst hEq
        simp only [lookupPairs_head x u xs]
        rw [intersectVal_some_left]
        rename_i h
        rw [ih]
        · simp only
          have hPairs₂ : lookupPairs pairs₂ x = none := by
            apply lookupPairs_not_mem_none
            simp only at h
            grind only [= List.contains_eq_mem]
          simp only [hPairs₂]
          rw [intersectVal_none_right]
        · apply IsCompat_tail x u xs pairs₂ neq₁
          exact hxy
      · simp only
        obtain ⟨x, u⟩ := dim
        have hXs : lookupPairs (⟨x, u⟩ :: xs) i = lookupPairs xs i := by
            apply lookupPairs_tail
            simp only [ne_eq]
            intro a
            exact hEq a
        simp only [hXs]
        rw [ih]
        apply IsCompat_tail x u xs pairs₂ neq₁
        exact hxy

theorem lookup_intersectIs_eq (xs ys : Is)
  (hxy : xs ∼ ys)
  (id : Id) :
  lookup (intersectIs xs ys hxy) id =
  (intersectVal (lookup xs id) (lookup ys id) (hxy id)) := by
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    exact lookupPairs_intersectPairs_eq xpairs ypairs xnodup ynodup hxy id

def minusVal (u v : Option UpperBound) : Option UpperBound :=
  match u , v with
  | some u , none => some u
  | _ , _ => none

infix:70 " ∖ᵢ " => minusVal

@[simp]
lemma minusVal_refl (v : Option UpperBound) :
  minusVal v v = none := by
  match v with
  | none => rfl
  | some u => rfl

lemma minusVal_none_left (v : Option UpperBound) :
  minusVal none v = none := by
  rfl

lemma minusVal_none_right (v : Option UpperBound) :
  minusVal v none = v := by
  match v with
  | none => rfl
  | some u => rfl

theorem minusVal_some_inv {x y : Option UpperBound} {v : UpperBound}
  (h : (x ∖ᵢ y) = some v) :
  x = some v ∧ y = none := by
  match x , y with
  | some u , none =>
    simp only [minusVal] at h
    constructor
    · exact h
    · simp only
  | some u , some v =>
    simp only [minusVal] at h
    contradiction
  | none , _ => contradiction

lemma minusVal_some_right (v : Option UpperBound) (u : UpperBound) :
  minusVal v (some u) = none := by
  match v with
  | none => rfl
  | some u => rfl

theorem minusVal_compat_left (x y : Option UpperBound) : (x ∖ᵢ y) ∼ᵢ x := by
  match x , y with
  | some u , none => exact CompatVal.vv u
  | some u , some v => exact CompatVal.nv u
  | none , _ => exact CompatVal.nn

theorem minusVal_compat_right (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  minusVal v₁ v₂ ∼ᵢ v₂ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.nv v
  | nv v => exact CompatVal.nv v
  | vn v => exact CompatVal.vn v

theorem minusVal_compat_of_compat {v₁ v₂ v₃ : Option UpperBound}
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v1_comp_v3 : v₁ ∼ᵢ v₃)
  (v2_comp_v3 : v₂ ∼ᵢ v₃) :
  minusVal v₁ v₂ ∼ᵢ v₃ := by
  cases v1_comp_v2 <;> cases v1_comp_v3 <;> cases v2_comp_v3 <;>
    simp [minusVal]
  all_goals constructor

lemma minusVal_joinVal_self_left (x y : Option UpperBound)
  (x_y : x ∼ᵢ y) :
  (x ∖ᵢ (joinVal x y x_y) = none) := by
  match x with
  | none => rfl
  | some u =>
    simp only [joinVal_some_left]
    rfl

lemma joinVal_minusVal_eq_right (x y : Option UpperBound)
  (x_y : x ∼ᵢ y) :
  joinVal x y x_y ∖ᵢ (x ∖ᵢ y) = y := by
  match x with
  | none =>
    simp only [joinVal_none_left, minusVal_none_left, minusVal_none_right]
  | some u =>
    simp only [joinVal_some_left]
    match y with
    | none => rfl
    | some v =>
      simp_all only [minusVal_some_right, minusVal_none_right]
      simp only [Option.some.injEq]
      exact compatVal_inv_eq x_y

def minusPairs (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) : List Dim :=
  match xs with
  | [] => []
  | (x, up) :: xs' =>
    if h : (ys.map Prod.fst).contains x then
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      minusPairs xs' ys hx' hy
    else
      have hx' := by
        unfold Unique
        unfold Unique at hx
        exact (List.nodup_cons.1 hx).2
      (x, up) :: minusPairs xs' ys hx' hy

lemma minusPairs_not_mem_key (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) {x : Id}
  (x_notin_xs : x ∉ xs.map Prod.fst) :
  x ∉ (minusPairs xs ys hx hy).map Prod.fst := by
  induction xs with
  | nil =>
    unfold minusPairs
    simp only [List.map_nil, List.not_mem_nil, not_false_eq_true]
  | cons dim xs ih =>
    unfold minusPairs
    split
    · exact ih _ (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))
    · change x ∉ dim.1 :: (minusPairs xs ys _ hy).map Prod.fst
      intro x_mem
      rcases List.mem_cons.mp x_mem with x_eq_dim | x_mem_tail
      · exact x_notin_xs (by simp [x_eq_dim])
      · exact ih _
          (fun x_mem_xs => x_notin_xs (List.mem_cons_of_mem dim.1 x_mem_xs))
          x_mem_tail

lemma minusPairs_nodup (xs ys : List Dim)
  (hx : Unique xs) (hy : Unique ys) :
  Unique (minusPairs xs ys hx hy) := by
  unfold Unique
  unfold Unique at hx
  unfold Unique at hy
  induction xs with
  | nil =>
    unfold minusPairs NamedShape.Unique
    simp only [List.map_nil, List.nodup_nil]
  | cons dim xs ih =>
    unfold minusPairs
    split
    · rename_i heq
      apply ih
    · rename_i hneq
      apply List.nodup_cons.2
      constructor
      · apply minusPairs_not_mem_key
        exact fun dim_mem_xs => (List.nodup_cons.1 hx).1 dim_mem_xs
      · apply ih

def minusIs (xs ys : Is) : Is :=
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    { pairs := minusPairs xpairs ypairs xnodup ynodup
      noDup := minusPairs_nodup xpairs ypairs xnodup ynodup }

notation xs " ∖ " ys => minusIs xs ys

lemma lookupPairs_minusPairs_eq
  (pairs₁ pairs₂ : List Dim)
  (neq₁ : Unique pairs₁)
  (neq₂ : Unique pairs₂)
  (i : Id) :
  lookupPairs (minusPairs pairs₁ pairs₂ neq₁ neq₂) i =
  (minusVal (lookupPairs pairs₁ i) (lookupPairs pairs₂ i)) := by
  induction pairs₁ with
  | nil =>
    unfold minusPairs
    simp only [lookupPairs_empty_none]
    simp_all only [minusVal_none_left]
  | cons dim xs ih =>
    unfold minusPairs
    split
    · rename_i h
      simp_all only
      obtain ⟨x, u⟩ := dim
      by_cases hEq : i = x
      · rw [hEq]
        simp only [lookupPairs_head]
        have hPairs₂ : lookupPairs pairs₂ x ≠ none := by
          apply lookupPairs_contain_some
          exact h
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hPairs₂
        rw [hv]
        simp_all only [minusVal_some_right]
      · have hPairs₁ : lookupPairs ((x, u) :: xs) i = lookupPairs xs i := by
          apply lookupPairs_tail x u xs i
          intro a
          exact hEq a.symm
        rw [hPairs₁]
    · rename_i h
      simp_all only
      obtain ⟨x, u⟩ := dim
      by_cases hEq : i = x
      · rw [hEq]
        simp only [lookupPairs_head]
        have hPairs₂ : lookupPairs pairs₂ x = none := by
          apply lookupPairs_not_mem_none
          simp only at h
          grind only [= List.contains_eq_mem]
        rw [hPairs₂]
        rw [minusVal_none_right]
      · simp only
        rw [lookupPairs_tail x u (minusPairs xs pairs₂ _ neq₂) i]
        · have hPairs₁ : lookupPairs ((x, u) :: xs) i = lookupPairs xs i := by
            apply lookupPairs_tail x u xs i
            intro a
            exact hEq a.symm
          rw [hPairs₁]
          rw [ih]
        · intro a
          exact hEq a.symm

theorem lookup_minusIs_eq (xs ys : Is)
  (id : Id) :
  lookup (minusIs xs ys) id =
  (minusVal (lookup xs id) (lookup ys id)) := by
  match xs , ys with
  | { pairs := xpairs
      noDup := xnodup } ,
    { pairs := ypairs
      noDup := ynodup } =>
    exact lookupPairs_minusPairs_eq xpairs ypairs xnodup ynodup id

end ShapeOperations
