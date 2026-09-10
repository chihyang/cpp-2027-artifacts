import Mathlib.Data.List.Nodup

namespace NamedShape

abbrev UpperBound := ℕ
abbrev Id := String
-- Index sequence
abbrev Dim := Id × UpperBound
abbrev Unique (xs : List Dim) := (xs.map Prod.fst).Nodup

lemma Unique_head_not_in_tail {xs : List Dim} {x : Id} {up : UpperBound}
  (neq : Unique ((x , up) :: xs)) :
  x ∉ xs.map Prod.fst := by
  unfold Unique at neq
  exact (List.nodup_cons.1 neq).1

lemma Unique_cons {xs : List Dim} {x : Id} {up : UpperBound}
  (neq : Unique ((x , up) :: xs)) :
  Unique xs := by
  unfold Unique
  unfold Unique at neq
  simp_all only [List.map_cons, List.nodup_cons,
    List.mem_map, Prod.exists, exists_and_right,
    exists_eq_right, not_exists]

structure Is where
  pairs : List Dim
  noDup : (pairs.map Prod.fst).Nodup
abbrev Iss : Type := List Is

def Is.prod (xs : Is) : ℕ :=
  match xs with
  | { pairs := pairs , noDup := _ } =>
    (pairs.map Prod.snd).prod

def empty : Is := Is.mk [] (by simp)

def lookupPairs (xs : List Dim) (x : Id) : Option UpperBound :=
  (xs.find? fun dim => dim.1 == x).map Prod.snd

def lookup (Γ : Is) (x : Id) : Option UpperBound :=
  lookupPairs Γ.pairs x

lemma lookup_mk (pairs : List Dim) (nodup : Unique pairs) (i : Id) :
  lookup (Is.mk pairs nodup) i = lookupPairs pairs i := by
  rfl

def Fresh (id : Id) (xs : Is) : Prop :=
  (lookup xs id) = none

def updatePairs : List Dim → Id → UpperBound → List Dim
  | [], _, _ => []
  | dim :: pairs, x, up =>
      if x = dim.1 then
        (dim.1, up) :: pairs
      else
        dim :: updatePairs pairs x up

lemma updatePairs_keep_keys :
  (pairs : List Dim) → (x : Id) → (up : UpperBound) →
  (updatePairs pairs x up).map Prod.fst = pairs.map Prod.fst
  | [], _, _ => by simp [updatePairs]
  | dim :: pairs, x, up => by
      by_cases h : x = dim.1
      · simp [updatePairs, h]
      · simp [updatePairs, h, updatePairs_keep_keys pairs x up]

lemma lookup_none_not_mem {pairs : List Dim} {x : Id}
  (h : lookupPairs pairs x = none) :
  x ∉ pairs.map Prod.fst := by
  induction pairs with
  | nil => simp
  | cons dim pairs ih =>
    unfold lookupPairs at h
    by_cases hx : dim.1 = x
    · simp [hx] at h
    · have htail :
        (pairs.find? fun dim => dim.1 == x).map Prod.snd = none := by
        simpa [hx] using h
      have hx' : ¬x = dim.1 := fun x_eq_dim => hx x_eq_dim.symm
      simp [hx', ih htail]

def extend (Γ : Is) (x : Id) (up : UpperBound) : Is :=
  match h : lookup Γ x with
  | some _ =>
      { pairs := updatePairs Γ.pairs x up
        noDup := by
          rw [updatePairs_keep_keys]
          exact Γ.noDup }
  | none =>
      { pairs := (x, up) :: Γ.pairs
        noDup := by
          constructor
          · unfold lookup at h
            intro i i_mem x_eq_i
            exact lookup_none_not_mem h (by simpa [← x_eq_i] using i_mem)
          · exact Γ.noDup }

notation Γ " ⨾ " x " , " up => extend Γ x up

def fromList (dims : List (Id × UpperBound))
  (neq : (dims.map Prod.fst).Nodup) :
  Is :=
  { pairs := dims
    noDup := neq }

def fromSingleton (dim : Dim) : Is :=
  match dim with
  | (x , v) => fromList [(x, v)] (by simp)

inductive CompatVal : Option UpperBound → Option UpperBound → Prop where
  | nn : CompatVal none none
  | vv (v : UpperBound) : CompatVal (some v) (some v)
  | nv (v : UpperBound) : CompatVal none (some v)
  | vn (v : UpperBound) : CompatVal (some v) none

infix:60 " ∼ᵢ " => CompatVal

theorem compatVal_refl {v : Option UpperBound} : v ∼ᵢ v := by
  cases v with
  | none => exact CompatVal.nn
  | some v => exact CompatVal.vv v

theorem compatVal_symm {v₁ v₂ : Option UpperBound}
  (v1_comp_v2 : v₁ ∼ᵢ v₂) : v₂ ∼ᵢ v₁ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.vv v
  | nv v => exact CompatVal.vn v
  | vn v => exact CompatVal.nv v

lemma compatVal_none_any (a : Option UpperBound) : none ∼ᵢ a := by
  match a with
  | none => exact CompatVal.nn
  | some v => exact CompatVal.nv v

lemma compatVal_any_none (a : Option UpperBound) : a ∼ᵢ none := by
  exact compatVal_symm (compatVal_none_any a)

theorem CompatVal_eq_compat {v₁ v₂ : Option UpperBound}
  (h : v₁ = v₂) :
  v₁ ∼ᵢ v₂ := by
  match v₁ , v₂ with
  | none , none => exact CompatVal.nn
  | some u , none => simp_all only [reduceCtorEq]
  | none , some u => simp_all only [reduceCtorEq]
  | some u₁ , some u₂ =>
    simp_all only [Option.some.injEq]
    subst h
    exact CompatVal.vv u₁

lemma CompatVal_some_or {u : UpperBound}
  {v₁ v₂ : Option UpperBound}
  (h : v₁ = some u)
  (v1_v2 : v₁ ∼ᵢ v₂) :
  v₂ = some u ∨ v₂ = none := by
  rw [h] at v1_v2
  match v1_v2 with
  | CompatVal.vv w => exact Or.inl rfl
  | CompatVal.vn w => exact Or.inr rfl

lemma CompatVal_some_eq {u : UpperBound} {v : Option UpperBound}
  (v1_v2 : some u ∼ᵢ v) (hneq : v ≠ none) :
  v = some u := by
  match v1_v2 with
  | CompatVal.vv w => rfl
  | CompatVal.vn w => contradiction

/-! Operations on UpperBound and Is

-/
def joinVal (v₁ v₂ : Option UpperBound) (h : CompatVal v₁ v₂) : Option UpperBound :=
  match v₁ with
  | some u => some u
  | none => v₂

@[simp]
theorem joinVal_refl {u : Option UpperBound} {compat : u ∼ᵢ u} :
  joinVal u u compat = u := by
  match u with
  | some _ => rfl
  | none => rfl

theorem compatVal_inv_eq {u₁ u₂ : UpperBound}
  (v1_comp_v2 : some u₁ ∼ᵢ some u₂) :
  u₁ = u₂ := by
  cases v1_comp_v2 with
  | vv v => rfl

theorem joinVal_comm (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v2_comp_v1 : v₂ ∼ᵢ v₁) :
  joinVal v₁ v₂ v1_comp_v2 = joinVal v₂ v₁ v2_comp_v1 := by
  match v₁ , v₂ with
  | none , none => rfl
  | some u , none => rfl
  | none , some u => rfl
  | some u₁ , some u₂ =>
    have u1_u2_eq := by exact compatVal_inv_eq v1_comp_v2
    subst u1_u2_eq
    simp_all only

theorem joinVal_comm' (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  joinVal v₁ v₂ v1_comp_v2 = joinVal v₂ v₁ (compatVal_symm v1_comp_v2) := by
  apply joinVal_comm

theorem joinVal_irrl (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂)
  (v1_comp_v2' : v₁ ∼ᵢ v₂) :
  joinVal v₁ v₂ v1_comp_v2 = joinVal v₁ v₂ v1_comp_v2' := by
  match v₁ , v₂ with
  | none , none => rfl
  | some u , none => rfl
  | none , some u => rfl
  | some u₁ , some u₂ =>
    have u1_u2_eq := by exact compatVal_inv_eq v1_comp_v2
    subst u1_u2_eq
    simp_all only

lemma joinVal_some_left (u : UpperBound) (v : Option UpperBound)
  (p : some u ∼ᵢ v) :
  joinVal (some u) v p = some u := by
  match v with
  | none => rfl
  | some u' =>
    have u_eq_u' := compatVal_inv_eq p
    subst u_eq_u'
    rw [joinVal_refl]

lemma joinVal_some_right (u : UpperBound) (v : Option UpperBound)
  (p : v ∼ᵢ some u) :
  joinVal v (some u) p = some u := by
  rw [joinVal_comm v (some u) p (compatVal_symm p)]
  rw [joinVal_some_left u v (compatVal_symm p)]

lemma joinVal_none_left (v : Option UpperBound)
  (p : none ∼ᵢ v) :
  joinVal none v p = v := by
  rfl

lemma joinVal_none_right (v : Option UpperBound)
  (p : v ∼ᵢ none) :
  joinVal v none p = v := by
  rw [joinVal_comm v none p (compatVal_symm p)]
  rfl

theorem joinVal_compat_left (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  joinVal v₁ v₂ v1_comp_v2 ∼ᵢ v₁ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.vv v
  | nv v => exact CompatVal.vn v
  | vn v => exact CompatVal.vv v

theorem joinVal_compat_right (v₁ v₂ : Option UpperBound)
  (v1_comp_v2 : v₁ ∼ᵢ v₂) :
  joinVal v₁ v₂ v1_comp_v2 ∼ᵢ v₂ := by
  cases v1_comp_v2 with
  | nn => exact CompatVal.nn
  | vv v => exact CompatVal.vv v
  | nv v => exact CompatVal.vv v
  | vn v => exact CompatVal.vn v

theorem joinVal_compat_of_compat {v₁ v₂ v₃ : Option UpperBound}
  (v1_2 : v₁ ∼ᵢ v₂)
  (v1_3 : v₁ ∼ᵢ v₃)
  (v2_3 : v₂ ∼ᵢ v₃) :
  joinVal v₁ v₂ v1_2 ∼ᵢ v₃ := by
  match v1_2 with
  | .nn => apply compatVal_none_any
  | .nv v =>
    rw [joinVal_none_left]
    exact v2_3
  | .vn v =>
    rw [joinVal_none_right]
    exact v1_3
  | .vv v =>
    rw [joinVal_some_left]
    exact v1_3

lemma joinVal_some_inv {v₁ v₂ : Option UpperBound} {u : UpperBound}
  (v1_v2 : v₁ ∼ᵢ v₂)
  (h : joinVal v₁ v₂ v1_v2 = some u) :
  v₁ = some u ∨ v₂ = some u := by
  match v1_v2 with
  | CompatVal.nn =>
    simp_all only [reduceCtorEq, or_self]
    contradiction
  | CompatVal.vv v =>
    simp_all only [Option.some.injEq, or_self]
    rw [joinVal_refl] at h
    simp_all only [Option.some.injEq]
  | CompatVal.nv v =>
    rw [joinVal_none_left] at h
    simp_all only [Option.some.injEq, reduceCtorEq, or_true]
  | CompatVal.vn v =>
    rw [joinVal_none_right] at h
    simp_all only [Option.some.injEq, reduceCtorEq, or_false]

lemma joinVal_none_inv {v₁ v₂ : Option UpperBound}
  (v1_v2 : v₁ ∼ᵢ v₂)
  (h : joinVal v₁ v₂ v1_v2 = none) :
  v₁ = none ∧ v₂ = none := by
  match v1_v2 with
  | CompatVal.nn => simp only [and_self]

theorem joinVal_assoc {v₁ v₂ v₃ : Option UpperBound}
  (v1_2 : v₁ ∼ᵢ v₂)
  (v2_3 : v₂ ∼ᵢ v₃)
  (v1_3 : v₁ ∼ᵢ v₃)
  (v12_3 : (joinVal v₁ v₂ v1_2) ∼ᵢ v₃) :
  have v1_23 : (joinVal v₂ v₃ v2_3) ∼ᵢ v₁ := by
    apply joinVal_compat_of_compat
    · exact (compatVal_symm v1_2)
    · exact (compatVal_symm v1_3)
  joinVal (joinVal v₁ v₂ v1_2) v₃ v12_3 =
  joinVal v₁ (joinVal v₂ v₃ v2_3) (compatVal_symm v1_23) := by
  match v₁ with
  | none => simp only [joinVal_none_left]
  | some u => simp only [joinVal_some_left]

lemma joinVal_self_right_twice {v₁ v₂ : Option UpperBound}
  (v1_2 : v₁ ∼ᵢ v₂)
  (v12_2 : (joinVal v₁ v₂ v1_2) ∼ᵢ v₂) :
  (joinVal (joinVal v₁ v₂ v1_2) v₂ v12_2 = joinVal v₁ v₂ v1_2) := by
  match v₁ with
  | none => simp_all [joinVal_none_left]
  | some u => simp_all [joinVal_some_left]

def IsCompat (Γ Δ : Is) : Prop :=
  ∀ i, CompatVal (lookup Γ i) (lookup Δ i)

infix:50 " ∼ " => IsCompat

theorem IsCompat_refl {xs : Is} : xs ∼ xs := by
  intro i
  exact compatVal_refl

theorem IsCompat_symm {xs ys : Is} (xs_comat_ys : xs ∼ ys) :
  ys ∼ xs := by
  intro i
  exact compatVal_symm (xs_comat_ys i)

lemma IsCompat_empty_any {xs : Is} : empty ∼ xs := by
  intro i
  exact compatVal_none_any (lookup xs i)

lemma IsCompat_any_empty {xs : Is} : xs ∼ empty := by
  intro i
  exact compatVal_any_none (lookup xs i)

def IssCompat (xss : Iss) : Prop :=
  ∀ xs , ∀ ys , xs ∈ xss → ys ∈ xss → xs ∼ ys

lemma IssCompat_empty : IssCompat [] := by
  unfold IssCompat
  intro xs ys xs_in ys_in
  contradiction

lemma IssCompat_singleton {xs : Is} : IssCompat [xs] := by
  unfold IssCompat
  intro ys zs ys_in zs_in
  simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  subst ys_in zs_in
  exact IsCompat_refl

lemma IssCompat_two {xs ys : Is} (xs_ys : xs ∼ ys) : IssCompat [xs, ys] := by
  intro xs' ys' xs_in ys_in
  cases xs_in with
  | head =>
    cases ys_in with
    | head => exact IsCompat_refl
    | tail _ ys_in' =>
      cases ys_in' with
      | head => exact xs_ys
      | tail _ h => cases h
  | tail _ xs_in' =>
    cases xs_in' with
    | head =>
      cases ys_in with
      | head => exact IsCompat_symm xs_ys
      | tail _ ys_in' =>
        cases ys_in' with
        | head => exact IsCompat_refl
        | tail _ h => cases h
    | tail _ h => cases h

lemma IssCompat_two_inv {xs ys : Is}
  (xs_ys : IssCompat [xs, ys]) :
  xs ∼ ys := by
  apply xs_ys xs ys
  · simp only [List.mem_cons, List.not_mem_nil, or_false, true_or]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]

lemma IssCompat_empty_any {xss : Iss} (compat : IssCompat xss) :
  IssCompat (empty :: xss) := by
  intro ys zs ys_in zs_in
  rcases List.mem_cons.mp ys_in with rfl | ys_in_tail
  · exact IsCompat_empty_any
  rcases List.mem_cons.mp zs_in with rfl | zs_in_tail
  · exact IsCompat_any_empty
  exact compat ys zs ys_in_tail zs_in_tail

lemma IssCompat_inv_cons (xs : Is) (xss : Iss)
  (compat : IssCompat (xs :: xss)) :
  IssCompat xss := by
  intro ys zs ys_in_xss zs_in_xss
  apply compat
  · apply List.mem_cons_of_mem xs ys_in_xss
  · apply List.mem_cons_of_mem xs zs_in_xss

def IssCompat_reduce (xs ys : Is) (xss : Iss)
  (compat : IssCompat (xs :: ys :: xss)) :
  IssCompat (xs :: xss) := by
  intro zs ws zs_in_xss ws_in_xss
  apply compat
  · grind only [= List.mem_cons]
  · grind only [= List.mem_cons]

end NamedShape
