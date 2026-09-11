import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Einsum.NamedShape
import Einsum.ShapeOperations
import Einsum.ShapeProperties

namespace NamedIndex
open NamedShape
open ShapeOperations
open ShapeProperties

abbrev Unique := NamedShape.Unique

structure NIndex (xs : Is) where
  get : ∀ {x : Id} {v : UpperBound}, lookup xs x = some v → Fin v

def NIndex.empty : NIndex empty := by
  apply NIndex.mk
  intro x v h
  contradiction

def NIndex.singleton (dim : Dim) (v : Fin dim.2) :
  NIndex (fromSingleton dim) := by
  apply NIndex.mk
  intro x w h
  have h' := lookupPairs_head dim.1 dim.2 []
  unfold fromSingleton fromList lookup at h
  simp only [Prod.mk.eta] at h
  simp only [Prod.mk.eta] at h'
  by_cases h'' : x = dim.1
  · rw [h''] at h
    subst h''
    simp_all only [Option.some.injEq]
    subst h
    obtain ⟨fst, snd⟩ := dim
    simp_all only
    exact v
  · rw [lookupPairs_tail] at h
    · contradiction
    · intro dim_eq_x
      exact h'' dim_eq_x.symm

def NIndex.Compat {xs : Is} (idx₁ idx₂ : NIndex xs) : Prop :=
  ∀ {x : Id} {v : UpperBound} (hx : lookup xs x = some v),
    idx₁.get hx = idx₂.get hx

notation xs " ≈ᵢ " ys => NIndex.Compat xs ys

theorem NIndex.ext {xs : Is} {idx₁ idx₂ : NIndex xs}
  (h : idx₁ ≈ᵢ idx₂) :
  idx₁ = idx₂ := by
  cases idx₁
  cases idx₂
  simp only [mk.injEq]
  funext x
  funext v
  funext hx
  exact h hx

def NIndex.subst_cast {xs ys : Is} (idx : NIndex ys)
  (xs_ys : xs ⊑ ys) : NIndex xs :=
  { get := by
      intro x v h
      exact (idx.get (xs_ys x v h))
  }

notation idx " ↓ᵢ " xs_ys => NIndex.subst_cast idx xs_ys

def NIndex.eq_cast {xs ys : Is}
  (idx : NIndex xs) (xs_ys : xs ≈ ys) : NIndex ys :=
  { get := by
      intro x v h
      exact idx.get (by
        rw [xs_ys x]
        exact h)
  }

notation idx " →ᵢ " xs_ys => NIndex.eq_cast idx xs_ys

def NIndex.HeterEquiv {xs ys : Is} (xs_ys : xs ≈ ys)
  (idx₁ : NIndex xs) (idx₂ : NIndex ys) : Prop :=
  (idx₁ →ᵢ xs_ys) ≈ᵢ idx₂

notation:50 idx₁ " ≈ᵢ[" hxy "] " idx₂ =>
  NIndex.HeterEquiv hxy idx₁ idx₂

theorem NIndex.heter_refl {xs : Is} {idx₁ idx₂ : NIndex xs}
  (heq : idx₁ ≈ᵢ idx₂) :
  idx₁ ≈ᵢ[IsRelEquiv.refl xs] idx₂ := by
  unfold NIndex.HeterEquiv
  intro i v h
  unfold NIndex.eq_cast
  exact heq h

theorem NIndex.subst_cast_heter {xs ys zs : Is}
  (idx : NIndex zs)
  (hxy : xs ≈ ys)
  (hxz : xs ⊑ zs) (hyz : ys ⊑ zs) :
  (idx ↓ᵢ hxz) ≈ᵢ[hxy] (idx ↓ᵢ hyz) := by
  unfold NIndex.HeterEquiv
  intro i v h
  unfold NIndex.eq_cast NIndex.subst_cast
  exact congrArg (fun p => idx.get p) (Subsingleton.elim _ _)

theorem NIndex.compat_cast_heter {xs ys zs : Is}
  (idx : NIndex xs)
  (hxy : ys ≈ zs)
  (hxz : xs ≈ ys) (hxz' : xs ≈ zs) :
  (idx →ᵢ hxz) ≈ᵢ[hxy] (idx →ᵢ hxz') := by
  unfold NIndex.HeterEquiv
  intro i v h
  unfold NIndex.eq_cast
  exact congrArg (fun p => idx.get p) (Subsingleton.elim _ _)

theorem NIndex.compat_cast_left_equiv {xs ys zs : Is}
  {idx₁ : NIndex xs} {idx₂ : NIndex ys}
  (hxy : xs ≈ ys)
  (heq : idx₁ ≈ᵢ[hxy] idx₂)
  (hxz : xs ≈ zs) (hzy : zs ≈ ys) :
  (idx₁ →ᵢ hxz) ≈ᵢ[hzy] idx₂ := by
  unfold NIndex.HeterEquiv
  intro i v h
  unfold NIndex.eq_cast
  unfold NIndex.HeterEquiv at heq
  unfold NIndex.eq_cast at heq
  exact heq h

theorem NIndex.compat_cong {xs ys : Is} {idx₁ idx₂ : NIndex xs}
  (heq : idx₁ ≈ᵢ idx₂)
  (hxy : xs ≈ ys) :
  (idx₁ →ᵢ hxy) ≈ᵢ (idx₂ →ᵢ hxy) := by
  intro x v h
  unfold NIndex.eq_cast
  exact heq (by
    rw [hxy x]
    exact h)

theorem NIndex.compat_cast_equiv {xs ys zs : Is}
  {idx₁ : NIndex xs} {idx₂ : NIndex ys}
  (hxy : xs ≈ ys)
  (heq : idx₁ ≈ᵢ[hxy] idx₂)
  (hzx : xs ≈ zs) (hzy : ys ≈ zs) :
  (idx₁ →ᵢ hzx) ≈ᵢ (idx₂ →ᵢ hzy) := by
  intro i v h
  unfold NIndex.eq_cast
  unfold NIndex.HeterEquiv at heq
  unfold NIndex.eq_cast at heq
  exact heq (by
    rw [hzy i]
    exact h)

theorem NIndex.subst_cast_equiv {xs ys zs : Is}
  {idx₁ : NIndex xs} {idx₂ : NIndex ys}
  (hxy : xs ≈ ys)
  (heq : idx₁ ≈ᵢ[hxy] idx₂)
  (hzx : zs ⊑ xs) (hzy : zs ⊑ ys) :
  (idx₁ ↓ᵢ hzx) ≈ᵢ (idx₂ ↓ᵢ hzy) := by
  intro i v h
  unfold NIndex.subst_cast
  unfold NIndex.HeterEquiv at heq
  unfold NIndex.eq_cast at heq
  exact heq (hzy i v h)

theorem NIndex.subst_cast_assoc {xs ys zs : Is}
  (idx : NIndex zs) (hxy : xs ⊑ ys) (hyz : ys ⊑ zs) :
  ((idx ↓ᵢ hyz) ↓ᵢ hxy) ≈ᵢ (idx ↓ᵢ (IsSubset_trans hxy hyz)) := by
  intro x v h
  unfold subst_cast
  simp only

lemma NIndex.subst_cast_irrl {xs ys : Is}
  (hxy₁ hxy₂ : xs ⊑ ys)
  (idx : NIndex ys) :
  (idx ↓ᵢ hxy₁) ≈ᵢ (idx ↓ᵢ hxy₂) := by
  intro x v h
  unfold NIndex.subst_cast
  exact congrArg (fun p => idx.get p) (Subsingleton.elim (hxy₁ x v h) (hxy₂ x v h))

lemma NIndex.eq_subst_cast {xs ys zs : Is}
  (idx : NIndex ys)
  (ys_zs : ys ≈ zs)
  (xs_ys : xs ⊑ ys)
  (xs_zs : xs ⊑ zs) :
  ((idx →ᵢ ys_zs) ↓ᵢ xs_zs) ≈ᵢ (idx ↓ᵢ xs_ys) := by
  intro i v h
  unfold NIndex.eq_cast NIndex.subst_cast
  exact congrArg (fun p => idx.get p) (Subsingleton.elim _ _)

def NIndex.cons {x : Id} {d : UpperBound} {xs : List Dim}
  {neq : Unique ((x, d) :: xs)}
  (i : Fin d)
  (idx : NIndex (fromList xs (Unique_cons neq))) :
  NIndex (fromList ((x, d) :: xs) neq) := by
  constructor
  intro y v h
  by_cases hy : y = x
  · rw [hy] at h
    unfold lookup fromList at h
    rw [lookupPairs_head] at h
    subst hy
    simp_all only [Option.some.injEq]
    subst h
    exact i
  · unfold lookup fromList at h
    rw [lookupPairs_tail] at h
    · exact idx.get h
    · simp only [ne_eq]
      grind only

def NIndex.head {x : Id} {d : UpperBound} {xs : List Dim}
  {neq : Unique ((x, d) :: xs)}
  (idx : NIndex (fromList ((x, d) :: xs) neq)) : Fin d := by
  apply @idx.get x d
  unfold fromList
  apply lookupPairs_head

def NIndex.tail {x : Id} {up : UpperBound} {xs : List Dim}
  (neq : Unique ((x , up) :: xs))
  (idx : NIndex (fromList ((x , up) :: xs) neq)) :
  NIndex (fromList xs (Unique_cons neq)) := by
  constructor
  intro y v h
  if h' : x = y then
    subst h'
    have hN : lookup (fromList xs (Unique_cons neq)) x = none := by
      apply lookupPairs_not_mem_none
      apply Unique_head_not_in_tail
      exact neq
    simp_all only [reduceCtorEq]
  else
    apply @idx.get y
    unfold fromList
    unfold lookup
    simp only
    rw [lookupPairs_tail]
    · exact h
    · simp only [ne_eq]
      exact h'

def NIndex.union {xs ys : Is}
  (xs_ys : xs ⊥ ys) (idx₁ : NIndex xs) (idx₂ : NIndex ys) :
  (NIndex (unionIs xs ys (disjointIs_compat xs_ys))) := by
  constructor
  intro x v h
  have h' : (lookup xs x = some v) ∨ (lookup ys x = some v) := by
    apply lookup_unionIs_some
    exact h
  by_cases hxs : lookup xs x = some v
  · exact idx₁.get hxs
  · by_cases hys : lookup ys x = some v
    · exact idx₂.get hys
    · simp_all only [or_self]

theorem NIndex.union_equiv {xs ys zs ws : Is}
  {idx₁ : NIndex xs} {idx₂ : NIndex ys}
  {idx₃ : NIndex zs} {idx₄ : NIndex ws}
  (xs_ys : xs ≈ ys) (zs_ws : zs ≈ ws)
  (idx₁_idx₂ : idx₁ ≈ᵢ[xs_ys] idx₂)
  (idx₃_idx₄ : idx₃ ≈ᵢ[zs_ws] idx₄)
  (xs_zs : xs ⊥ zs) (ys_ws : ys ⊥ ws) :
  NIndex.union xs_zs idx₁ idx₃
    ≈ᵢ[unionIs_equiv xs_ys zs_ws
      (disjointIs_compat xs_zs)
      (disjointIs_compat ys_ws)]
  NIndex.union ys_ws idx₂ idx₄ := by
  unfold NIndex.HeterEquiv
  intro i v h
  unfold NIndex.eq_cast NIndex.union
  simp only
  rw [lookup_unionIs_eq] at h
  rcases joinVal_some_inv (disjointIs_compat ys_ws i) h with hys | hws
  · have hxs : lookup xs i = some v := by
      rw [xs_ys i]
      exact hys
    unfold NIndex.HeterEquiv NIndex.eq_cast at idx₁_idx₂
    simp only [hxs, hys, ↓reduceDIte]
    exact idx₁_idx₂ hys
  · have hzs : lookup zs i = some v := by
      rw [zs_ws i]
      exact hws
    have hxs : lookup xs i = none := by
      simpa [hzs] using xs_zs i
    have hys : lookup ys i = none := by
      simpa [hws] using ys_ws i
    unfold NIndex.HeterEquiv NIndex.eq_cast at idx₃_idx₄
    simp only [hxs, hys, hzs, hws, reduceCtorEq, ↓reduceDIte]
    exact idx₃_idx₄ hws

def NIndex.union' {xs ys : Is}
  (xs_ys : xs ⊥ ys) (idx : NIndex xs × NIndex ys) :
  (NIndex (unionIs xs ys (disjointIs_compat xs_ys))) :=
  NIndex.union xs_ys idx.1 idx.2

def NIndex.split {xs ys : Is}
  (xs_ys : xs ⊥ ys)
  (idx : NIndex (unionIs xs ys (disjointIs_compat xs_ys))) :
  (NIndex xs) × (NIndex ys) := by
  have x_y_xy := unionIs_subset (disjointIs_compat xs_ys)
  have x_xy := x_y_xy.1
  have y_xy := x_y_xy.2
  constructor
  · constructor
    intro x v h
    exact (idx.get (x_xy x v h))
  · constructor
    intro x v h
    exact (idx.get (y_xy x v h))

lemma NIndex.split_union {xs ys : Is}
  (xs_ys : xs ⊥ ys)
  (idx : NIndex xs × NIndex ys) :
  NIndex.split xs_ys (NIndex.union xs_ys idx.1 idx.2) = idx := by
  apply Prod.ext
  · apply NIndex.ext
    intro x v h
    unfold NIndex.split NIndex.union
    simp only
    simp_all only [↓reduceDIte]
  · apply NIndex.ext
    intro x v h
    unfold NIndex.split NIndex.union
    simp only
    have hxs : lookup xs x = none :=
      by simpa [h] using xs_ys x
    simp_all only [reduceCtorEq, ↓reduceDIte]

lemma NIndex.union_split {xs ys : Is}
  (xs_ys : xs ⊥ ys)
  (idx : NIndex (unionIs xs ys (disjointIs_compat xs_ys))) :
  NIndex.union' xs_ys (NIndex.split xs_ys idx) = idx := by
  apply NIndex.ext
  intro x v h
  unfold union' union
  simp only
  rw [lookup_unionIs_eq] at h
  rcases joinVal_some_inv (disjointIs_compat xs_ys x) h with hxs | hys
  · simp only [hxs, ↓reduceDIte]
    unfold NIndex.split
    simp only
  · have hxs : lookup xs x = none :=
      by simpa [hys] using xs_ys x
    simp only [hxs, reduceCtorEq, ↓reduceDIte, hys]
    unfold NIndex.split
    simp only

def NIndex.union_disjoint {xs ys : Is} (xs_ys : xs ⊥ ys) :
  (NIndex (unionIs xs ys (disjointIs_compat xs_ys))) ≃
  (NIndex xs × NIndex ys) := by
  constructor
  · apply NIndex.union_split xs_ys
  · apply NIndex.split_union xs_ys

lemma NIndex.head_cons {xs : List Dim} {x : Id} {d : UpperBound}
  {neq : Unique ((x, d) :: xs)}
  (i : Fin d)
  (idx : NIndex (fromList xs (Unique_cons neq))) :
  NIndex.head (NIndex.cons (neq := neq) i idx) = i := by
  unfold NIndex.head NIndex.cons
  simp only [↓reduceDIte]

lemma NIndex.tail_cons {xs : List Dim} {x : Id} {d : UpperBound}
  {neq : Unique ((x, d) :: xs)}
  (i : Fin d)
  (idx : NIndex (fromList xs (Unique_cons neq))) :
  NIndex.tail neq (NIndex.cons (neq := neq) i idx) = idx := by
  apply NIndex.ext
  intro y v h
  unfold NIndex.tail NIndex.cons
  by_cases hxy : x = y
  · subst hxy
    have hN : lookup (fromList xs (Unique_cons neq)) x = none := by
      apply lookupPairs_not_mem_none
      apply Unique_head_not_in_tail
      exact neq
    simp_all only [reduceCtorEq]
  · simp only [hxy]
    have hyx : ¬ y = x := fun h => hxy h.symm
    simp only [↓reduceDIte, hyx]

lemma NIndex.cons_head_tail {xs : List Dim} {x : Id} {d : UpperBound}
  {neq : Unique ((x, d) :: xs)}
  (idx : NIndex (fromList ((x, d) :: xs) neq)) :
  NIndex.cons (NIndex.head idx) (NIndex.tail neq idx) = idx := by
  apply NIndex.ext
  intro y v h
  unfold NIndex.cons
  by_cases hyx : y = x
  · subst hyx
    unfold fromList lookup at h
    rw [lookupPairs_head] at h
    have hv : d = v := Option.some.inj h
    subst hv
    unfold NIndex.head
    simp only [↓reduceDIte]
  · simp only [hyx]
    have hxy : ¬ x = y := fun h => hyx h.symm
    unfold NIndex.tail
    simp only [hxy]
    exact congrArg (fun p => idx.get p) (Subsingleton.elim _ _)

def NIndex.headTailEquiv {xs : List Dim} {x : Id} {d : UpperBound}
  (neq : Unique ((x, d) :: xs)) :
  NIndex (fromList ((x, d) :: xs) neq) ≃
  Fin d × NIndex (fromList xs (Unique_cons neq)) where
  toFun := fun idx => (NIndex.head idx, NIndex.tail neq idx)
  invFun := fun idx => NIndex.cons idx.1 idx.2
  left_inv := NIndex.cons_head_tail
  right_inv := by
    intro idx
    rcases idx with ⟨i, idx⟩
    apply Prod.ext
    · exact NIndex.head_cons (neq := neq) i idx
    · exact NIndex.tail_cons (neq := neq) i idx

instance NIndex.nil (neq : Unique []) :
  Subsingleton (NIndex (fromList [] neq)) := by
  constructor
  intro idx₁ idx₂
  apply NIndex.ext
  intro y v h
  unfold lookup at h
  unfold fromList at h
  simp only [lookupPairs_empty_none, reduceCtorEq] at h

def NIndex.fintypeFromList (xs : List Dim) (neq : Unique xs) :
  Fintype (NIndex (fromList xs neq)) :=
  match xs, neq with
  | [], neq => Fintype.ofSubsingleton NIndex.empty
  | (x, d) :: xs, neq => by
    let tailType := NIndex (fromList xs (Unique_cons neq))
    let tailFintype : Fintype tailType :=
      NIndex.fintypeFromList xs (Unique_cons neq)
    let productFintype : Fintype (Fin d × tailType) := by
      apply instFintypeProd
    apply Fintype.ofEquiv (Fin d × tailType)
    apply (NIndex.headTailEquiv neq).symm

instance NIndex.fintype (xs : Is) : Fintype (NIndex xs) :=
  NIndex.fintypeFromList xs.pairs xs.noDup

def NIndex.eqEquiv {xs ys : Is} (hxy : xs ≈ ys) :
  NIndex xs ≃ NIndex ys where
  toFun := fun idx => idx →ᵢ hxy
  invFun := fun idx => idx →ᵢ IsRelEquiv.symm hxy
  left_inv := by
    intro idx
    simp only
    apply NIndex.ext
    intro x v h
    unfold NIndex.eq_cast
    simp only
  right_inv := by
    intro idx
    simp only
    apply NIndex.ext
    intro x v h
    unfold NIndex.eq_cast
    simp only

end NamedIndex
