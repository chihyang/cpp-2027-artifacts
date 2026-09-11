import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Einsum.NamedShape
import Einsum.ShapeOperations
import Einsum.ShapeProperties
import Einsum.NamedIndex
import Einsum.UnnamedIndex
import Einsum.TensorExpr
import Einsum.TensorDenotation
import Einsum.ExpandProperties

namespace TensorExamples
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex
open UnnamedIndex
open TensorExpr
open TensorDenotation
open ExpandProperties

abbrev Unique := NamedShape.Unique

def x : Is :=
  {
    pairs := [("x", 2)]
    noDup := by decide
  }

def y : Is :=
  {
    pairs := [("y", 3)]
    noDup := by decide
  }

def z : Is :=
  {
    pairs := [("z", 4)]
    noDup := by decide
  }

def xCompatY : x ∼ y := by
  intro i
  by_cases hx : i = "x"
  · rw [hx]
    unfold lookup x y
    simp only
    exact .vn 2
  · by_cases hy : i = "y"
    · rw [hy]
      unfold lookup x y
      simp only
      exact .nv 3
    · unfold lookup x y
      simp only
      unfold lookupPairs
      simp only [List.find?_singleton, beq_iff_eq, Option.map_if]
      simp only [if_neg (Ne.symm hx), if_neg (Ne.symm hy)]
      exact .nn

def xCompatZ : x ∼ z := by
  intro i
  by_cases hx : i = "x"
  · rw [hx]
    unfold lookup x z
    simp only
    exact .vn 2
  · by_cases hy : i = "z"
    · rw [hy]
      unfold lookup x z
      simp only
      exact .nv 4
    · unfold lookup x z
      simp only
      unfold lookupPairs
      simp only [List.find?_singleton, beq_iff_eq, Option.map_if]
      simp only [if_neg (Ne.symm hx), if_neg (Ne.symm hy)]
      exact .nn

def yCompatZ : y ∼ z := by
  intro i
  by_cases hx : i = "y"
  · rw [hx]
    unfold lookup y z
    simp only
    exact .vn 3
  · by_cases hy : i = "z"
    · rw [hy]
      unfold lookup y z
      simp only
      exact .nv 4
    · unfold lookup y z
      simp only
      unfold lookupPairs
      simp only [List.find?_singleton, beq_iff_eq, Option.map_if]
      simp only [if_neg (Ne.symm hx), if_neg (Ne.symm hy)]
      exact .nn

def xy : Is := unionIs x y xCompatY

private theorem unionIs_left_some {Γ Δ : Is}
  {hCompat : Γ ∼ Δ} {i : Id} {up : UpperBound}
  (h : lookup Γ i = some up) :
    lookup (unionIs Γ Δ hCompat) i = some up := by
  rw [lookup_unionIs_eq]
  simp only [h]
  apply joinVal_some_left

private theorem unionIs_none_of_none_none {Γ Δ : Is} {hCompat : Γ ∼ Δ} {i : Id}
    (hΓ : lookup Γ i = none) (hΔ : lookup Δ i = none) :
    lookup (unionIs Γ Δ hCompat) i = none := by
  rw [lookup_unionIs_eq]
  simp only [hΓ, hΔ]
  apply joinVal_none_left

def xyCompatZ : xy ∼ z := by
  unfold xy
  apply IsCompat_symm
  apply unionIs_part_full
  · exact IsCompat_symm xCompatZ
  · exact IsCompat_symm yCompatZ

def xyz : Is := unionIs xy z xyCompatZ

def xSubXY : x ⊑ xy := by
  intro i up h
  exact unionIs_left_some (hCompat := xCompatY) h

def xySubXYZ : xy ⊑ xyz := by
  intro i up h
  exact unionIs_left_some (hCompat := xyCompatZ) h

def xSubXYZ : x ⊑ xyz := IsSubset_trans xSubXY xySubXYZ

def xToVec : Index x → ℕ
  | ⟨idx⟩ =>
    let h : lookup x "x" = some 2 := by
      unfold lookup x
      simp only
      unfold lookupPairs
      simp only [List.find?_singleton, beq_iff_eq, Option.map_if]
      simp only [↓reduceIte]
    if idx h = 0 then 3 else 7

def ctx : Context := .nil

def env : Env (S := ℕ) ctx := .unit

def wt37 : TExpr (S := ℕ) ctx x := .const x xToVec

def wtExpandedXY : TExpr (S := ℕ) ctx xy :=
  .expand wt37 xSubXY

def wtExpandedXYZ : TExpr (S := ℕ) ctx xyz :=
  .expand wtExpandedXY xySubXYZ

def wtExpandedDirect : TExpr (S := ℕ) ctx xyz :=
  .expand wt37 xSubXYZ

example (idx : Index xyz) :
  denote wtExpandedXYZ env idx = denote wtExpandedDirect env idx := by
  unfold wtExpandedXYZ wtExpandedDirect
  exact expand_fuse wt37 xSubXY xySubXYZ env idx

def wtsEmpty : TExprSeq (S := ℂ) ctx [] :=
  TExprSeq.nil (S := ℂ) (Γ := ctx)

def einsumEmpty : TExpr (S := ℂ) ctx empty :=
  TExpr.einsum (xss := []) (zs := empty)
    wtsEmpty
    IssCompat_empty
    (by
      unfold unionIss unionIssAcc
      apply IsSubset_refl)

def denoteEinsumEmpty : denote einsumEmpty env Index.empty = 1 := by
  simp only [einsumEmpty, denote, unionIss, unionIssAcc, minusIs, sum, wtsEmpty, denotes]
  simp_all only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_eq_one]
  rfl

end TensorExamples
