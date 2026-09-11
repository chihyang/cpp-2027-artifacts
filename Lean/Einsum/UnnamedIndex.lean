import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Defs
import Einsum.NamedShape
import Einsum.ShapeOperations
import Einsum.ShapeProperties
import Einsum.NamedIndex

namespace UnnamedIndex
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex

abbrev Unique := NamedShape.Unique

def UIndex (dims : List UpperBound) : Type :=
  match dims with
  | [] => Unit
  | d :: ds => Fin d × UIndex ds

instance UIndex.singleton :
  Subsingleton (UIndex []) := by
  constructor
  intro idx₁ idx₂
  cases idx₁
  cases idx₂
  rfl

instance UIndex.fintype (dims : List UpperBound) :
  Fintype (UIndex dims) := by
  induction dims with
  | nil =>
    apply Fintype.ofSubsingleton
    exact .unit
  | cons d ds ih =>
    unfold UIndex
    apply instFintypeProd

def NIndex.toUnnamed (xs : List Dim) (neq : Unique xs)
  (idx : NIndex (fromList xs neq)) :
  UIndex (xs.map Prod.snd) :=
  match xs with
  | [] => .unit
  | (x, d) :: xs' => by
    unfold UIndex
    simp only [List.map_cons]
    apply Prod.mk
    · apply @idx.get x d
      unfold fromList
      apply lookupPairs_head
    · apply NIndex.toUnnamed xs'
      apply NIndex.tail neq idx

def NIndex.fromUnnamed (xs : List Dim) (neq : Unique xs) :
  UIndex (xs.map Prod.snd) → NIndex (fromList xs neq) :=
  fun idx =>
  match xs with
  | [] =>
    { get := by
        intro x v h
        contradiction }
  | (x, d) :: xs' =>
    match idx with
    | (i , is) =>
      NIndex.cons (neq := neq) i
        (NIndex.fromUnnamed xs' (Unique_cons neq) is)

end UnnamedIndex
