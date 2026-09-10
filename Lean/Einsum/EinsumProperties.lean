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
import Einsum.UnnamedIndex
import Einsum.TensorExpr
import Einsum.TensorDenotation

namespace EinsumProperties
open NamedShape
open ShapeOperations
open ShapeProperties
open NamedIndex
open UnnamedIndex
open TensorExpr
open TensorDenotation

abbrev Unique := NamedShape.Unique

lemma expand_reduce {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys : Is}
  (wt : TExpr Γ xs)
  (xs_ys : xs ⊑ ys)
  (env : Env (S := S) Γ)
  (idx : Index ys) :
  denote (.expand wt xs_ys) env idx
    =
  denote wt env (by exact idx.subst_cast xs_ys) := by
  rfl

lemma minusIs_reduce_compat {xs ys zs ws : Is}
  (xs_ys : xs ∼ ys)
  (xs_zs : xs ∼ zs)
  (ys_zs : ys ∼ zs)
  (xs_zs_compat : IssCompat [xs, zs])
  (xys_zs : unionIs xs ys xs_ys ∼ zs)
  (ws_xyzs : ws ⊑ unionIss (IssCompat_two xys_zs)) :
  (ws ∖ (ys ∖ zs)) ⊑ unionIss xs_zs_compat := by
  have ws_subset' : (ws ∖ (ys ∖ zs)) ⊑ ws := by
    apply minusIs_subset
  intro i up h
  simp only [lookup_minusIs_eq] at h
  rw [unionIss_two_eq, lookup_unionIs_eq]
  · have h' := minusVal_some_inv h
    have hEq := ws_xyzs i up h'.1
    rw [unionIss_two_eq xys_zs, lookup_unionIs_eq] at hEq
    have hEq' :=
      joinVal_some_inv (v₂ := lookup zs i) (u := up)
        (xys_zs i) hEq
    rcases hEq' with hL | hR
    · rw [lookup_unionIs_eq] at hL
      rcases joinVal_some_inv (xs_ys i) hL with hL' | hR'
      · simp only [hL']
        apply joinVal_some_left
      · have hyz := h'.2
        rw [hR'] at hyz
        suffices hzs : lookup zs i = some up by
          simp only [hzs]
          apply joinVal_some_right
        rcases CompatVal_some_or hR' (ys_zs i) with hyzL | hyzR
        · exact hyzL
        · simp_all only [reduceCtorEq]
    · simp only [hR]
      apply joinVal_some_right
  · exact xs_zs

structure ShapeRelPack (xs ys zs ws : Is) : Prop where
  xy : xs ∼ ys
  xz : xs ∼ zs
  yz : ys ∼ zs
  xw : xs ∼ ws
  yw : ys ∼ ws
  zw : zs ∼ ws
  x_xy : xs ⊑ unionIs xs ys xy
  y_xy : ys ⊑ unionIs xs ys xy
  xzs : IssCompat [xs, zs]
  xy_z : IssCompat [unionIs xs ys xy, zs]
  wyz_xz : (ws ∖ (ys ∖ zs)) ⊑ unionIss xzs

def xyzw_Relations {xs ys zs ws : Is}
  (xs_ys_disj : xs ⊥ ys)
  (xys_zs : unionIs xs ys (disjointIs_compat xs_ys_disj) ∼ zs)
  (ws_xyzs : ws ⊑ unionIss (IssCompat_two xys_zs)) :
  ShapeRelPack xs ys zs ws := by
  have xy := disjointIs_compat xs_ys_disj
  let xys := unionIs xs ys xy
  have xy_subset := unionIs_subset xy
  have x_xy := xy_subset.1
  have y_xy := xy_subset.2
  have xyz_compat : IssCompat [xys, zs] := by
    exact IssCompat_two xys_zs
  have yz := IsSubset_compat_trans y_xy xys_zs
  have xz := IsSubset_compat_trans x_xy xys_zs
  apply ShapeRelPack.mk
  · exact xz
  · exact yz
  · apply IsSubset_compat_trans
    · exact x_xy
    · apply unionIss_subset_compat_part xyz_compat ws_xyzs
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      simp_all only [true_or, xys]
  · apply IsSubset_compat_trans
    · exact y_xy
    · apply unionIss_subset_compat_part xyz_compat ws_xyzs
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      simp_all only [true_or, xys]
  · apply unionIss_subset_compat_part xyz_compat ws_xyzs
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, or_true, xys]
  · exact x_xy
  · exact y_xy
  · exact xyz_compat
  · apply minusIs_reduce_compat xy xz yz
    · exact ws_xyzs
    · exact xys_zs
  · exact IssCompat_two xz

lemma sum_free_fs_empty {xs ys zs ws : Is}
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (w_xyz : ws ≈ unionIss xyzw_rels.xy_z) :
  (ys ∖ unionIs zs ws xyzw_rels.zw) ≈ empty := by
  intro i
  simp only [lookup_minusIs_eq, lookup_unionIs_eq]
  simp only [lookup_empty_none]
  rw [unionIss_two_eq'] at w_xyz
  have hEq := w_xyz i
  simp only [lookup_unionIs_eq] at hEq
  simp only [hEq]
  rw [joinVal_comm']
  simp only [joinVal_comm' (lookup xs i) (lookup ys i)]
  rw [joinVal_self_right_twice]
  rw [joinVal_assoc]
  · rw [minusVal_joinVal_self_left]
  · exact xyzw_rels.xz i
  · exact xyzw_rels.yz i

lemma sum_free_us_xzs {xs ys zs ws : Is}
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (xs_ys_disj : xs ⊥ ys)
  (w_xyz : ws ≈ unionIss xyzw_rels.xy_z) :
  (ws ∖ (ys ∖ zs)) ≈ unionIss xyzw_rels.xzs := by
  intro i
  rw [unionIss_two_eq']
  simp only [lookup_minusIs_eq, lookup_unionIs_eq]
  simp only [unionIss_two_eq'] at w_xyz
  have hEq := w_xyz i
  simp only [lookup_unionIs_eq] at hEq
  rw [hEq]
  have hxy := xs_ys_disj i
  rcases hxy with hL | hR
  · simp only [hL]
    simp only [joinVal_none_left]
    apply joinVal_minusVal_eq_right
  · simp only [hR]
    simp only [joinVal_none_right]
    simp only [minusVal_none_left]
    simp only [minusVal_none_right]

def EinsumExpandCommEq {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys zs ws : Is}
  (wt₁ : TExpr (S := S) Γ xs)
  (wt₂ : TExpr (S := S) Γ zs)
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (xys_zs : unionIs xs ys xyzw_rels.xy ∼ zs)
  (ws_xyzs : ws ⊑ unionIss (IssCompat_two xys_zs))
  (env : Env (S := S) Γ)
  (idx : Index ws) : Prop :=
  let xys := unionIs xs ys xyzw_rels.xy
  let fs := ys ∖ (unionIs zs ws xyzw_rels.zw)
  let us := ws ∖ (ys ∖ zs)
  have us_ws : us ⊑ ws := by
    exact minusIs_subset
  let F : Nat := fs.prod
  denote
    (.einsum ⟦.expand wt₁ xyzw_rels.x_xy, wt₂⟧ xyzw_rels.xy_z ws_xyzs)
    env idx
    =
  denote
    (.expand (.scale F (.einsum ⟦wt₁, wt₂⟧ xyzw_rels.xzs xyzw_rels.wyz_xz)) us_ws)
    env idx

lemma IsCompat_shrink {xs ys zs ws : Is}
  (xs_ys : xs ∼ ys) : (xs ∖ zs) ∼ (ys ∖ ws) := by
  have xz_ys : (xs ∖ zs) ∼ ys := by
    apply IsSubset_compat_trans minusIs_subset xs_ys
  have yw_xz : (ys ∖ ws) ∼ (xs ∖ zs) := by
    apply IsSubset_compat_trans minusIs_subset
    exact (IsCompat_symm xz_ys)
  exact IsCompat_symm yw_xz

lemma abcd_join_disjoint {a b c d : Option UpperBound}
  (ab : a = none ∨ b = none)
  (ac : a ∼ᵢ c) (bc : b ∼ᵢ c)
  (ad : a ∼ᵢ d) (bd : b ∼ᵢ d) (cd : c ∼ᵢ d) :
  b ∖ᵢ joinVal c d cd = none ∨
  joinVal a c ac ∖ᵢ (d ∖ᵢ (b ∖ᵢ c)) = none := by
  cases cd with
  | nn =>
    simp_all only [
      joinVal_none_right, minusVal_none_left,
      minusVal_none_right]
    apply Or.comm.mp
    exact ab
  | nv v =>
    apply Or.inl
    apply minusVal_some_right
  | vn v =>
    simp_all only [
      joinVal_none_right, joinVal_some_right,
      minusVal_some_right, minusVal_none_right]
    apply Or.inl
    simp only
  | vv v =>
    apply Or.inl
    apply minusVal_some_right

lemma abcd_join_eq {a b c d : Option UpperBound}
  (ab : a ∼ᵢ b) (ac : a ∼ᵢ c) (bc : b ∼ᵢ c)
  (ad : a ∼ᵢ d) (bd : b ∼ᵢ d) (cd : c ∼ᵢ d)
  (ab_disjoint : a = none ∨ b = none)
  (ab_c : (joinVal a b ab) ∼ᵢ c)
  (b_ac : (b ∖ᵢ joinVal c d cd) ∼ᵢ
    (joinVal a c ac ∖ᵢ (d ∖ᵢ (b ∖ᵢ c)))) :
  joinVal (joinVal a b ab) c ab_c ∖ᵢ d =
  joinVal (b ∖ᵢ joinVal c d cd) (joinVal a c ac ∖ᵢ (d ∖ᵢ (b ∖ᵢ c))) b_ac := by
  cases cd with
  | nn =>
    simp_all only [
      joinVal_none_right, minusVal_none_left,
      minusVal_none_right, joinVal_comm]
  | nv v =>
    rcases ab_disjoint with h1 | h2
    · simp_all only [
        joinVal_none_right, joinVal_some_right,
        minusVal_some_right, minusVal_none_left]
    · simp_all only [
        joinVal_none_left, joinVal_none_right,
        minusVal_some_right, minusVal_none_right]
  | vn v =>
    simp_all only [
      joinVal_none_right, joinVal_some_right,
      minusVal_none_left, minusVal_none_right]
  | vv v =>
    simp_all only [
      joinVal_some_right, minusVal_none_right,
      minusVal_some_right, joinVal_none_left]

lemma xyzw_split_disjoint {xs ys zs ws : Is}
  (xs_ys_disj : xs ⊥ ys)
  (xyzw_rels : ShapeRelPack xs ys zs ws) :
  let us : Is := ws ∖ (ys ∖ zs)
  let zws : Is := unionIs zs ws xyzw_rels.zw
  let xzs : Is := unionIss (IssCompat_two xyzw_rels.xz)
  (ys ∖ zws) ⊥ (xzs ∖ us) := by
    simp only
    intro x
    rw [unionIss_two_eq xyzw_rels.xz]
    simp only [lookup_minusIs_eq, lookup_unionIs_eq]
    apply abcd_join_disjoint
    · exact xs_ys_disj x
    · exact xyzw_rels.yz x
    · exact xyzw_rels.xw x
    · exact xyzw_rels.yw x

lemma xyzw_split_eq {xs ys zs ws : Is}
  (xs_ys_disj : xs ⊥ ys)
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (xys_zs : unionIs xs ys xyzw_rels.xy ∼ zs) :
  let xyz : Is := unionIs (unionIs xs ys xyzw_rels.xy) zs xys_zs
  let us : Is := ws ∖ (ys ∖ zs)
  let zws : Is := unionIs zs ws xyzw_rels.zw
  let xzs : Is := unionIss (IssCompat_two xyzw_rels.xz)
  have y_xz : ys ∼ xzs := by
    apply unionIs_part_full
    · exact IsCompat_symm xyzw_rels.xy
    · exact xyzw_rels.yz
    · exact xyzw_rels.xz
  have y_xs : (ys ∖ zws) ∼ (xzs ∖ us) := by
    apply IsCompat_shrink
    exact y_xz
  (xyz ∖ ws) ≈ (unionIs (ys ∖ zws) (xzs ∖ us) y_xs) := by
  simp only
  intro i
  simp_all only [lookup_unionIs_eq, lookup_minusIs_eq, unionIss_two_eq xyzw_rels.xz]
  apply abcd_join_eq
  · exact xyzw_rels.yz i
  · exact xyzw_rels.xw i
  · exact xyzw_rels.yw i
  · exact xs_ys_disj i

lemma Index.card_eq_prod_fromList
  (dims : List Dim) (neq : Unique dims) :
  Fintype.card (Index (fromList dims neq)) =
  (fromList dims neq).prod := by
  induction dims with
  | nil =>
    apply Fintype.card_ofSubsingleton
  | cons dim dims ih =>
    rcases dim with ⟨x, u⟩
    unfold Is.prod
    simp only
    unfold Is.prod at ih
    simp only at ih
    have h := ih (Unique_cons neq)
    simp_all only [implies_true]
    rw [Fintype.card_congr (Index.headTailEquiv neq)]
    rw [Fintype.card_prod, Fintype.card_fin]
    unfold List.map fromList
    simp only [List.prod_cons]
    unfold fromList at h
    simp only at h
    simp_all only

theorem Index.card_eq_prod {xs : Is} :
  Fintype.card (Index xs) = xs.prod := by
  exact Index.card_eq_prod_fromList xs.pairs xs.noDup

lemma xyzw_down_x_eq {xs ys zs ws : Is}
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (xs_ys_disj : xs ⊥ ys)
  (idx : Index ws)
  {idxy : Index (ys ∖ (unionIs zs ws xyzw_rels.zw))}
  {idxz : Index (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))}
  {yz_disjoint :
    (ys ∖ (unionIs zs ws xyzw_rels.zw)) ⊥
    (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))}
  {xyzw_eq :
    unionIs
      (ys ∖ (unionIs zs ws xyzw_rels.zw))
      (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))
      (disjointIs_compat yz_disjoint) ≈
    (unionIss xyzw_rels.xy_z ∖ ws)}
  {xs_xyzs : xs ⊑ unionIss xyzw_rels.xy_z}
  {wxyw_xyz : unionIs ws (unionIss xyzw_rels.xy_z ∖ ws)
    (disjointIs_compat minusIs_disjoint) ≈
    unionIss xyzw_rels.xy_z}
  {wyz_w : (ws ∖ (ys ∖ zs)) ⊑ ws}
  {wyz_xz :
    (ws ∖ ys ∖ zs) ⊥
    unionIss (IssCompat_two xyzw_rels.xz) ∖ ws ∖ ys ∖ zs}
  {xz_minus :
    (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs))) ≈
    (unionIss (IssCompat_two xyzw_rels.xz) ∖ (ws ∖ (ys ∖ zs)))}
  {xs_xz : xs ⊑ unionIss (IssCompat_two xyzw_rels.xz)}
  {wyz_xzwyz :
    unionIs (ws ∖ ys ∖ zs)
      (unionIss (IssCompat_two xyzw_rels.xz) ∖ ws ∖ ys ∖ zs)
      (disjointIs_compat wyz_xz) ≈
    unionIss (IssCompat_two xyzw_rels.xz)}:
  (((Index.union minusIs_disjoint idx
     ((Index.union yz_disjoint idxy idxz) →ᵢ xyzw_eq))
     →ᵢ
    wxyw_xyz)
   ↓ᵢ xs_xyzs) ≈ᵢ
  ((Index.union wyz_xz (idx ↓ᵢ wyz_w) (idxz →ᵢ xz_minus))
    →ᵢ
    wyz_xzwyz)
   ↓ᵢ xs_xz := by
  intro x v h
  have hys : lookup ys x = none := by
    rcases xs_ys_disj x with hxs | hys
    · rw [h] at hxs
      contradiction
    · exact hys
  unfold Index.get
  unfold Index.union
  simp only
  unfold Index.subst_cast
  unfold Index.eq_cast
  unfold Index.get
  rcases CompatVal_some_or h (xyzw_rels.xw x) with hL | hR
  · simp only [hL, ↓reduceDIte]
    simp only [lookup_minusIs_eq]
    simp only [hys]
    simp only [minusVal_none_left]
    simp only [minusVal_none_right]
    simp only [hL, ↓reduceDIte]
  · simp only [hR, reduceCtorEq, ↓reduceDIte]
    simp only [unionIss_two_eq' xyzw_rels.xy_z]
    simp only [lookup_minusIs_eq]
    simp only [hR]
    simp only [minusVal_none_right]
    simp only [lookup_unionIs_eq]
    simp only [h, hys]
    simp only [joinVal_some_left]
    simp only [↓reduceDIte]
    simp only [minusVal_none_left]
    simp only [reduceCtorEq, ↓reduceDIte]
    simp only [minusVal_none_right]
    rw [dif_pos True.intro]
    simp only [unionIss_two_eq xyzw_rels.xz]
    simp only [lookup_unionIs_eq]
    simp only [h]
    simp only [joinVal_some_left]
    rw [dif_pos True.intro]

lemma xyzw_down_z_eq {xs ys zs ws : Is}
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (idx : Index ws)
  {idxy : Index (ys ∖ (unionIs zs ws xyzw_rels.zw))}
  {idxz : Index (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))}
  {yz_disjoint :
    (ys ∖ (unionIs zs ws xyzw_rels.zw)) ⊥
    (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))}
  {xyzw_eq :
    unionIs
      (ys ∖ (unionIs zs ws xyzw_rels.zw))
      (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs)))
      (disjointIs_compat yz_disjoint) ≈
    (unionIss xyzw_rels.xy_z ∖ ws)}
  {zs_xyzs : zs ⊑ unionIss xyzw_rels.xy_z}
  {wxyw_xyz : unionIs ws (unionIss xyzw_rels.xy_z ∖ ws)
    (disjointIs_compat minusIs_disjoint) ≈
    unionIss xyzw_rels.xy_z}
  {wyz_w : (ws ∖ (ys ∖ zs)) ⊑ ws}
  {wyz_xz :
    (ws ∖ ys ∖ zs) ⊥
    unionIss (IssCompat_two xyzw_rels.xz) ∖ ws ∖ ys ∖ zs}
  {xz_minus :
    (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs))) ≈
    (unionIss (IssCompat_two xyzw_rels.xz) ∖ (ws ∖ (ys ∖ zs)))}
  {zs_xz : zs ⊑ unionIss (IssCompat_two xyzw_rels.xz)}
  {wyz_xzwyz :
    unionIs (ws ∖ ys ∖ zs)
      (unionIss (IssCompat_two xyzw_rels.xz) ∖ ws ∖ ys ∖ zs)
      (disjointIs_compat wyz_xz) ≈
    unionIss (IssCompat_two xyzw_rels.xz)}:
  (((Index.union minusIs_disjoint idx
     ((Index.union yz_disjoint idxy idxz) →ᵢ xyzw_eq))
     →ᵢ
    wxyw_xyz)
   ↓ᵢ zs_xyzs) ≈ᵢ
  ((Index.union wyz_xz (idx ↓ᵢ wyz_w) (idxz →ᵢ xz_minus))
    →ᵢ
    wyz_xzwyz)
   ↓ᵢ zs_xz := by
  intro x v h
  unfold Index.get
  unfold Index.union
  simp only
  unfold Index.subst_cast
  unfold Index.eq_cast
  unfold Index.get
  rcases CompatVal_some_or h (xyzw_rels.zw x) with hL | hR
  · simp only [hL, ↓reduceDIte]
    simp_all only [lookup_minusIs_eq]
    simp_all only [minusVal_some_right]
    simp_all only [minusVal_none_right]
    rw [dif_pos True.intro]
  · simp only [hR, reduceCtorEq, ↓reduceDIte]
    simp only [unionIss_two_eq' xyzw_rels.xy_z]
    simp only [lookup_minusIs_eq]
    simp only [hR]
    simp only [minusVal_none_right]
    simp only [lookup_unionIs_eq]
    simp only [h]
    simp only [joinVal_some_right]
    simp only [↓reduceDIte]
    simp only [joinVal_some_left]
    simp only [minusVal_some_right]
    simp only [reduceCtorEq, ↓reduceDIte]
    simp only [minusVal_none_right]
    rw [dif_pos True.intro]
    simp only [reduceCtorEq, ↓reduceDIte]
    simp only [unionIss_two_eq xyzw_rels.xz]
    simp only [lookup_unionIs_eq]
    simp only [h]
    simp only [joinVal_some_right]
    rw [dif_pos True.intro]

theorem einsum_expand_comm_two {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys zs ws : Is}
  (wt₁ : TExpr Γ xs)
  (wt₂ : TExpr Γ zs)
  (xs_ys_disj : xs ⊥ ys)
  (xy_z : unionIs xs ys (disjointIs_compat xs_ys_disj) ∼ zs)
  (w_xyz : ws ⊑ unionIss (IssCompat_two xy_z))
  (env : Env (S := S) Γ)
  (idx : Index ws) :
  have xyzw_rels := xyzw_Relations xs_ys_disj xy_z w_xyz
  EinsumExpandCommEq wt₁ wt₂ xyzw_rels xy_z w_xyz env idx := by
  simp only [EinsumExpandCommEq, denote, denotes]
  have xyzw_rels := xyzw_Relations xs_ys_disj xy_z w_xyz
  have xyzw_split := xyzw_split_eq xs_ys_disj xyzw_rels xy_z
  have xyzw_split_disj := xyzw_split_disjoint xs_ys_disj xyzw_rels
  have xz_union := unionIss_two_eq xyzw_rels.xz
  have xz_minus :
    (unionIs xs zs xyzw_rels.xz ∖ (ws ∖ (ys ∖ zs))) ≈
    (unionIss (IssCompat_two xyzw_rels.xz) ∖ (ws ∖ (ys ∖ zs))) := by
    intro i
    simp only [lookup_minusIs_eq, xz_union]
  /- Step 1: Prepare the condition -/
  simp only at xyzw_split
  simp only [xz_union] at xyzw_split xyzw_split_disj
  rw [← unionIss_two_eq xy_z] at xyzw_split
  /- Step 2 : rewrite the LHS to sum (us ∪ fs) f and split the LHS
     function into two -/
  rw [sum_disjoing_prod_type xyzw_split_disj (IsRelEquiv.symm xyzw_split)]
  rw [sum_comp xz_minus]
  unfold Function.comp
  simp_rw [denote_subst_cast_assoc]
  simp only [mul_one]
  /- Step 3: the outer argument in LHS doesn't matter -/
  have down_eq_xs := fun idxy idxz =>
    Index.ext (xyzw_down_x_eq xyzw_rels xs_ys_disj idx
      (idxy := idxy)
      (idxz := idxz)
      (yz_disjoint := xyzw_split_disj)
      (xyzw_eq := IsRelEquiv.symm xyzw_split)
      (xs_xyzs := IsSubset_trans xyzw_rels.x_xy
        (unionIss_compat_part xyzw_rels.xy_z List.mem_cons_self))
      (wxyw_xyz := minusIs_union_eq w_xyz)
      (wyz_w := minusIs_subset)
      (wyz_xz := minusIs_disjoint)
      (xz_minus := xz_minus)
      (xs_xz := unionIss_compat_part
        (IssCompat_two xyzw_rels.xz) List.mem_cons_self)
      (wyz_xzwyz := minusIs_union_eq xyzw_rels.wyz_xz))
  simp_rw [down_eq_xs]
  have down_eq_zs := fun idxy idxz =>
    Index.ext (xyzw_down_z_eq xyzw_rels idx
      (idxy := idxy)
      (idxz := idxz)
      (yz_disjoint := xyzw_split_disj)
      (xyzw_eq := IsRelEquiv.symm xyzw_split)
      (zs_xyzs := unionIss_compat_part xyzw_rels.xy_z
        (List.mem_cons_of_mem (unionIs xs ys xyzw_rels.xy)
          List.mem_cons_self))
      (wxyw_xyz := minusIs_union_eq w_xyz)
      (wyz_w := minusIs_subset)
      (wyz_xz := minusIs_disjoint)
      (xz_minus := xz_minus)
      (zs_xz := unionIss_compat_part
        (IssCompat_two xyzw_rels.xz)
        (List.mem_cons_of_mem xs List.mem_cons_self))
      (wyz_xzwyz := minusIs_union_eq xyzw_rels.wyz_xz))
  simp_rw [down_eq_zs]
  /- Step 4: rewrite RHS to Fintype.card -/
  rw [← Index.card_eq_prod]
  unfold sum
  rw [Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul]

def EinsumExpandSumFreeCommEq {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys zs ws : Is}
  (wt₁ : TExpr (S := S) Γ xs)
  (wt₂ : TExpr (S := S) Γ zs)
  (xyzw_rels : ShapeRelPack xs ys zs ws)
  (xys_zs : unionIs xs ys xyzw_rels.xy ∼ zs)
  (ws_xyzs : ws ≈ unionIss (IssCompat_two xys_zs))
  (env : Env (S := S) Γ)
  (idx : Index ws) : Prop :=
  let xzs := unionIss xyzw_rels.xzs
  have ws_xyzs_subset : ws ⊑ unionIss xyzw_rels.xy_z := by
    apply IsEq_subset
    exact ws_xyzs
  have xzs_xyzs : xzs ⊑ unionIss (IssCompat_two xys_zs) := by
    intro x v h
    unfold xzs at h
    rw [unionIss_two_eq (IssCompat_two_inv xyzw_rels.xzs)] at h
    rw [lookup_unionIs_eq] at h
    simp_all only [unionIss_two_eq]
    simp_all only [lookup_unionIs_eq]
    rcases joinVal_some_inv (xyzw_rels.xz x) h with hL | hR
    · simp only [hL]
      simp only [joinVal_some_left]
    · simp only [hR]
      simp only [joinVal_some_right]
  have xzs_ws : xzs ⊑ ws := by
    apply IsEq_subset_right ws_xyzs
    exact xzs_xyzs
  denote
    (.einsum ⟦.expand wt₁ xyzw_rels.x_xy, wt₂⟧ xyzw_rels.xy_z ws_xyzs_subset)
    env idx
    =
  denote
    (.expand (.einsum ⟦wt₁, wt₂⟧ xyzw_rels.xzs IsSubset_refl) xzs_ws)
    env idx

theorem scale_one {S : Type} [Semiring S]
  {Γ : Context}
  {xs : Is}
  (wt₁ : TExpr Γ xs)
  (env : Env (S := S) Γ)
  (idx : Index xs) :
  denote (.scale 1 wt₁) env idx =
  denote wt₁ env idx := by
  simp only [denote]
  simp only [Nat.cast_one, one_mul]

theorem scale_expand_comm {S : Type} [Semiring S]
  {Γ : Context}
  {xs zs : Is} {n : ℕ}
  (xs_zs : xs ⊑ zs)
  (wt₁ : TExpr Γ xs)
  (env : Env (S := S) Γ)
  (idx : Index zs) :
  denote (.expand (.scale n wt₁) xs_zs) env idx =
  denote (.scale n (.expand wt₁ xs_zs)) env idx := by
  simp only [denote]

theorem scale_one_expand {S : Type} [Semiring S]
  {Γ : Context}
  {xs zs : Is}
  (xs_zs : xs ⊑ zs)
  (wt₁ : TExpr Γ xs)
  (env : Env (S := S) Γ)
  (idx : Index zs) :
  denote (.expand (.scale 1 wt₁) xs_zs) env idx =
  denote (.expand wt₁ xs_zs) env idx := by
  rw [scale_expand_comm]
  rw [scale_one]

lemma denote_sum_free_union_path_eq {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys xs' ys' zs ws us us' vs : Is}
  (xs_xs' : xs ≈ xs')
  (ys_ys' : ys ≈ ys')
  (xs_ys : xs ⊥ ys)
  (xs_ys' : xs' ⊥ ys')
  (xs_ws : xs ⊑ ws)
  (xs_ws' : xs' ⊑ ws)
  (zs_ys : zs ≈ ys)
  (zs_ys' : zs ≈ ys')
  (xy : unionIs xs ys (disjointIs_compat xs_ys) ≈ us)
  (xy' : unionIs xs' ys' (disjointIs_compat xs_ys') ≈ us')
  (us_us' : us ≈ us')
  (vs_us : vs ⊑ us)
  (vs_us' : vs ⊑ us')
  (wt₁ : TExpr Γ vs)
  (env : Env (S := S) Γ)
  (idx : Index ws)
  (idx' : Index zs) :
  denote wt₁ env
    ((Index.union xs_ys (idx ↓ᵢ xs_ws) (idx' →ᵢ zs_ys) →ᵢ xy) ↓ᵢ vs_us) =
  denote wt₁ env
    ((Index.union xs_ys' (idx ↓ᵢ xs_ws') (idx' →ᵢ zs_ys') →ᵢ xy') ↓ᵢ vs_us') := by
  apply denote_congr
  apply Index.subst_cast_equiv
  · apply Index.compat_cast_equiv
    · apply Index.compat_cast_left_equiv
      · apply Index.union_equiv
        · apply Index.subst_cast_heter
        · apply Index.compat_cast_heter
        · exact xs_xs'
        · exact ys_ys'
    · apply IsRelEquiv.symm
      apply IsRelEquiv.trans
      · exact xy'
      · apply IsRelEquiv.symm
        exact us_us'
  · exact us_us'

lemma einsum_expand_sum_free_comm_two {S : Type} [Semiring S]
  {Γ : Context}
  {xs ys zs ws : Is}
  (wt₁ : TExpr Γ xs)
  (wt₂ : TExpr Γ zs)
  (xs_ys_disj : xs ⊥ ys)
  (xy_z : unionIs xs ys (disjointIs_compat xs_ys_disj) ∼ zs)
  (w_xyz : ws ≈ unionIss (IssCompat_two xy_z))
  (env : Env (S := S) Γ)
  (idx : Index ws) :
  have xyzw_rels := xyzw_Relations xs_ys_disj xy_z (IsEq_subset w_xyz)
  EinsumExpandSumFreeCommEq wt₁ wt₂ xyzw_rels xy_z w_xyz env idx := by
  have xyzw_rels := xyzw_Relations xs_ys_disj xy_z (IsEq_subset w_xyz)
  /- Step 1: rewrite LHS with `einsum_expand_comm_two` -/
  simp only [EinsumExpandSumFreeCommEq]
  rw [einsum_expand_comm_two wt₁ wt₂ xs_ys_disj xy_z]
  /- Step 2: Convert LHS to 1 * e -/
  have fs_empty := sum_free_fs_empty xyzw_rels w_xyz
  rw [empty_prod_one fs_empty]
  /- Step 3: Simplify the LHS to eliminate 1 -/
  rw [scale_one_expand]
  /- Step 4: Reduce LHS with `sum_free_us_xzs` -/
  have us_xzs := sum_free_us_xzs xyzw_rels xs_ys_disj w_xyz
  have us_empty := minusIs_eq_empty (IsRelEquiv.symm us_xzs)
  have xzs_xzs := minusIs_refl_empty (xs := unionIss xyzw_rels.xzs)
  simp only [denote, denotes, mul_one]
  rw [sum_comp (IsRelEquiv.symm us_empty)]
  rw [sum_comp (IsRelEquiv.symm xzs_xzs)]
  /- Step 5: congruence of multiplication -/
  simp only [sum]
  apply Finset.sum_congr rfl
  intro x h
  simp only [Function.comp_apply]
  apply congrArg₂
  · apply denote_sum_free_union_path_eq
    · exact us_xzs
    · apply IsRelEquiv.trans
      · exact us_empty
      · apply IsRelEquiv.symm
        exact minusIs_refl_empty
    · exact IsRelEquiv.refl _
  · apply denote_sum_free_union_path_eq
    · exact us_xzs
    · apply IsRelEquiv.trans
      · exact us_empty
      · apply IsRelEquiv.symm
        exact minusIs_refl_empty
    · exact IsRelEquiv.refl _

end EinsumProperties
