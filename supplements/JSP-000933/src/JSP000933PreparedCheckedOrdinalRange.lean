import JSP000933PreparedPartialProfiles

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

noncomputable def preparedOrdinalEntry {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (i : GroundContinuumSuccIndex) : bSet B :=
  check (BaseSuccPSet.Func (baseSuccIndexEquiv i))

theorem preparedOrdinalEntry_asOrdinal_r416 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (i : GroundContinuumSuccIndex) :
    (preparedOrdinalEntry i : bSet B)=check (PSet.ordinalMk (continuumSuccOrdinal i)) := by
  unfold preparedOrdinalEntry
  apply congrArg (fun x => (check x : bSet B))
  exact baseSuccFunc_ordinal_r397 i

theorem preparedOrdinalEntry_eq_bot_r416 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    {i j : GroundContinuumSuccIndex} (h : i≠j) :
    ((preparedOrdinalEntry i : bSet B)=ᴮ preparedOrdinalEntry j)=⊥ := by
  unfold preparedOrdinalEntry
  apply check_bv_eq_bot_of_not_equiv
  exact PSet.ordinalMk_inj GroundContinuumSucc.ord _ _ (fun he => h (baseSuccIndexEquiv.injective he))

noncomputable def preparedGraphValues (x : PSet.{0}) (G : bSet PreparedBA)
    (i : x.Type) (j : GroundContinuumSuccIndex) : PreparedBA :=
  pair (check (x.Func i)) (preparedOrdinalEntry j)∈ᴮ G

theorem preparedGraphValues_disjoint_r416 (x : PSet.{0}) (G : bSet PreparedBA)
    (i : x.Type) :
    Pairwise (fun j k => Disjoint (is_func G⊓preparedGraphValues x G i j)
      (is_func G⊓preparedGraphValues x G i k)) := by
  intro j k hJK
  apply disjoint_iff_inf_le.mpr
  let r := (is_func G⊓preparedGraphValues x G i j)⊓(is_func G⊓preparedGraphValues x G i k)
  have hF : r≤ is_func G := inf_le_left.trans inf_le_left
  have hJ : r≤preparedGraphValues x G i j := inf_le_left.trans inf_le_right
  have hK : r≤preparedGraphValues x G i k := inf_le_right.trans inf_le_right
  have hEq : r≤preparedOrdinalEntry j=ᴮ (preparedOrdinalEntry k : bSet PreparedBA) :=
    eq_of_is_func_of_eq hF bv_refl hJ hK
  exact hEq.trans_eq (preparedOrdinalEntry_eq_bot_r416 hJK)

noncomputable def preparedRangeBelow (X Y G d : bSet PreparedBA) : PreparedBA :=
  ⨅ a : bSet PreparedBA,(a∈ᴮ X)⟹
    (⨅ b : bSet PreparedBA,(b∈ᴮ Y)⟹((pair a b∈ᴮ G)⟹ b∈ᴮ d))

theorem prepared_rangeValue_of_zeroRows_r416 (x : PSet.{0}) (G : bSet PreparedBA)
    (m : PreparedBA) (β : GroundContinuumSuccIndex)
    (hV : ∀ i j,β≤j → m⊓preparedGraphValues x G i j=⊥) :
    m≤preparedRangeBelow (check x) (check BaseSuccPSet) G (preparedOrdinalEntry β) := by
  let d : bSet PreparedBA := preparedOrdinalEntry β
  unfold preparedRangeBelow
  have hA : B_ext (fun a : bSet PreparedBA => ⨅ b : bSet PreparedBA,
      (b∈ᴮ check BaseSuccPSet)⟹((pair a b∈ᴮ G)⟹ b∈ᴮ d)) :=
    B_ext_iInf (h := fun b => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_const)))
  rw [← bounded_forall (h_congr := hA)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,inf_top_eq,check_func]
  let a : bSet PreparedBA := check (x.Func (check_cast i))
  have hB : B_ext (fun b : bSet PreparedBA => (pair a b∈ᴮ G)⟹ b∈ᴮ d) :=
    B_ext_imp (h₁ := B_ext_pair_mem_right) (h₂ := B_ext_mem_left)
  change m≤⨅ b : bSet PreparedBA,(b∈ᴮ check BaseSuccPSet)⟹((pair a b∈ᴮ G)⟹ b∈ᴮ d)
  rw [← bounded_forall (h_congr := hB)]
  apply le_iInf
  intro j
  rw [← deduction,check_bval_top,inf_top_eq,check_func,← deduction]
  let z := baseSuccIndexEquiv.symm (check_cast j)
  have hz : (preparedOrdinalEntry z : bSet PreparedBA)=check (BaseSuccPSet.Func (check_cast j)) := by
    simp [preparedOrdinalEntry,z]
  rw [←hz]
  by_cases hb : z<β
  · change _≤(preparedOrdinalEntry z : bSet PreparedBA)∈ᴮ preparedOrdinalEntry β
    rw [preparedOrdinalEntry_asOrdinal_r416,preparedOrdinalEntry_asOrdinal_r416]
    exact check_mem (prepOrdinalMk_mem_of_lt_r397 ((continuumSuccIndex_lt_iff_r399 _ _).mp hb))
  · change m⊓preparedGraphValues x G (check_cast i) z≤_
    rw [hV _ _ (le_of_not_gt hb)]
    exact bot_le

theorem prepared_checkedShort_graphRange_r416 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) (G : bSet PreparedBA) :
    is_func G≤⨆ d : bSet PreparedBA,d∈ᴮ check BaseSuccPSet⊓
      preparedRangeBelow (check x) (check BaseSuccPSet) G d := by
  classical
  let v : PreparedBA := ⨆ d : bSet PreparedBA,d∈ᴮ check BaseSuccPSet⊓
    preparedRangeBelow (check x) (check BaseSuccPSet) G d
  change is_func G≤v
  by_contra hn
  have hNZ : is_func G⊓vᶜ≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hNZ
  obtain ⟨s,β,hs,hV⟩ := prepared_partialProfiles_bounded_r415 hx
    (preparedGraphValues x G) (is_func G) (preparedGraphValues_disjoint_r416 x G)
    p.1 p.2 (hp.trans inf_le_left)
  let q : PreparedCondition := (p.1,s)
  have hq : q≤p := ⟨le_rfl,hs⟩
  have hqN : imageCondition q≤vᶜ := (imageCondition_mono_r50 hq).trans (hp.trans inf_le_right)
  have hEntry : imageCondition q≤(preparedOrdinalEntry β : bSet PreparedBA)∈ᴮ check BaseSuccPSet :=
    check_mem (PSet.func_mem BaseSuccPSet (baseSuccIndexEquiv β))
  have hqR : imageCondition q≤v := le_iSup_of_le (preparedOrdinalEntry β)
    (le_inf hEntry (prepared_rangeValue_of_zeroRows_r416 x G (imageCondition q) β hV))
  exact imageCondition_ne_bot_r50 q (disjoint_compl_right.out _ hqR hqN)

end PreparedModel
end JSP000933
