import JSP000930PositiveLocalPartialKappaRows
import JSP000933PreparedOrdinalQuantifiers

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive
open JSP000933.PreparedModel JSP000933.RelativeOCA

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedSmallDomain_noSurj_kappa (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc)
    (S G : bSet B) (m : B)
    (hS : m ≤ S ⊆ᴮ check x) (hG : m ≤ is_func G)
    (hOnto : m ≤ is_surj S (check BaseSuccPSet) G) : m = ⊥ := by
  classical
  by_contra hm
  let V (i : x.Type) (j : GroundContinuumSuccIndex) : B :=
    pair (check (x.Func i)) (preparedOrdinalEntry j) ∈ᴮ G
  let W (i : x.Type) (j : GroundContinuumSuccIndex) : B := m ⊓ V i j
  have hDisj (i : x.Type) : Pairwise (fun j k => Disjoint (W i j) (W i k)) := by
    intro j k hjk
    apply disjoint_iff_inf_le.mpr
    let c := W i j ⊓ W i k
    have hM : c ≤ m := inf_le_left.trans inf_le_left
    have hJ : c ≤ V i j := inf_le_left.trans inf_le_right
    have hK : c ≤ V i k := inf_le_right.trans inf_le_right
    have he : c ≤ (preparedOrdinalEntry j : bSet B) =ᴮ preparedOrdinalEntry k :=
      eq_of_is_func_of_eq (hM.trans hG) bv_refl hJ hK
    exact he.trans_eq (preparedOrdinalEntry_eq_bot_r416 hjk)
  obtain ⟨β,d,hd,hdm,hW⟩ := local_bound_for_partial_kappa_rows hB hx W hDisj m hm
  have hKill (i : x.Type) (j : GroundContinuumSuccIndex) (hj : β ≤ j) :
      d ⊓ V i j = ⊥ := by
    have h := hW i j hj
    change d ⊓ (m ⊓ V i j) = ⊥ at h
    rwa [← inf_assoc,inf_eq_left.mpr hdm] at h
  let y : bSet B := preparedOrdinalEntry β
  have hy : d≤y∈ᴮ (check BaseSuccPSet : bSet B) :=
    check_mem (PSet.func_mem BaseSuccPSet (baseSuccIndexEquiv β))
  let φ (z : bSet B) := pair z y∈ᴮ G
  have hE : B_ext φ := B_ext_pair_mem_left
  have hA : d≤⨆ w : bSet B,w∈ᴮ S⊓φ w :=
    (le_inf ((hdm.trans hOnto).trans (iInf_le _ y)) hy).trans Lattice.bv_imp_elim
  have hD : d≤⨆ w : bSet B,w∈ᴮ check x⊓φ w := by
    apply (le_inf le_rfl hA).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro w
    apply le_iSup_of_le w
    exact le_inf (mem_of_mem_subset (inf_le_left.trans (hdm.trans hS))
      (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)
  rw [← bounded_exists (h_congr := hE)] at hD
  have hz : d≤⊥ := by
    apply (le_inf le_rfl hD).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    simp only [check_bval_top,top_inf_eq,check_func]
    change d⊓V (check_cast i) β≤⊥
    exact (hKill (check_cast i) β le_rfl).le
  exact hd (le_bot_iff.mp hz)

theorem checkedSmall_notLarger_kappa (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc) :
    larger_than (check x : bSet B) (check BaseSuccPSet) = ⊥ := by
  apply le_bot_iff.mp
  unfold larger_than
  apply iSup_le
  intro S
  apply iSup_le
  intro G
  let c := ((S ⊆ᴮ (check x : bSet B)) ⊓ is_func' S (check BaseSuccPSet) G) ⊓
    is_surj S (check BaseSuccPSet) G
  exact (checkedSmallDomain_noSurj_kappa hB x hx S G c
    (inf_le_left.trans inf_le_left)
    (inf_le_left.trans (inf_le_right.trans inf_le_left)) inf_le_right).le

theorem checkedSmall_notInject_kappa (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc) :
    injects_into (check BaseSuccPSet : bSet B) (check x) = ⊥ := by
  let m := injects_into (check BaseSuccPSet : bSet B) (check x)
  let i := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  have he : m ≤ exists_mem (check BaseSuccPSet : bSet B) := by
    unfold exists_mem
    exact le_iSup_of_le (preparedOrdinalEntry i) (le_top.trans (preparedKappa_mem_r418 i))
  have hL : m ≤ larger_than (check x : bSet B) (check BaseSuccPSet) :=
    larger_than_of_surjects_onto (surjects_onto_of_injects_into' le_rfl he)
  exact le_bot_iff.mp (hL.trans_eq (checkedSmall_notLarger_kappa hB x hx))

end JSP000930.Positive
