import JSP000930PositiveOneReserveUnboundedFamily
import JSP000930PositiveNoInjectionCheckedSmall
import JSP000933FiniteBooleanWitnesses

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000933.RelativeOCA JSP000933.CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedSmall_noSurj_unbounded_family (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc)
    (S T G : bSet B) (m : B)
    (hS : m ≤ S ⊆ᴮ check x) (hG : m ≤ is_func G)
    (hOnto : m ≤ is_surj S T G)
    (hUnbounded : m ≤ unboundedKappaValue
      (fun i => (preparedOrdinalEntry i : bSet B) ∈ᴮ T)) : m = ⊥ := by
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
  have hF : d ≤ ⨆ j : {i : GroundContinuumSuccIndex // β < i},
      (preparedOrdinalEntry j.val : bSet B) ∈ᴮ T :=
    hdm.trans (hUnbounded.trans (iInf_le _ β))
  obtain ⟨j,c,hc,hcd,hMem⟩ := exists_nonzero_below_choice_r135 d hd
    (fun j : {i : GroundContinuumSuccIndex // β < i} =>
      (preparedOrdinalEntry j.val : bSet B) ∈ᴮ T) hF
  let y : bSet B := preparedOrdinalEntry j.val
  have hy : c ≤ y ∈ᴮ T := hMem
  let φ (z : bSet B) := pair z y∈ᴮ G
  have hE : B_ext φ := B_ext_pair_mem_left
  have hA : c≤⨆ w : bSet B,w∈ᴮ S⊓φ w :=
    (le_inf (((hcd.trans hdm).trans hOnto).trans (iInf_le _ y)) hy).trans Lattice.bv_imp_elim
  have hD : c≤⨆ w : bSet B,w∈ᴮ check x⊓φ w := by
    apply (le_inf le_rfl hA).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro w
    apply le_iSup_of_le w
    exact le_inf (mem_of_mem_subset (inf_le_left.trans ((hcd.trans hdm).trans hS))
      (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)
  rw [← bounded_exists (h_congr := hE)] at hD
  have hz : c≤⊥ := by
    apply (le_inf le_rfl hD).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    simp only [check_bval_top,top_inf_eq,check_func]
    change c⊓V (check_cast i) j.val≤⊥
    exact (inf_le_inf hcd le_rfl).trans (hKill (check_cast i) j.val j.property.le).le
  exact hc (le_bot_iff.mp hz)

theorem unbounded_family_not_injects_small (hB : BoundsSmallKappaNames B)
    (x : PSet.{0}) (hx : Cardinal.mk x.Type < GroundContinuumSucc)
    (T : bSet B) (m : B)
    (hUnbounded : m ≤ unboundedKappaValue
      (fun i => (preparedOrdinalEntry i : bSet B) ∈ᴮ T))
    (hI : m ≤ injects_into T (check x)) : m = ⊥ := by
  let o := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  have hNE : m ≤ exists_mem T := by
    apply (hUnbounded.trans (iInf_le _ o)).trans
    apply iSup_le
    intro j
    exact le_iSup (fun y : bSet B => y ∈ᴮ T) (preparedOrdinalEntry j.val)
  have hSurj : m ≤ surjects_onto (check x) T :=
    surjects_onto_of_injects_into' hI hNE
  apply le_bot_iff.mp
  apply (le_inf le_rfl hSurj).trans
  rw [surjects_onto,inf_iSup_eq]
  apply iSup_le
  intro G
  let d := m ⊓ is_surj_onto (check x) T G
  exact (checkedSmall_noSurj_unbounded_family hB x hx (check x) T G d
    (by rw [← inf_idem (check x ⊆ᴮ check x), ← bSet.eq_iff_subset_subset]; exact bSet.bv_refl) (inf_le_right.trans (inf_le_left.trans inf_le_left))
    (inf_le_right.trans inf_le_right) (inf_le_left.trans hUnbounded)).le

end JSP000930.Positive
