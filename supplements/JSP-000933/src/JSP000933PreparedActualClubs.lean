import JSP000933PreparedOrdinalQuantifiers
import JSP000933PreparedNameCodedDiamond

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable def actualCofinalIn (s d : bSet PreparedBA) : PreparedBA :=
  ⨅ x : bSet PreparedBA,(x∈ᴮ d)⟹
    (⨆ y : bSet PreparedBA,(y∈ᴮ d)⊓((x∈ᴮ y)⊓(y∈ᴮ s)))

noncomputable def actualClosedIn (s k : bSet PreparedBA) : PreparedBA :=
  ⨅ d : bSet PreparedBA,(d∈ᴮ k)⟹
    ((⨆ x : bSet PreparedBA,x∈ᴮ d)⟹(actualCofinalIn s d⟹d∈ᴮ s))

noncomputable def preparedActualClub (s : bSet PreparedBA) : PreparedBA :=
  actualCofinalIn s (check BaseSuccPSet)⊓actualClosedIn s (check BaseSuccPSet)

noncomputable def preparedProfile (s : bSet PreparedBA) (i : GroundContinuumSuccIndex) : PreparedBA :=
  preparedOrdinalEntry i∈ᴮ s

theorem preparedAbove_semantics_r419 (s : bSet PreparedBA) (a : GroundContinuumSuccIndex) :
    (⨆ y : bSet PreparedBA,(y∈ᴮ check BaseSuccPSet)⊓
      (((preparedOrdinalEntry a : bSet PreparedBA)∈ᴮ y)⊓(y∈ᴮ s)))=
        aboveClub (preparedProfile s) a := by
  rw [checkedBoundedExists_eq_r418 BaseSuccPSet preparedOrdinalEntry
    preparedKappa_basis_r418 preparedKappa_mem_r418 _
    (B_ext_inf B_ext_mem_right B_ext_mem_left)]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases h : a<j
    · exact inf_le_right.trans (le_iSup (fun k : {k : GroundContinuumSuccIndex // a < k} => preparedProfile s k.val) ⟨j,h⟩)
    · rw [preparedEntry_mem_bot_r418 h,bot_inf_eq]
      exact bot_le
  · apply iSup_le
    intro j
    apply le_iSup_of_le j.val
    exact le_inf (le_top.trans (preparedEntry_mem_top_r418 j.property)) le_rfl

theorem preparedWindow_semantics_r419 (s : bSet PreparedBA) (a d : GroundContinuumSuccIndex) :
    (⨆ y : bSet PreparedBA,(y∈ᴮ preparedOrdinalEntry d)⊓
      (((preparedOrdinalEntry a : bSet PreparedBA)∈ᴮ y)⊓(y∈ᴮ s)))=
        inClubWindow (preparedProfile s) a d := by
  rw [preparedOrdinalEntry_asOrdinal_r416 d]
  rw [checkedBoundedExists_eq_r418 (PSet.ordinalMk (continuumSuccOrdinal d))
    (fun j : ↥(Set.Iio d) => preparedOrdinalEntry j.val) (preparedEntry_basis_r418 d)
    (fun j => by
      rw [← preparedOrdinalEntry_asOrdinal_r416 d]
      exact preparedEntry_mem_top_r418 j.property) _
    (B_ext_inf B_ext_mem_right B_ext_mem_left)]
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases h : a<j.val
    · exact inf_le_right.trans (le_iSup (fun k : {k : GroundContinuumSuccIndex // a < k ∧ k < d} => preparedProfile s k.val)
      ⟨j.val,h,j.property⟩)
    · rw [preparedEntry_mem_bot_r418 h,bot_inf_eq]
      exact bot_le
  · apply iSup_le
    intro j
    apply le_iSup_of_le (⟨j.val,j.property.2⟩ : ↥(Set.Iio d))
    exact le_inf (le_top.trans (preparedEntry_mem_top_r418 j.property.1)) le_rfl

theorem prepared_actualClub_reduces_r419 (s : bSet PreparedBA) (m : PreparedBA)
    (h : m≤preparedActualClub s) :
    (∀ a,m≤aboveClub (preparedProfile s) a) ∧
    (∀ d,OmegaOneCofinalIndex d → m⊓clubAccumulation (preparedProfile s) d≤preparedProfile s d) := by
  constructor
  · intro a
    unfold preparedActualClub actualCofinalIn at h
    rw [← preparedAbove_semantics_r419]
    exact (le_inf (h.trans (inf_le_left.trans (iInf_le _ (preparedOrdinalEntry a))))
      (le_top.trans (preparedKappa_mem_r418 a))).trans Lattice.bv_imp_elim
  · intro d hd
    let D : bSet PreparedBA := preparedOrdinalEntry d
    let r := m⊓clubAccumulation (preparedProfile s) d
    have hr : r≤ m := inf_le_left
    have hD : r≤D∈ᴮ check BaseSuccPSet := le_top.trans (preparedKappa_mem_r418 d)
    have hCl : r≤(⨆ x : bSet PreparedBA,x∈ᴮ D)⟹
        (actualCofinalIn s D⟹D∈ᴮ s) :=
      (le_inf ((hr.trans h).trans (inf_le_right.trans (iInf_le _ D))) hD).trans Lattice.bv_imp_elim
    have hd0 : 0<continuumSuccOrdinal d := by
      by_contra hn
      have he : continuumSuccOrdinal d=0 := le_antisymm (le_of_not_gt hn) zero_le
      unfold OmegaOneCofinalIndex at hd
      rw [he,Ordinal.cof_zero] at hd
      exact (ne_of_gt (Cardinal.aleph0_pos.trans PSet.omega_lt_aleph_one)) hd.symm
    let zero := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
    have hz : zero<d :=
      (continuumSuccIndex_lt_iff_r399 _ _).mpr (by simpa [zero] using hd0)
    have hN : r≤⨆ x : bSet PreparedBA,x∈ᴮ D :=
      le_iSup_of_le (preparedOrdinalEntry zero) (le_top.trans (preparedEntry_mem_top_r418 hz))
    have hA : r≤actualCofinalIn s D := by
      unfold actualCofinalIn
      rw [show D=check (PSet.ordinalMk (continuumSuccOrdinal d)) from preparedOrdinalEntry_asOrdinal_r416 d]
      let F (x : bSet PreparedBA) := ⨆ y : bSet PreparedBA,
        (y∈ᴮ check (PSet.ordinalMk (continuumSuccOrdinal d)))⊓((x∈ᴮ y)⊓(y∈ᴮ s))
      have hF : B_ext F :=
        B_ext_iSup (h := fun y => B_ext_inf B_ext_const (B_ext_inf B_ext_mem_left B_ext_const))
      apply (checkedBoundedAll_iff_r418 (PSet.ordinalMk (continuumSuccOrdinal d))
        (fun j : ↥(Set.Iio d) => preparedOrdinalEntry j.val) (preparedEntry_basis_r418 d)
        (fun j => by
          rw [← preparedOrdinalEntry_asOrdinal_r416 d]
          exact preparedEntry_mem_top_r418 j.property) r F hF).mpr
      intro j
      change r≤F (preparedOrdinalEntry j.val)
      rw [show F (preparedOrdinalEntry j.val)=inClubWindow (preparedProfile s) j.val d from by
        unfold F
        rw [← preparedOrdinalEntry_asOrdinal_r416 d,preparedWindow_semantics_r419]]
      exact inf_le_right.trans (iInf_le _ j)
    exact (le_inf ((le_inf hCl hN).trans Lattice.bv_imp_elim) hA).trans Lattice.bv_imp_elim

end PreparedModel
end JSP000933
