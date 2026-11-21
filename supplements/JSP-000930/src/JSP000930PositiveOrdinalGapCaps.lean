import JSP000930PositiveActiveFamilyOneReserve

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.PreparedModel JSP000930.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem ordinal_noMem_reverse_inject {a b : bSet B} {p : B}
    (ha : p ≤ Ord a) (hb : p ≤ Ord b) (hn : p ≤ (a ∈ᴮ b)ᶜ) :
    p ≤ injects_into b a := by
  apply injects_into_of_subset
  rw [Ord.le_iff_lt_or_eq hb ha]
  have ht := Ord.trichotomy ha hb
  apply (le_inf ht le_rfl).trans
  rw [inf_sup_right,inf_sup_right]
  apply sup_le
  · apply sup_le
    · exact (inf_le_left.trans_eq bv_eq_symm).trans le_sup_right
    · exact (disjoint_compl_right.out _ inf_le_left (inf_le_right.trans hn)).le.trans bot_le
  · exact inf_le_left.trans le_sup_left

theorem ordinal_mem_of_reverse_not_inject {a b : bSet B} {p : B}
    (ha : p ≤ Ord a) (hb : p ≤ Ord b)
    (hn : p ≤ (injects_into b a)ᶜ) : p ≤ a ∈ᴮ b := by
  by_contra hh
  let d := p ⊓ (a ∈ᴮ b)ᶜ
  have hd : d ≠ ⊥ := fun e =>
    hh (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr e.le))
  have hi : d ≤ injects_into b a :=
    ordinal_noMem_reverse_inject (inf_le_left.trans ha) (inf_le_left.trans hb) inf_le_right
  exact hd (disjoint_compl_right.out _ hi (inf_le_left.trans hn))

theorem checked_gap_cap_eq_omegaOne
    (X : bSet B) (p : B)
    (hOrd : p ≤ Ord X)
    (hAbove : p ≤ (injects_into X bSet.omega)ᶜ)
    (hBelow : p ≤ (injects_into (bv_powerset bSet.omega) X)ᶜ)
    (h₁ : p ≤ nextInitialCard bSet.omega (check BaseOmegaOne))
    (h₂ : p ≤ nextInitialCard (check BaseOmegaOne) (check BaseSuccPSet))
    (hReals : p ≤ injects_into (bv_powerset bSet.omega) (check BaseSuccPSet)) :
    p ≤ injects_into X (check BaseOmegaOne) ⊓ injects_into (check BaseOmegaOne) X := by
  have hOrd₁ : p ≤ Ord (check BaseOmegaOne : bSet B) := h₁.trans inf_le_left
  have hOrd₂ : p ≤ Ord (check BaseSuccPSet : bSet B) := h₂.trans inf_le_left
  have hLt₂ : p ≤ (injects_into (check BaseSuccPSet) X)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hI : p ⊓ injects_into (check BaseSuccPSet) X ≤
        injects_into (bv_powerset bSet.omega) X :=
      injects_into_trans (inf_le_left.trans hReals) inf_le_right
    exact le_bot_iff.mpr (disjoint_compl_right.out _ hI (inf_le_left.trans hBelow))
  have hm : p ≤ X ∈ᴮ (check BaseSuccPSet : bSet B) :=
    ordinal_mem_of_reverse_not_inject hOrd hOrd₂ hLt₂
  have hInj₁ : p ≤ injects_into X (check BaseOmegaOne) := by
    have h : p ≤ ⨅ d : bSet B, imp (d ∈ᴮ check BaseSuccPSet) (injects_into d (check BaseOmegaOne)) :=
      h₂.trans (inf_le_right.trans inf_le_right)
    exact (le_inf (h.trans (iInf_le _ X)) hm).trans Lattice.bv_imp_elim
  have hNo₁ : p ≤ (X ∈ᴮ (check BaseOmegaOne : bSet B))ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have h : p ⊓ (X ∈ᴮ check BaseOmegaOne) ≤ injects_into X bSet.omega :=
      injects_into_omega_of_mem_aleph_one_check inf_le_right
    exact le_bot_iff.mpr (disjoint_compl_right.out _ h (inf_le_left.trans hAbove))
  exact le_inf hInj₁ (ordinal_noMem_reverse_inject hOrd hOrd₁ hNo₁)

end JSP000930.Positive
