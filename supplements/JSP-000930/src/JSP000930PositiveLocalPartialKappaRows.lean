import JSP000930PositiveCheckedKappaPreservation

namespace JSP000930.Positive

open Cardinal JSP000933.PreparedModel JSP000933.RelativeOCA

variable {B : Type} [CompleteBooleanAlgebra B]

theorem local_bound_for_partial_kappa_rows
    (hB : BoundsSmallKappaNames B) {I : Type}
    (hI : Cardinal.mk I < GroundContinuumSucc)
    (W : I → GroundContinuumSuccIndex → B)
    (hW : ∀ i, Pairwise (fun j k => Disjoint (W i j) (W i k)))
    (m : B) (hm : m ≠ ⊥) :
    ∃ (c : GroundContinuumSuccIndex) (d : B), d ≠ ⊥ ∧ d ≤ m ∧
      ∀ i j, c ≤ j → d ⊓ W i j = ⊥ := by
  classical
  let o := continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos
  let V (i : I) (j : GroundContinuumSuccIndex) : B :=
    W i j ⊔ if j = o then (⨆ k,W i k)ᶜ else ⊥
  have hV (i : I) : (⨆ j,V i j) = ⊤ := by
    apply top_unique
    have h₁ : (⨆ j,W i j) ≤ ⨆ j,V i j :=
      iSup_le fun j => le_iSup_of_le j le_sup_left
    have h₂ : (⨆ j,W i j)ᶜ ≤ ⨆ j,V i j :=
      le_iSup_of_le o (by
        change (⨆ j,W i j)ᶜ ≤ W i o ⊔ (if o = o then (⨆ j,W i j)ᶜ else ⊥)
        rw [ite_eq_left (show o = o from rfl)]
        exact le_sup_right)
    exact sup_compl_eq_top.symm.le.trans (sup_le h₁ h₂)
  let T (c : GroundContinuumSuccIndex) : B := ⨅ i,⨆ j : ↥(Set.Iio c),V i j.val
  have hT : (⨆ c,T c) = ⊤ := by
    apply top_unique
    exact (le_iInf (fun i => (hV i).ge)).trans (hB I hI V)
  have hHit : ∃ c, m ⊓ T c ≠ ⊥ := by
    by_contra hh
    apply hm
    calc
      m = m ⊓ (⨆ c,T c) := by rw [hT,inf_top_eq]
      _ = ⨆ c,m ⊓ T c := inf_iSup_eq _ _
      _ = ⊥ := le_bot_iff.mp (iSup_le (fun c => by
        by_contra hle
        exact hh ⟨c,fun h => hle h.le⟩))
  obtain ⟨c,hc⟩ := hHit
  let d := m ⊓ T c
  refine ⟨c,d,hc,inf_le_left,fun i j hj => ?_⟩
  have hD : d ≤ ⨆ k : ↥(Set.Iio c), V i k.val :=
    inf_le_right.trans (iInf_le _ i)
  have hApart (k : ↥(Set.Iio c)) : V i k.val ⊓ W i j ≤ ⊥ := by
    have hk : k.val ≠ j := (k.property.trans_le hj).ne
    have h0 : Disjoint (W i k.val) (W i j) := hW i hk
    have h1 : Disjoint ((⨆ l,W i l)ᶜ) (W i j) :=
      disjoint_compl_left.mono_right (le_iSup (W i) j)
    unfold V
    rw [inf_sup_right]
    apply sup_le (disjoint_iff_inf_le.mp h0)
    by_cases ho : k.val = o
    · rw [ite_eq_left ho]
      exact disjoint_iff_inf_le.mp h1
    · simp [ho]
  apply le_bot_iff.mp
  exact (inf_le_inf hD le_rfl).trans (by
    rw [iSup_inf_eq]
    exact iSup_le hApart)

end JSP000930.Positive
