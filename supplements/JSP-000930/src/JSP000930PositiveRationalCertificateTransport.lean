import JSP000930PositiveDyadicCutFirstOrder

namespace JSP000930.Positive.Cohen

open JSP000930.Positive.Dyadic
open JSP000933.BooleanCompletion

variable {B I : Type} [CompleteBooleanAlgebra B]

def ProperSubinterval (w : List Bool) (ab : ℚ × ℚ) : Prop :=
  (unitInterval.follow w).left < ab.1 ∧ ab.1 < ab.2 ∧
    ab.2 < (unitInterval.follow w).right

def StrictlyInsideCertificate (w : List Bool) (ab : ℚ × ℚ) : Prop :=
  ab.1 < (unitInterval.follow w).left ∧ (unitInterval.follow w).right < ab.2

theorem fresh_row_from_rational_interval_certificates
    (S : Set (I × ℕ)) (i : I) (hFresh : ∀ n,(i,n) ∉ S)
    (p : CohenBlockBA B S) (cert : ℚ × ℚ → CohenBlockBA B S)
    (hDense : ∀ u,p ≤ ⨆ ab : {ab : ℚ × ℚ // ProperSubinterval u ab},cert ab.val)
    (goal : CohenBA B (I × ℕ))
    (hSound : ∀ w ab,StrictlyInsideCertificate w ab →
      wordValue B i w ⊓ blockEmbed B S (cert ab) ≤ goal) :
    blockEmbed B S p ≤ goal := by
  let D (w : List Bool) : CohenBlockBA B S :=
    ⨆ ab : {ab : ℚ × ℚ // StrictlyInsideCertificate w ab},cert ab.val
  have hD (u : List Bool) : p ≤ ⨆ v,D (u ++ v) := by
    apply (hDense u).trans
    apply iSup_le
    intro ab
    let s := unitInterval.follow u
    let a := ab.val.1
    let b := ab.val.2
    let q := (a+b)/2
    have hab : a < b := ab.property.2.1
    have ha : a < q := by unfold q; linarith
    have hb : q < b := by unfold q; linarith
    obtain ⟨v,hvL,hvR⟩ := exists_descendant_inside s a q b ha hb
      (ab.property.1.le.trans ha.le) (hb.le.trans ab.property.2.2.le)
    apply le_iSup_of_le v
    have hGood : StrictlyInsideCertificate (u ++ v) ab.val := by
      unfold StrictlyInsideCertificate
      rw [Interval.follow_append]
      exact ⟨hvL,hvR⟩
    exact le_iSup (fun ab : {z : ℚ × ℚ // StrictlyInsideCertificate (u ++ v) z} =>
      cert ab.val) ⟨ab.val,hGood⟩
  apply (fresh_row_meets_mixed_dense_words S i hFresh p D hD).trans
  apply iSup_le
  intro w
  unfold D
  rw [blockEmbed_general_iSup,inf_iSup_eq]
  exact iSup_le fun ab => hSound w ab.val ab.property

end JSP000930.Positive.Cohen
