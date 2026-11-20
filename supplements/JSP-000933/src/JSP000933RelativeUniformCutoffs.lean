import JSP000933RelativeGenericUnbounded

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem uniform_countable_cutoffs_r444 (hB : BoundsCountableOmegaOneNames B)
    {I : Type} [Countable I] (m : B) (V : I→OmegaOneIndex→B)
    (hMono : ∀ i,Monotone (V i)) (hV : ∀ i,m≤⨆ b,V i b) :
    m≤⨆ b : OmegaOneIndex,⨅ i,V i b := by
  letI := Encodable.ofCountable I
  let U (n : ℕ) (b : OmegaOneIndex) :=
    match (Encodable.decode n : Option I) with
    | none => (⊤ : B)
    | some i => V i b
  have hU (n : ℕ) : m≤⨆ b,U n b := by
    cases hn : (Encodable.decode n : Option I) with
    | none =>
      have hI : Nonempty OmegaOneIndex :=
        Ordinal.nonempty_toType_iff.mpr (ne_of_gt Cardinal.isRegular_aleph_one.ord_pos)
      obtain ⟨b⟩ := hI
      apply le_iSup_of_le b
      simp [U,hn]
    | some i => simpa [U,hn] using hV i
  apply ((le_iInf hU).trans (hB U)).trans
  apply iSup_le
  intro b
  apply le_iSup_of_le b
  apply le_iInf
  intro i
  apply (iInf_le _ (Encodable.encode i)).trans
  apply iSup_le
  intro a
  simpa only [U,Encodable.encodek] using hMono i a.property.le

theorem boundedValue_eq_join_r444 (w : OmegaOneIndex→B) :
    (unboundedValue w)ᶜ=⨆ b,(aboveValue w b)ᶜ := by
  simp only [unboundedValue,compl_iInf]

end RelativeOCA
end JSP000933
