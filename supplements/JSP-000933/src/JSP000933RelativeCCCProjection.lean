import JSP000933RelativeOmegaOne

namespace JSP000933
namespace RelativeOCA

open BooleanCompletion MarkedForcing OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

def ForcesRelativeCCC (Q : ValuedPoset B N) : Prop :=
  ∀ W : OmegaOneIndex→N→B,
    (∀ i n,W i n≤Q.valid n) →
    (∀ i j,i<j→∀ n k,(W i n⊓W j k)⊓commonRefinementValue Q n k=⊥) →
    unboundedValue (fun i => ⨆ n,W i n)=⊥

noncomputable def traceWeight (Q : ValuedPoset B N) (x : TotalBA Q) (n : N) : B :=
  ⨆ p : {p : TotalCondition Q // p.trace=n ∧ imageCondition p≤x},p.val.mask

theorem traceWeight_le_valid_r434 (Q : ValuedPoset B N) (x : TotalBA Q) (n : N) :
    traceWeight Q x n≤Q.valid n := by
  apply iSup_le
  intro p
  exact p.val.valid.trans_eq (congrArg Q.valid p.property.1)

theorem traceWeight_joins_projection_r434 (Q : ValuedPoset B N) (x : TotalBA Q) :
    (⨆ n,traceWeight Q x n)=supportProjection Q x := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro p
    exact le_iSup (fun q : {q : TotalCondition Q // imageCondition q ≤ x} => q.val.mask)
      ⟨p.val,p.property.2⟩
  · apply iSup_le
    intro p
    exact le_iSup_of_le p.val.trace (le_iSup (fun q : {q : TotalCondition Q //
      q.trace = p.val.trace ∧ imageCondition q ≤ x} => q.val.mask) ⟨p.val,rfl,p.property⟩)

theorem traceWeights_incompatible_of_disjoint_r434 (Q : ValuedPoset B N)
    {x y : TotalBA Q} (h : Disjoint x y) (n k : N) :
    (traceWeight Q x n⊓traceWeight Q y k)⊓commonRefinementValue Q n k=⊥ := by
  apply le_bot_iff.mp
  simp only [traceWeight,iSup_inf_eq,inf_iSup_eq]
  apply iSup_le
  intro q
  apply iSup_le
  intro p
  change (p.val.mask⊓q.val.mask)⊓commonRefinementValue Q n k≤⊥
  have hTrace : commonRefinementValue Q p.val.trace q.val.trace = commonRefinementValue Q n k :=
    congrArg₂ (commonRefinementValue Q) p.property.1 q.property.1
  rw [← hTrace]
  by_contra hn
  have hN : (p.val.mask⊓q.val.mask)⊓commonRefinementValue Q p.val.trace q.val.trace≠⊥ :=
    fun he => hn he.le
  have hC := (totalCompatible_iff_r426 p.val q.val).mpr hN
  exact ((compatible_iff_not_disjoint_r50 p.val q.val).mp hC)
    ((h.mono_left p.property.2).mono_right q.property.2)

theorem relativeCCC_projectedAntichain_bounded_r434 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (V : OmegaOneIndex→TotalBA Q)
    (hV : ∀ i j,i<j→Disjoint (V i) (V j)) :
    unboundedValue (fun i => supportProjection Q (V i))=⊥ := by
  have hh := hQ (fun i => traceWeight Q (V i))
    (fun i n => traceWeight_le_valid_r434 Q (V i) n)
    (fun i j hij n k => traceWeights_incompatible_of_disjoint_r434 Q (hV i j hij) n k)
  simpa only [traceWeight_joins_projection_r434] using hh

end RelativeOCA
end JSP000933
