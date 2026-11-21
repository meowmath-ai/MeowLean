import JSP000930ActualAugmentedCompatibility

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport

variable {P Q S T : Type} [Preorder P] [Preorder Q] [Preorder S] [Preorder T]

theorem dense_terminal_image_of_dense930 (D : DenseForcingMap P S)
    (X : Set P) (hX : DenseConditionSet X) :
    DenseConditionSet {s : S | ∃ p∈X,s ≤ D.map p} := by
  intro s
  obtain ⟨p,hp⟩ := D.dense s
  obtain ⟨q,hqp,hq⟩ := hX p
  exact ⟨D.map q,(D.monotone hqp).trans hp,q,hq,le_rfl⟩

theorem predensity_through_dense_charts930
    (D : DenseForcingMap P S) (E : DenseForcingMap Q T) (f : P→Q) (g : S→T)
    (hComm : ∀ p,E.map (f p) = g (D.map p)) (hg : Monotone g)
    (hG : PreservesPredensity g) : PreservesPredensity f := by
  intro X hX q
  let Y : Set S := {s | ∃ p∈X,s ≤ D.map p}
  obtain ⟨s,hs,w,hwq,hws⟩ :=
    hG Y (dense_terminal_image_of_dense930 D X hX) (E.map q)
  obtain ⟨p,hp,hsp⟩ := hs
  have h : w ≤ E.map (f p) := hws.trans ((hg hsp).trans_eq (hComm p).symm)
  exact ⟨p,hp,E.reflect_compatible ⟨w,hwq,h⟩⟩

theorem restriction_predensity930 (D : RestrictionMap Q P) (i : P→Q)
    (h : ∀ (q : Q) (p : P),D.toFun q ≤ p → q ≤ i p) :
    PreservesPredensity i := by
  intro X hX q
  obtain ⟨p,hp,hP⟩ := hX (D.toFun q)
  obtain ⟨q',hq',hq'P⟩ := D.lift q p hp
  exact ⟨p,hP,q',hq',h q' p hq'P⟩

variable {B N M : Type} [CompleteBooleanAlgebra B]

def maskSubposet {Q : ValuedPoset B N} (m : B) (p : TotalCondition Q) : Prop :=
  p.mask ≤ m

def DenseForcingMap.masked930 {Q : ValuedPoset B N} {R : ValuedPoset B M} {m : B}
    (D : DenseForcingMap (TotalCondition Q) (TotalCondition R))
    (hMask : ∀ p,(D.map p).mask=p.mask) :
    DenseForcingMap (MaskedCondition Q m) (MaskedCondition R m) where
  map p := ⟨D.map p.val,(hMask p.val).trans_le p.property⟩
  monotone := fun _ _ h => D.monotone h
  dense := by
    intro q
    obtain ⟨p,hp⟩ := D.dense q.val
    exact ⟨⟨p,(hMask p).symm.trans_le (hp.1.trans q.property)⟩,hp⟩
  reflect_compatible := by
    intro p q h
    obtain ⟨r,hrp,hrq⟩ := h
    obtain ⟨u,hup,huq⟩ := D.reflect_compatible ⟨r.val,hrp,hrq⟩
    exact ⟨⟨u,hup.1.trans p.property⟩,hup,huq⟩

end JSP000930.Negative
