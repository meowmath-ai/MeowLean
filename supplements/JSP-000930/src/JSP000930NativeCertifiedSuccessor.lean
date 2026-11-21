import JSP000930CertifiedWeightedForcingEquivalence

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.BooleanCompletion JSP000933.ForcingTransport
open JSP000933.FiniteSupport

def denseForcingMap_comp930 {P Q R : Type} [Preorder P] [Preorder Q] [Preorder R]
    (F : DenseForcingMap P Q) (G : DenseForcingMap Q R) : DenseForcingMap P R where
  map := G.map ∘ F.map
  monotone := G.monotone.comp F.monotone
  dense := by
    intro r
    obtain ⟨q,hq⟩ := G.dense r
    obtain ⟨p,hp⟩ := F.dense q
    exact ⟨p,(G.monotone hp).trans hq⟩
  reflect_compatible := fun h => F.reflect_compatible (G.reflect_compatible h)

private theorem staticValuedPoset_eq_of_value_eq {D T : Type} [CompleteBooleanAlgebra D] [Preorder T]
    [OrderTop T] (v w : T → D) (hv : Monotone v) (hw : Monotone w)
    (hvt : v ⊤ = ⊤) (hwt : w ⊤ = ⊤) (h : v = w) :
    staticValuedPoset v hv hvt = staticValuedPoset w hw hwt := by
  subst w
  rfl

variable {A B N : Type} [LinearOrder A] [OrderBot A] [WellFoundedLT A]
  [NontrivialCompleteBooleanAlgebra B]

theorem nativeTailValuePoset_eq_certified
    (tail : BasedTailPolicy A B (CertifiedStageLabel N)) {a : A}
    (Q : ValuedPoset (PreStageAlgebra tail (a := a)) N)
    (hV : Monotone (TailStageValues tail (a := a))) (hTop : TailStageValues tail (a := a) ⊤ = ⊤)
    (hA : TailStageValues tail (a := a) = CertifiedStageLabel.admits Q) :
    ExactTailIterand tail hV hTop = certifiedQ Q := by
  exact staticValuedPoset_eq_of_value_eq _ _ hV (CertifiedStageLabel.admits_mono Q) hTop
    (CertifiedStageLabel.admits_top Q) hA

noncomputable def nativeCertifiedSuccessor
    (tail : BasedTailPolicy A B (CertifiedStageLabel N)) {a b : A} (ha : a ≠ ⊥)
    (succ : ∀ i : A,i<b ↔ i≤a)
    (Q : ValuedPoset (PreStageAlgebra tail (a := a)) N)
    (hA : TailStageValues tail (a := a) = CertifiedStageLabel.admits Q) :
    DenseForcingMap (BasedBefore tail b) (TotalCondition Q) := by
  have hV : Monotone (TailStageValues tail (a := a)) := hA.symm ▸ CertifiedStageLabel.admits_mono Q
  have hTop : TailStageValues tail (a := a) ⊤ = ⊤ := by rw [hA,CertifiedStageLabel.admits_top]
  have hEq := nativeTailValuePoset_eq_certified tail Q hV hTop hA
  let M : DenseForcingMap (BasedBefore tail b) (TotalCondition (certifiedQ Q)) :=
    hEq ▸ markedSuccessorComparison tail ha hV hTop succ
  exact denseForcingMap_comp930 M (certifiedHeadDenseMap Q)

end JSP000930.Negative
