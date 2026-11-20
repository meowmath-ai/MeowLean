import JSP000933RelativeJoinedLabelWeights
import JSP000933BooleanRectangleThinning

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

abbrev OffDiagonalCode (n : ℕ) := OffDiag n→Word×Word

noncomputable def offDiagonalTest {n : ℕ} (K : Word×Word→B)
    (X : Fin n→ℕ→B) (c : OffDiagonalCode n) : B :=
  ⨅ a : OffDiag n,K (c a)⊓(cylinderValue (X a.val.1) (c a).1⊓
    cylinderValue (X a.val.2) (c a).2)

theorem offDiagonalTests_cover_r453 {n : ℕ} (K : Word×Word→B)
    (X : Fin n→ℕ→B) (w : B)
    (hW : ∀ a b,a≠b → w≤colorValue K (X a) (X b)) :
    w=⨆ c : OffDiagonalCode n,w⊓offDiagonalTest K X c := by
  apply le_antisymm
  · by_contra hn
    let u := ⨆ c : OffDiagonalCode n,w⊓offDiagonalTest K X c
    let p := w⊓uᶜ
    have hp : p≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    let f (a : OffDiag n) (v : Word×Word) :=
      K v⊓(cylinderValue (X a.val.1) v.1⊓cylinderValue (X a.val.2) v.2)
    obtain ⟨c,q,hq,hqp,hC⟩ := exists_nonzero_finiteChoices_r135 f p hp
      (le_iInf (fun a : OffDiag n => inf_le_left.trans (hW a.val.1 a.val.2 a.property)))
    have hU : q≤u := le_iSup_of_le c (le_inf (hqp.trans inf_le_left) (le_iInf hC))
    exact hq (disjoint_compl_right.out _ hU (hqp.trans inf_le_right))
  · exact iSup_le (fun _ => inf_le_left)

noncomputable def rectangularWeight {n : ℕ} (K : Word×Word→B) (X : LabelCandidate→Fin n→ℕ→B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (c : OffDiagonalCode n)
    (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : B :=
  W i s⊓offDiagonalTest K (X (i,s)) c

theorem rectangularWeight_unbounded_r453 {n : ℕ} (hB : BoundsCountableOmegaOneNames B)
    (K : Word×Word→B) (X : LabelCandidate→Fin n→ℕ→B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hW : ∀ i s a b,a≠b → W i s≤colorValue K (X (i,s) a) (X (i,s) b)) :
    unboundedValue (rowLabelWeight W)=
      ⨆ c : OffDiagonalCode n,unboundedValue (rowLabelWeight (rectangularWeight K X W c)) := by
  have hE : rowLabelWeight W=(fun i => ⨆ c : OffDiagonalCode n,
      rowLabelWeight (rectangularWeight K X W c) i) := by
    funext i
    apply le_antisymm
    · apply iSup_le
      intro s
      have hCover := offDiagonalTests_cover_r453 K (X (i,s)) (W i s) (hW i s)
      apply hCover.le.trans
      apply iSup_le
      intro c
      exact le_iSup_of_le c (le_iSup (rectangularWeight K X W c i) s)
    · apply iSup_le
      intro c
      apply iSup_le
      intro s
      exact inf_le_left.trans (le_iSup _ s)
  rw [hE,unboundedValue_countableTypePartition_r443 hB]

theorem rectangularWeight_cross_r453 {n : ℕ} (K : Word×Word→B) (X : LabelCandidate→Fin n→ℕ→B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (c : OffDiagonalCode n)
    (x y : LabelCandidate) {a b : Fin n} (h : a≠b) :
    rectangularWeight K X W c x.1 x.2⊓rectangularWeight K X W c y.1 y.2≤
      colorValue K (X x a) (X y b) := by
  let q : OffDiag n := ⟨(a,b),h⟩
  have hx := (show rectangularWeight K X W c x.1 x.2≤offDiagonalTest K (X x) c from
    inf_le_right).trans (iInf_le _ q)
  have hy := (show rectangularWeight K X W c y.1 y.2≤offDiagonalTest K (X y) c from
    inf_le_right).trans (iInf_le _ q)
  exact edgeBox_suffices_r136 K (X x a) (X y b) (c q)
    (inf_le_left.trans (hx.trans inf_le_left))
    (inf_le_left.trans (hx.trans (inf_le_right.trans inf_le_left)))
    (inf_le_right.trans (hy.trans (inf_le_right.trans inf_le_right)))

end RelativeOCA
end JSP000933
