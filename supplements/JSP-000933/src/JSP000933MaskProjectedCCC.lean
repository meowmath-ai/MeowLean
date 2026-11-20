import JSP000933ProjectedSuccessorCCC
import JSP000933NativeBasePrefixCoherence

namespace JSP000933

open BooleanCompletion

namespace ForcingTransport

open RelativeOCA OpenGraphForcing

variable {B P : Type} [CompleteBooleanAlgebra B] [Preorder P]

noncomputable def MaskRealization.project (M : MaskRealization B P) (x : RO P) : B :=
  ⨆ p : {p : P // imageCondition p≤x}, M.mask p.val

theorem MaskRealization.project_gc (M : MaskRealization B P) :
    GaloisConnection M.project M.embed := by
  intro x b
  constructor
  · intro h
    apply le_of_image_tests
    intro p hp
    exact M.image_le p b ((le_iSup (fun q : {q : P // imageCondition q ≤ x} => M.mask q.val) ⟨p,hp⟩).trans h)
  · intro h
    exact iSup_le (fun p => (M.image_le_iff p.val b).mp (p.property.trans h))

theorem MaskRealization.project_trace_cut (M : MaskRealization B P) (p : P) (b : B) :
    M.project (imageCondition p ⊓ M.embed b) = M.mask p ⊓ b := by
  apply le_antisymm
  · apply iSup_le
    intro q
    have h1 : M.mask q.val ≤ M.mask p :=
      (M.image_le_iff q.val _).mp (q.property.trans (inf_le_left.trans (M.image_le p _ le_rfl)))
    have h2 : M.mask q.val ≤ b := (M.image_le_iff q.val b).mp (q.property.trans inf_le_right)
    exact le_inf h1 h2
  · by_cases h : M.mask p ⊓ b = ⊥
    · rw [h]; exact bot_le
    · obtain ⟨q,hqp,hq⟩ := M.cut p b h
      rw [←hq]
      exact le_iSup (fun r : {r : P // imageCondition r ≤ imageCondition p ⊓ M.embed b} => M.mask r.val)
        ⟨q,le_inf (imageCondition_mono_r50 hqp)
        (M.image_le q b (hq.trans_le inf_le_right))⟩

theorem MaskRealization.projectedRowCCC_iff (M : MaskRealization B P) :
    ProjectedRowCCC M.mask (fun p q => ∃ r, r≤p ∧ r≤q) ↔ ProjectedAntichainCCC M.project := by
  classical
  constructor
  · intro h v hDisj
    let W (i : OmegaOneIndex) (p : P) := if imageCondition p ≤ v i then M.mask p else ⊥
    have hWM (i p) : W i p ≤ M.mask p := by
      unfold W
      split
      · exact le_rfl
      · exact bot_le
    have hWsep (i j) (hij : i<j) (p q : P) (hPQ : ∃ r, r≤p ∧ r≤q) :
        Disjoint (W i p) (W j q) := by
      by_cases hp : imageCondition p≤v i
      · by_cases hq : imageCondition q≤v j
        · obtain ⟨r,hrp,hrq⟩ := hPQ
          exact False.elim (imageCondition_ne_bot_r50 r
            ((hDisj i j hij).out _ ((imageCondition_mono_r50 hrp).trans hp)
              ((imageCondition_mono_r50 hrq).trans hq)))
        · simp [W,hq]
      · simp [W,hp]
    have hRows (i : OmegaOneIndex) : (⨆ p,W i p) = M.project (v i) := by
      apply le_antisymm
      · apply iSup_le
        intro p
        unfold W
        split
        · rename_i hp
          exact le_iSup (fun q : {q : P // imageCondition q ≤ v i} => M.mask q.val) ⟨p,hp⟩
        · exact bot_le
      · apply iSup_le
        intro p
        exact le_iSup_of_le p.val (by simp [W,p.property])
    have hh := h W hWM hWsep
    simpa only [hRows] using hh
  · intro h W hWM hSep
    let x (i : OmegaOneIndex) := ⨆ p, imageCondition p ⊓ M.embed (W i p)
    have hx (i j) (hij : i<j) : Disjoint (x i) (x j) := by
      apply disjoint_iff_inf_le.mpr
      simp only [x,iSup_inf_iSup]
      apply iSup_le
      rintro ⟨p,q⟩
      apply disjoint_iff_inf_le.mp
      by_cases hc : ∃ r, r≤p ∧ r≤q
      · exact (M.embed_disjoint (hSep i j hij p q hc)).mono inf_le_right inf_le_right
      · have hd : Disjoint (imageCondition p) (imageCondition q) := by
          by_contra hn
          exact hc ((compatible_iff_not_disjoint_r50 p q).mpr hn)
        exact hd.mono inf_le_left inf_le_left
    have hRows (i : OmegaOneIndex) : M.project (x i) = ⨆ p,W i p := by
      unfold x
      rw [M.project_gc.l_iSup]
      congr 1
      funext p
      rw [M.project_trace_cut,inf_eq_right.mpr (hWM i p)]
    have hh := h x hx
    simpa only [hRows] using hh

end ForcingTransport
end JSP000933
