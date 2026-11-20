import JSP000933ActualScheduledPolicy

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion MarkedForcing FiniteSupport RelativeOCA OpenGraphForcing

variable {B P N : Type} [CompleteBooleanAlgebra B] [Preorder P]
  [Preorder N] [OrderTop N]

structure TailPresentation (M : MaskRealization B P) where
  strip : P → N
  mono_strip : Monotone strip
  empty : P
  empty_mask : M.mask empty = ⊤
  empty_strip : strip empty = ⊤
  replace : ∀ p b, b ≠ ⊥ → b ≤ M.mask p → P
  replace_mask : ∀ p b hb hpb, M.mask (replace p b hb hpb) = b
  replace_strip : ∀ p b hb hpb, strip (replace p b hb hpb) = strip p
  replace_le_of : ∀ p q b hb hpb, b ≤ M.mask q → strip p ≤ strip q → replace p b hb hpb ≤ q

namespace TailPresentation
variable {M : MaskRealization B P} (S : TailPresentation (N := N) M)

noncomputable def valid (n : N) : B :=
  ⨆ p : {p : P // S.strip p=n}, M.mask p.val

theorem mask_le_valid (p : P) : M.mask p ≤ S.valid (S.strip p) :=
  le_iSup (fun a : {a : P // S.strip a = S.strip p} => M.mask a.val) ⟨p,rfl⟩

theorem valid_top : S.valid ⊤ = ⊤ := by
  apply top_unique
  exact S.empty_mask.symm.trans_le (S.empty_strip ▸ S.mask_le_valid S.empty)

open scoped Classical in
noncomputable def quotient : ValuedPoset B N where
  valid := S.valid
  refines n m := if n≤ m then S.valid n ⊓ S.valid m else ⊥
  refine_valid n m := by by_cases h : n≤ m <;> simp [h]
  refl n := by simp
  trans n m k := by
    by_cases hnm : n≤ m
    · by_cases hmk : m≤k
      · simp only [ite_eq_left hnm,ite_eq_left hmk,ite_eq_left (hnm.trans hmk)]
        exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
      · simp only [ite_eq_right hmk,inf_bot_eq,bot_le]
    · simp only [ite_eq_right hnm,bot_inf_eq,bot_le]
  weakest := ⊤
  weakest_valid := S.valid_top
  weaker n := by simp [S.valid_top]

noncomputable def map (p : P) : TotalCondition S.quotient :=
  ⟨M.mask p,S.strip p,M.positive p,S.mask_le_valid p⟩

theorem map_mono : Monotone S.map := by
  classical
  intro p q hpq
  refine ⟨M.monotone hpq,?_⟩
  change M.mask p ≤ if S.strip p≤S.strip q then
    S.valid (S.strip p) ⊓ S.valid (S.strip q) else ⊥
  rw [ite_eq_left (S.mono_strip hpq)]
  exact le_inf (S.mask_le_valid p) ((M.monotone hpq).trans (S.mask_le_valid q))

theorem chosen_refines_iff {p q : TotalCondition S.quotient} :
    p≤q ↔ p.mask≤q.mask ∧ p.trace≤q.trace := by
  classical
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    by_contra hn
    have hh := h.2
    change p.mask ≤ if p.trace≤q.trace then S.valid p.trace ⊓ S.valid q.trace else ⊥ at hh
    rw [ite_eq_right hn] at hh
    exact p.nonzero (le_bot_iff.mp hh)
  · rintro ⟨h,hTrace⟩
    refine ⟨h,?_⟩
    change p.mask ≤ if p.trace≤q.trace then S.valid p.trace ⊓ S.valid q.trace else ⊥
    rw [ite_eq_left hTrace]
    exact le_inf p.valid (h.trans q.valid)

theorem positive_tail_witness (r : TotalCondition S.quotient) :
    ∃ p : P, S.strip p=r.trace ∧ M.mask p⊓r.mask≠⊥ := by
  by_contra h
  have hz (p : {p : P // S.strip p=r.trace}) : M.mask p.val⊓r.mask=⊥ := by
    by_contra hp
    exact h ⟨p.val,p.property,hp⟩
  have h0 : S.valid r.trace⊓r.mask = ⊥ := by
    unfold valid
    rw [iSup_inf_eq]
    simp only [hz,iSup_bot]
  exact r.nonzero (le_bot_iff.mp ((le_inf r.valid le_rfl).trans_eq h0))

theorem map_dense (r : TotalCondition S.quotient) : ∃ p, S.map p≤r := by
  obtain ⟨p,hp,hPos⟩ := S.positive_tail_witness r
  let b := M.mask p⊓r.mask
  let q := S.replace p b hPos inf_le_left
  refine ⟨q,S.chosen_refines_iff.mpr ?_⟩
  change M.mask q≤r.mask ∧ S.strip q≤r.trace
  exact ⟨(S.replace_mask p b hPos inf_le_left).trans_le inf_le_right,
    ((S.replace_strip p b hPos inf_le_left).trans hp).le⟩

theorem map_compat_reflect {p q : P} (h : Compatible (S.map p) (S.map q)) :
    Compatible p q := by
  obtain ⟨r,hrp,hrq⟩ := h
  obtain ⟨u,hu,hPos⟩ := S.positive_tail_witness r
  have hp := S.chosen_refines_iff.mp hrp
  have hq := S.chosen_refines_iff.mp hrq
  let b := M.mask u⊓r.mask
  refine ⟨S.replace u b hPos inf_le_left,?_ ,?_⟩
  · exact S.replace_le_of u p b hPos inf_le_left (inf_le_right.trans hp.1) (hu.trans_le hp.2)
  · exact S.replace_le_of u q b hPos inf_le_left (inf_le_right.trans hq.1) (hu.trans_le hq.2)

noncomputable def denseMap : DenseForcingMap P (TotalCondition S.quotient) :=
  ⟨S.map,S.map_mono,S.map_dense,S.map_compat_reflect⟩

theorem quotient_base_coherent (b : B) :
    S.denseMap.pullIso (baseEmbed S.quotient b) = M.embed b := by
  have htest (p : P) :
      imageCondition p ≤ S.denseMap.pullIso (baseEmbed S.quotient b) ↔ imageCondition p ≤ M.embed b := by
    rw [image_le_iff_member]
    change S.map p ∈ (baseEmbed S.quotient b : LowerSet (TotalCondition S.quotient)) ↔ _
    rw [←image_le_iff_member,baseEmbed_reflects_mask_r427,MaskRealization.image_le_iff] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (htest p).mp))
    (le_of_image_tests (fun p => (htest p).mpr))

end TailPresentation
end ForcingTransport
end JSP000933
