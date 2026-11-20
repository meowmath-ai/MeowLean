import JSP000933ActualClosedIndexRegularSelector

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem robustGoodTails_has_regularApprox_r320 {p : B} {H : (ℕ → B) → (ℕ → B) → ℕ → B}
    (hH : NamedTwoArgContinuous p H) (R : (ℕ → B) → ℕ → B) (k : ℕ)
    (hGood : ∀ x, p≤robustGoodTails (goodTailCodesAt H R (4*k) x)) :
    ∃ f : (ℕ → B) → ℕ → B, Nonempty (NamedRegularOn p f) ∧
      ∀ x, p≤eventuallySmallError true k (f x) (R x) := by
  let d (i : ℕ) := (Encodable.decode (α := ℕ × Word) i).getD (0,[])
  let V (x : ℕ → B) (i : ℕ) := anchorGapClosedValue H (2*k) (d i).2 (d i).1 x
  let K (i : ℕ) : Word → B := anchorGapBadCode H (2*k) (d i).2 (d i).1
  let f (i : ℕ) (x : ℕ → B) := H x (paddedWordBits (d i).2)
  have hCov (x : ℕ → B) : p≤⨆ i, V x i := by
    apply (robustGoodTail_anchorCover_r316 hH R k x (hGood x)).trans
    apply iSup_le
    intro Nu
    apply le_iSup_of_le (Encodable.encode Nu)
    unfold V d
    rw [Encodable.encodek]
    exact le_rfl
  have hK (x : ℕ → B) (i : ℕ) : p⊓openValue (K i) x=p⊓(V x i)ᶜ :=
    anchorGapBadCode_mask_r315 hH (2*k) (d i).1 (d i).2 x
  have hEach (x : ℕ → B) (i : ℕ) : p⊓V x i≤eventuallySmallError true k (f i x) (R x) :=
    robustGoodTail_anchorGood_r316 hH R k (d i).1 (d i).2 x inf_le_left
      (inf_le_left.trans (hGood x)) inf_le_right
  exact ⟨firstNamedIndexOutput V f,firstNamedIndexOutput_regular_r319 p V K f hK
      (fun i => hH.1 (paddedWordBits (d i).2)) hCov,
    fun x => firstNamedIndexOutput_tail_r317 V f R k x (hCov x) (hEach x)⟩

theorem NamedRegularOn.onSection_continuous_r320 {p : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedRegularOn p f) (P : ℕ → B) (b : Bool)
    (hReg : ∀ x, p≤⨅ n : ℕ, openValue (h.code n) (actualSectionPoint P b x)) :
    NamedContinuousOn p (fun x => f (actualSectionPoint P b x)) := by
  intro x N q hq hqp
  let z := actualSectionPoint P b x
  obtain ⟨r,u,hr,hrq,hR,hSame⟩ := h.localAt z N q hq hqp (hqp.trans (hReg x))
  obtain ⟨v,hv,t,ht,htr,hT⟩ := exists_decided_initialWord_r136 x u.length r hr
  refine ⟨t,v,ht,htr.trans hrq,hT,?_⟩
  intro y s hst hS
  let w := actualSectionPoint P b y
  have hz : s≤cylinderValue z u := hst.trans (htr.trans hR)
  have hV : ∀ m<u.length, s⊓z m=s⊓w m := fun m hm =>
    actualSectionPoint_samePrefix_r297 P x y b v (hst.trans hT) hS m (hv.symm ▸ hm)
  have he := mask_cylinder_bounded_r278 u hV
  have hw : s≤cylinderValue w u := ((le_inf le_rfl hz).trans_eq he).trans inf_le_right
  exact hSame w s (hst.trans htr) hw

end SetLanguage
end JSP000933
