import JSP000933ActualDyadicHybridRegular

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem LocalEq.xor_congr_r346 {h : Bool} {p : B} {a b c d : ℕ → B}
    (ha : LocalEq h p a b) (hc : LocalEq h p c d) :
    LocalEq h p (bitsSymmDiff a c) (bitsSymmDiff b d) := by
  unfold bitsSymmDiff
  exact (ha.meet_congr_r239 hc.compl_congr_r239).join_congr_r239 (ha.compl_congr_r239.meet_congr_r239 hc)

theorem actualRegularExact_to_continuous_r346 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (f : (ℕ → B) → ℕ → B) (hR : NamedRegularOn p f)
    (hApp : ∀ x, LocalEq true p (f x) (F.toName (bitsMeet c x))) :
    ∃ L : (ℕ → B) → ℕ → B, NamedContinuousOn p L ∧
      ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)) := by
  obtain ⟨P,hP⟩ := exists_actualComplementarySections_r296 hR.code p hR.dense
  let I := F.restrict_r246 (show p≤p from le_rfl)
  let bFace (b : Bool) := actualCoordinateFace c P b
  let g (b : Bool) (x : ℕ → B) :=
    bitsMeet (F.toName (bFace b)) (f (actualSectionPoint P b x))
  have hG (b : Bool) : NamedContinuousOn p (g b) :=
    (hR.onSection_continuous_r320 P b (fun x => le_iInf (fun n => hP n b x))).meet_fixed_r297 (F.toName (bFace b))
  refine ⟨fun x => bitsSymmDiff (g false x) (g true x),(hG false).xor_r297 (hG true),?_⟩
  intro x
  have hSides (b : Bool) : LocalEq true p (g b x) (F.toName (bitsMeet (bFace b) x)) := by
    let a := bFace b
    let z := actualSectionPoint P b x
    let y := bitsMeet c z
    let H := bitsMeet (F.toName a) (F.toName y)
    let Y := F.toName (bitsMeet a x)
    have hEq : LocalEq true p Y H := by
      have he := I.mapMeet_r237 a y
      change LocalEq true p (F.toName (bitsMeet a y)) H at he
      have hPayload : bitsMeet a y = bitsMeet a x := actualFace_section_payload_r298 c P x b
      rw [hPayload] at he
      exact he
    have hG' : LocalEq true p (g b x) H :=
      (LocalEq.refl_r239 true p (F.toName a)).meet_congr_r239 (hApp z)
    exact hG'.trans_r236 hEq.symm_r236
  let u := bitsMeet (bFace false) x
  let v := bitsMeet (bFace true) x
  let W := bitsSymmDiff (F.toName u) (F.toName v)
  let Y := F.toName (bitsMeet c x)
  have hEq : LocalEq true p Y W := by
    have h := I.mapSymmDiff_r239 u v
    change LocalEq true p (F.toName (bitsSymmDiff u v)) W at h
    have hPayload : bitsSymmDiff u v = bitsMeet c x := actualFaces_payload_xor_r298 c P x
    rw [hPayload] at h
    exact h
  exact ((hSides false).xor_congr_r346 (hSides true)).trans_r236 hEq.symm_r236

theorem exists_actualWholeBlock_continuousLift_r346 (G : bSet B) {p : B}
    (F : CoherentSelectedIso B p) (hExt : NameMapExt F.toName)
    (hOCA : p≤namedCantorOCAValue B) (hG : p≤actualPreserveReflectValue G)
    (hGraph : ∀ x, p≤graphPairBits G false x (F.toName x)) :
    ∃ (a : ℕ → B) (L : (ℕ → B) → ℕ → B), p≤actualLongBlockLarge a ∧
      NamedContinuousOn p L ∧ ∀ x, LocalEq true p (L x) (F.toName (bitsMeet a x)) := by
  have hk (j : ℕ) : dyadicApproxDen j≠0 := Nat.ne_of_gt (dyadicApproxDen_pos_r335 j)
  let K (j : ℕ) := 64*(2*dyadicApproxDen j)
  have hK (j : ℕ) : K j≠0 := Nat.mul_ne_zero (by decide) (Nat.mul_ne_zero (by decide) (hk j))
  obtain ⟨c,hC,⟨A⟩⟩ := exists_sameBranch_actualContinuousApprox_r300 G K hK F hOCA hG hGraph
  obtain ⟨a,_,hA,hUniform⟩ := exists_sameCap_namedUniformAll_r334 F hExt c dyadicApproxDen hk A (le_top.trans hC)
  let R := fun x => F.toName (bitsMeet a x)
  have hE (j : ℕ) : ∃ f : (ℕ → B) → ℕ → B, NamedContinuousOn p f ∧
      p≤uniformTailErrorValue F.toName a (dyadicApproxDen j) f :=
    existsNamedUniformValue_elim_r313 F.toName a (dyadicApproxDen j) (hUniform j)
  choose f hF hM using hE
  have hM' (j : ℕ) (x : ℕ → B) : p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x) :=
    (hM j).trans (iInf_le _ x)
  obtain ⟨hReg⟩ := actualHybrid_regular_r345 f hF
  obtain ⟨L,hL,hLift⟩ := actualRegularExact_to_continuous_r346 F a (actualHybridBit f) hReg
    (actualHybrid_harmEq_representative_r344 f R hM')
  exact ⟨a,L,hA,hL,hLift⟩

end SetLanguage
end JSP000933
