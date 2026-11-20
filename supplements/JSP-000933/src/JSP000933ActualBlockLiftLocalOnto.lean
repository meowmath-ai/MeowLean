import JSP000933ActualNormalizedBlockLift

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem maskedMeetAbsorb_r365 {q : B} {x D : ℕ → B} (h : q≤bitsBelowValue x D) :
    q≤realEqValue (bitsMeet D x) x := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  change q⊓(D m⊓x m)=q⊓x m
  calc
    q⊓(D m⊓x m)=(q⊓x m)⊓D m := by ac_rfl
    _=q⊓x m := inf_eq_left.mpr (bitsBelowValue_apply_r256 h m)

theorem actualClampedOutput_fullSource_r365 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : actualClampedOutput T (actualSourceUnion T)=actualBlockClamp T := by
  funext m
  simp only [actualClampedOutput,actualBlockClamp,bitsMeet,← inf_assoc,inf_idem]

theorem actualClampedOutput_onto_range_r365 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (y : ℕ → B) (hy : p≤bitsBelowValue y (actualBlockClamp T)) :
    ∃ x : ℕ → B, p≤bitsBelowValue x (actualSourceUnion T) ∧ LocalEq true p (actualClampedOutput T x) y := by
  let I := F.restrict_r246 (show p≤p from le_rfl)
  let D := actualSourceUnion T
  let X := bitsMeet D (F.invName y)
  have hX : p≤bitsBelowValue X D := bitsBelowValue_of_pointwise_r272 (fun _ => inf_le_left)
  refine ⟨X,hX,(actualClampedOutput_harmEq_r364 F T hL X hX).trans_r236 ?_⟩
  have hS : LocalEq true p (F.toName D) (actualBlockClamp T) :=
    (actualBlockClamp_harmEq_r364 F T hL).symm_r236
  have hY : LocalEq true p (F.toName (F.invName y)) y := (F.inv_har y).symm_r236
  exact (I.mapMeet_r237 D (F.invName y)).trans_r236
    ((hS.meet_congr_r239 hY).trans_r236 (LocalEq.of_realEq_r246 true (maskedMeetAbsorb_r365 hy)))

theorem actualClampedOutput_local_r365 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (hL : NamedContinuousOn p L)
    {n : ℕ} (A : ActualStageHistory n) (hq : q≤(T.level n).weight A)
    (x y : ℕ → B) (k m : ℕ) (hk : k+1<n) (hM : m∈groundStageWindow A k)
    (he : ∀ i∈justSourceBlock (historyStage A k).position, q⊓x i=q⊓y i) :
    q⊓actualClampedOutput T x m=q⊓actualClampedOutput T y m := by
  have hx : q≤realEqValue (actualLocalRawInput T A k x) (actualLocalRawInput T A k y) := by
    apply (le_realEqValue_iff_r126 _ _ _).mpr
    intro i
    by_cases hi : i∈justSourceBlock (historyStage A k).position
    · exact mask_sup_congr_r211 rfl (mask_inf_congr_r126 rfl (he i hi))
    · simp [actualLocalRawInput,actualPaddedInput,bitsJoin,bitsMeet,crispStageSource,crispTruth,hi]
  have hqP := hq.trans ((T.level n).weight_le_r215 A)
  have hO := (le_realEqValue_iff_r126 _ _ _).mp (hL.realEq_mask_r323 hqP hx)
  have hRaw : q⊓actualRawOutput T x m=q⊓actualRawOutput T y m := by
    apply (le_bitEq_iff_r126 _ _ _).mp
    apply le_of_dense_named_refinements_r219
    intro s hs hsq
    let N := max n (m+2)
    obtain ⟨H,r,hr,hrs,hrH,hE⟩ := T.exists_larger_snapshot_r357 (le_max_left n (m+2)) A hs (hsq.trans hq)
    have hV : (T.level N).weight H≠⊥ := fun hh => hr (le_bot_iff.mp (hrH.trans_eq hh))
    have hk' : k+1<N := hk.trans_le (le_max_left _ _)
    have hm : m+2≤N := le_max_right _ _
    have hK := hE k (by omega)
    have hW : m∈groundStageWindow H k := by
      simpa only [groundStageWindow,hK,hE (k+1) hk] using hM
    have hX := mask_under_r302 hrH (actualRawOutput_window_mask_r358 T H hV x k m hm hk' hW)
    have hY := mask_under_r302 hrH (actualRawOutput_window_mask_r358 T H hV y k m hm hk' hW)
    have hXY := mask_under_r302 (hrs.trans hsq) (hO m)
    have hArg (z : ℕ → B) : actualLocalRawInput T H k z=actualLocalRawInput T A k z := by
      funext i
      simp only [actualLocalRawInput,actualPaddedInput,bitsJoin,bitsMeet,crispStageSource,hK]
    rw [hArg x] at hX
    rw [hArg y] at hY
    exact ⟨r,hr,hrs,(le_bitEq_iff_r126 _ _ _).mpr (hX.trans (hXY.trans hY.symm))⟩
  exact mask_inf_congr_r126 hRaw rfl

end SetLanguage
end JSP000933
