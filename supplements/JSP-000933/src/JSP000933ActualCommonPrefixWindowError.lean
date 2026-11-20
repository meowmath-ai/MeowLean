import JSP000933ActualMixedStageTrim

open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_joint_crispPrefix_r362 (a b : ℕ → B) (n : ℕ) (p : B) (hp : p≠⊥) :
    ∃ (A C : Set ℕ) (q : B), q≠⊥ ∧ q≤p ∧
      (∀ m<n, q⊓a m=q⊓crispTruth B (m∈A)) ∧ (∀ m<n, q⊓b m=q⊓crispTruth B (m∈C)) := by
  obtain ⟨A,C,q,hq,hqp,hA,hC⟩ := exists_joint_ground_prefix_r211 (realBitsName a) (realBitsName b) n p hp
  have hG (u : ℕ → B) (U : Set ℕ)
      (h : ∀ m<n, q⊓membershipBits (realBitsName u) m=q⊓membershipBits (groundSubsetName B U) m) :
      ∀ m<n, q⊓u m=q⊓crispTruth B (m∈U) := by
    intro m hm
    have he := h m hm
    rw [membershipBits_realBitsName_r128] at he
    change q⊓u m=q⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B U) at he
    rw [checkedNat_ground_mem_r197] at he
    exact he
  exact ⟨A,C,q,hq,hqp,hG a A hA,hG b C hC⟩

theorem nameBits_window_prefix_r362 {q : B} {a : ℕ → B} {A : Set ℕ} (n : ℕ)
    (hA : ∀ m<n, q⊓a m=q⊓crispTruth B (m∈A))
    {N : ℕ} (H : ActualStageHistory N) (k : ℕ) :
    ∀ m<n, q⊓bitsMeet (crispStageWindow H k) a m=
      q⊓crispTruth B (m∈((groundStageWindow H k : Set ℕ) ∩ A)) := by
  intro m hm
  exact (mask_inf_congr_r126 (show q⊓crispStageWindow H k m=q⊓crispStageWindow H k m from rfl) (hA m hm)).trans
    (congrArg (fun u : B => q⊓u) (crisp_and_r190 _ _).symm)

theorem xor_inter_slice_r362 (A C D : Set ℕ) :
    xorSet (D∩A) (D∩C)=xorSet A C∩D := by
  ext m
  simp only [xorSet,Set.mem_inter_iff,Set.mem_union,Set.mem_sdiff]
  tauto

theorem actualTrim_raw_local_window_r362 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N)
    (hH : (T.level N).weight H≠⊥) (hq : q≤(T.level N).weight H) (x : ℕ → B)
    (J k m : ℕ) (hJk : J≤k) (hk : k+1<N) (hm : m+2≤N) :
    q⊓bitsMeet (crispStageWindow H k) (bitsMeet (actualAfterStageOut T J) (actualRawOutput T x)) m=
      q⊓bitsMeet (crispStageWindow H k) (L (actualLocalRawInput T H k x)) m := by
  refine (actualTrim_window_mask_r361 T H hq hH J k m hJk hk (actualRawOutput T x)).trans ?_
  by_cases hM : m∈groundStageWindow H k
  · exact mask_inf_congr_r126 rfl (mask_under_r302 hq
      (actualRawOutput_window_mask_r358 T H hH x k m hm hk hM))
  · simp [bitsMeet,crispStageWindow,crispTruth,hM]

theorem actualTrim_groundWindow_error_r362 {p q : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) {N : ℕ} (H : ActualStageHistory N)
    (hH : (T.level N).weight H≠⊥) (hq : q≤(T.level N).weight H) (hq0 : q≠⊥)
    (x : ℕ → B) (hX : q≤bitsBelowValue x (actualSourceUnion T))
    (J k n : ℕ) (hJk : J≤k) (hk : k+1<N) (hn : n+1≤N) {A C : Set ℕ}
    (hA : ∀ m<n, q⊓bitsMeet (actualAfterStageOut T J) (L (actualPaddedInput T x)) m=q⊓crispTruth B (m∈A))
    (hC : ∀ m<n, q⊓bitsMeet (actualAfterStageOut T J) (actualRawOutput T x) m=q⊓crispTruth B (m∈C)) :
    GroundBudgetHolds true (xorSet A C∩(groundStageWindow H k : Set ℕ)) ∅ (dyadicGapDen k) n := by
  have hA' := nameBits_window_prefix_r362 n hA H k
  have hC' := nameBits_window_prefix_r362 n hC H k
  have hV := actualRawWindow_errorBudget_r360 T H hH hq x hX k n hk
  have hDA (m : ℕ) (hm : m<n) :
      q⊓bitsMeet (crispStageWindow H k) (L (actualPaddedInput T x)) m=
        q⊓crispTruth B (m∈((groundStageWindow H k : Set ℕ)∩A)) :=
    (actualTrim_window_mask_r361 T H hq hH J k m hJk hk _).symm.trans (hA' m hm)
  have hDC (m : ℕ) (hm : m<n) :
      q⊓bitsMeet (crispStageWindow H k) (L (actualLocalRawInput T H k x)) m=
        q⊓crispTruth B (m∈((groundStageWindow H k : Set ℕ)∩C)) :=
    (actualTrim_raw_local_window_r362 T H hH hq x J k m hJk hk (by omega)).symm.trans (hC' m hm)
  have h := nameErrorBudget_crispPrefix_sound_r340 true (dyadicGapDen k) n hq0 hDA hDC hV
  rwa [xor_inter_slice_r362] at h

end SetLanguage
end JSP000933
