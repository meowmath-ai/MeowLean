import JSP000933NameScheduleCoherence

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

variable {N : OmegaTwoIndex → Type} {R : Rules N}

noncomputable def liftBitsToWhole (a : OmegaTwoIndex) (v : ℕ → RO (Before R a)) : ℕ → RO (Condition R) :=
  fun n => (wholeReduction a).boolPullback (v n)

noncomputable def canonicalStageDecode (code : OmegaTwoIndex × OmegaOneIndex ↪ OmegaTwoIndex)
    (e : (a : OmegaTwoIndex) → OmegaOneIndex → ℕ → RO (Before R a))
    (a : OmegaTwoIndex) (j : OmegaTwoIndex) : ℕ → RO (Before R a) := by
  classical
  exact if h : ∃ q : {q : OmegaTwoIndex × OmegaOneIndex // q.1 < a}, code q.1 = j then
      fun n => (prefixReduction (Classical.choose h).2.le).boolPullback
        (e (Classical.choose h).1.1 (Classical.choose h).1.2 n)
    else fun _ => ⊥

structure ReflectingNameSchedule (R : Rules N) where
  enumerate : OmegaTwoIndex → ℕ → RO (Condition R)
  code : OmegaTwoIndex × OmegaOneIndex ↪ OmegaTwoIndex
  stageEnumerate : (a : OmegaTwoIndex) → OmegaOneIndex → ℕ → RO (Before R a)
  onto : Function.Surjective enumerate
  club : Set OmegaTwoIndex
  guard : OmegaTwoIndex → OmegaTwoIndex
  club_eq : club = stageClosedUnder guard
  isClub : OrdinalClub club
  localDecode_agrees : ∀ a ∈ club, ∀ j < a,
    liftBitsToWhole a (canonicalStageDecode code stageEnumerate a j) = enumerate j
  entry_for_every_local : ∀ a ∈ club, (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof →
    ∀ v : ℕ → RO (Before R a), ∃ j < a, enumerate j = liftBitsToWhole a v

theorem exists_reflectingNameSchedule_r111
    (hCCC : HasCountableAntichains (Condition R))
    (hBefore : ∀ a, HasCountableAntichains (Before R a))
    (hStage : ∀ a : OmegaTwoIndex, ∃ e : OmegaOneIndex → ℕ → RO (Before R a),
      Function.Surjective e) :
    Nonempty (ReflectingNameSchedule R) := by
  classical
  obtain ⟨code⟩ := exists_pairStageNameCode_r110
  choose e he using hStage
  let allNames (q : OmegaTwoIndex × OmegaOneIndex) := liftBitsToWhole q.1 (e q.1 q.2)
  let E (j : OmegaTwoIndex) : ℕ → RO (Condition R) :=
    if hj : ∃ q, code q = j then allNames (Classical.choose hj) else fun _ => ⊥
  have hPacked (q : OmegaTwoIndex × OmegaOneIndex) : E (code q) = allNames q := by
    have hh : ∃ r, code r = code q := ⟨q,rfl⟩
    have heq := code.injective (Classical.choose_spec hh)
    simp only [E,dite_eq_left hh,heq]
  have hOnto (v : ℕ → RO (Condition R)) : ∃ j, E j = v := by
    obtain ⟨a,w,hw⟩ := exists_properStage_for_countable_values_r101 hCCC v
    obtain ⟨i,hi⟩ := he a w
    exact ⟨code (a,i),(hPacked (a,i)).trans (funext (fun n => by simpa only [allNames,liftBitsToWhole,hi] using hw n))⟩
  let sourceStage (j : OmegaTwoIndex) : OmegaTwoIndex :=
    if h : ∃ q, code q = j then (Classical.choose h).1 else j
  choose cap hCap using exists_stagePairCodes_bounded_r110 code
  let cl (j : OmegaTwoIndex) := max (sourceStage j) (cap j)
  let C := stageClosedUnder cl
  refine ⟨⟨E,code,e,hOnto,C,cl,rfl,stageClosedUnder_isClub_r108 cl,?_,?_⟩⟩
  · intro a ha j hj
    by_cases h : ∃ q, code q = j
    · have hs : (Classical.choose h).1 < a := by
        have hh : sourceStage j < a := (le_max_left _ _).trans_lt (ha j hj)
        simpa only [sourceStage,dite_eq_left h] using hh
      have hl : ∃ q : {q : OmegaTwoIndex × OmegaOneIndex // q.1 < a}, code q.1 = j :=
        ⟨⟨Classical.choose h,hs⟩,Classical.choose_spec h⟩
      have heq : (Classical.choose hl).1 = Classical.choose h :=
        code.injective ((Classical.choose_spec hl).trans (Classical.choose_spec h).symm)
      funext n
      simp only [liftBitsToWhole,canonicalStageDecode,dite_eq_left hl,E,dite_eq_left h]
      rw [wholeReduction_coherent_r110,heq] <;> rfl
    · have hl : ¬ ∃ q : {q : OmegaTwoIndex × OmegaOneIndex // q.1 < a}, code q.1 = j :=
        fun h' => h ⟨(Classical.choose h').1,Classical.choose_spec h'⟩
      funext n
      simp only [liftBitsToWhole,canonicalStageDecode,dite_eq_right hl,E,dite_eq_right h,
        RestrictionMap.boolPullback_bot_r91]
  · intro a ha hcf v
    obtain ⟨b,hba,w,hw⟩ := exists_earlierStage_for_countable_values_r109 a hcf (hBefore a) v
    obtain ⟨i,hi⟩ := he b w
    have hj : code (b,i) < a :=
      (hCap b i).trans ((le_max_right _ _).trans_lt (ha b hba))
    refine ⟨code (b,i),hj,(hPacked (b,i)).trans ?_⟩
    funext n
    calc
      allNames (b,i) n = (wholeReduction b).boolPullback (w n) := by simp only [allNames,liftBitsToWhole,hi]
      _ = (wholeReduction a).boolPullback ((prefixReduction hba.le).boolPullback (w n)) :=
        (wholeReduction_coherent_r110 hba.le (w n)).symm
      _ = liftBitsToWhole a v n := by rw [hw n] <;> rfl

end FiniteSupport
end JSP000933
