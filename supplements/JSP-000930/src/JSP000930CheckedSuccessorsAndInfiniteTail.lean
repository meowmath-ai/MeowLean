import JSP000930MaskedPredensityTelescope
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace JSP000930.Negative

open JSP000933.PreparedModel
open Cardinal
open scoped Cardinal Ordinal

private theorem groundKappaAleph0Lt930 : ℵ₀ < GroundContinuumSucc :=
  Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ _)

noncomputable def wetzelIndexOfOrdinal (o : Ordinal) (ho : o < GroundContinuumSucc.ord) :
    GroundContinuumSuccIndex := Ordinal.ToType.mk ⟨o,ho⟩

theorem continuumSuccOrdinal_wetzelIndexOfOrdinal (o : Ordinal)
    (ho : o < GroundContinuumSucc.ord) :
    continuumSuccOrdinal (wetzelIndexOfOrdinal o ho) = o := by
  unfold continuumSuccOrdinal wetzelIndexOfOrdinal
  rw [OrderIso.symm_apply_apply]

theorem continuumSuccOrdinal_lt_iff930 (i j : GroundContinuumSuccIndex) :
    continuumSuccOrdinal i < continuumSuccOrdinal j ↔ i < j := by
  change (Ordinal.ToType.mk (o := GroundContinuumSucc.ord)).symm i <
    (Ordinal.ToType.mk (o := GroundContinuumSucc.ord)).symm j ↔ _
  exact OrderIso.lt_iff_lt _

theorem continuumSuccOrdinal_le_iff930 (i j : GroundContinuumSuccIndex) :
    continuumSuccOrdinal i ≤ continuumSuccOrdinal j ↔ i ≤ j := by
  rw [← not_lt,← not_lt,continuumSuccOrdinal_lt_iff930]

private theorem groundNextOrdinal_lt (i : GroundContinuumSuccIndex) :
    continuumSuccOrdinal i + 1 < GroundContinuumSucc.ord := by
  apply Cardinal.lt_ord.mpr
  rw [Ordinal.card_add_one]
  exact Cardinal.add_one_lt_of_lt groundKappaAleph0Lt930.le
    (Cardinal.lt_ord.mp (continuumSuccOrdinal_lt_r392 i))

noncomputable def wetzelGroundNext (i : GroundContinuumSuccIndex) : GroundContinuumSuccIndex :=
  wetzelIndexOfOrdinal (continuumSuccOrdinal i + 1) (groundNextOrdinal_lt i)

theorem wetzelGroundNext_spec (i j : GroundContinuumSuccIndex) :
    j < wetzelGroundNext i ↔ j ≤ i := by
  rw [← continuumSuccOrdinal_lt_iff930,wetzelGroundNext,continuumSuccOrdinal_wetzelIndexOfOrdinal,
    Order.lt_add_one_iff,continuumSuccOrdinal_le_iff930]

theorem wetzelWork_next (a : GroundContinuumSuccIndex) (i : WetzelStageIndex) :
    i < wetzelWorkStage (wetzelGroundNext a) ↔ i ≤ wetzelWorkStage a := by
  cases i with
  | none => exact ⟨fun _ => bot_le,fun _ => wetzel_bot_lt_work _⟩
  | some i =>
    cases i with
    | bot => exact ⟨fun _ => (wetzelBulk_lt_work _).le,fun _ => wetzelBulk_lt_work _⟩
    | coe i =>
      change wetzelWorkStage i < wetzelWorkStage (wetzelGroundNext a) ↔
        wetzelWorkStage i ≤ wetzelWorkStage a
      rw [wetzelWorkStage_lt_iff,wetzelWorkStage_le_iff,wetzelGroundNext_spec]

theorem wetzelGroundNext_le_of_lt {a b : GroundContinuumSuccIndex} (h : a<b) :
    wetzelGroundNext a ≤ b := by
  by_contra hn
  have hb := (wetzelGroundNext_spec a b).mp (lt_of_not_ge hn)
  exact h.not_ge hb

private theorem groundInfiniteTail_lt (i : GroundContinuumSuccIndex) :
    Ordinal.omega0 + continuumSuccOrdinal i < GroundContinuumSucc.ord := by
  apply Cardinal.lt_ord.mpr
  rw [Ordinal.card_add,Ordinal.card_omega0]
  exact Cardinal.add_lt_of_lt groundKappaAleph0Lt930.le groundKappaAleph0Lt930
    (Cardinal.lt_ord.mp (continuumSuccOrdinal_lt_r392 i))

noncomputable def wetzelFunctionStage (i : GroundContinuumSuccIndex) : GroundContinuumSuccIndex :=
  wetzelIndexOfOrdinal (Ordinal.omega0 + continuumSuccOrdinal i) (groundInfiniteTail_lt i)

theorem wetzelFunctionStage_strictMono : StrictMono wetzelFunctionStage := by
  intro i j hij
  apply (continuumSuccOrdinal_lt_iff930 _ _).mp
  simp only [wetzelFunctionStage,continuumSuccOrdinal_wetzelIndexOfOrdinal]
  have h := (continuumSuccOrdinal_lt_iff930 _ _).mpr hij
  exact add_lt_add_right h Ordinal.omega0

theorem le_wetzelFunctionStage (i : GroundContinuumSuccIndex) : i ≤ wetzelFunctionStage i := by
  apply (continuumSuccOrdinal_le_iff930 _ _).mp
  simp only [wetzelFunctionStage,continuumSuccOrdinal_wetzelIndexOfOrdinal]
  exact le_add_self (α := Ordinal)

noncomputable def wetzelNaturalSite (n : ℕ) : GroundContinuumSuccIndex :=
  wetzelIndexOfOrdinal n
    ((Ordinal.natCast_lt_omega0 n).trans (Cardinal.lt_ord.mpr
      (Ordinal.card_omega0.trans_lt groundKappaAleph0Lt930)))

theorem wetzelNaturalSite_lt_functionStage (i : GroundContinuumSuccIndex) (n : ℕ) :
    wetzelNaturalSite n < wetzelFunctionStage i := by
  apply (continuumSuccOrdinal_lt_iff930 _ _).mp
  simp only [wetzelNaturalSite,wetzelFunctionStage,continuumSuccOrdinal_wetzelIndexOfOrdinal]
  exact (Ordinal.natCast_lt_omega0 n).trans_le (le_self_add (α := Ordinal))

theorem infinite_oldSites_functionStage (i : GroundContinuumSuccIndex) :
    Infinite {j : GroundContinuumSuccIndex // j < wetzelFunctionStage i} := by
  let f (n : ℕ) : {j : GroundContinuumSuccIndex // j < wetzelFunctionStage i} :=
    ⟨wetzelNaturalSite n,wetzelNaturalSite_lt_functionStage i n⟩
  apply Infinite.of_injective f
  intro n m h
  have he : (n : Ordinal) = (m : Ordinal) := by
    have h' := congrArg (fun j => continuumSuccOrdinal j.val) h
    simpa only [f,wetzelNaturalSite,continuumSuccOrdinal_wetzelIndexOfOrdinal] using h'
  exact_mod_cast he

end JSP000930.Negative
