import JSP000933ActualRawEvalHarmonicNull

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualBlockClamp {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : ℕ → B :=
  bitsMeet (actualRawOutput T (actualSourceUnion T)) (L (actualSourceUnion T))

noncomputable def actualClampedOutput {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) : ℕ → B :=
  bitsMeet (actualRawOutput T x) (actualBlockClamp T)

theorem actualCap_acceptsSource_r364 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) : p≤realEqValue (bitsMeet c (actualSourceUnion T)) (actualSourceUnion T) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  change p⊓(c m⊓actualSourceUnion T m)=p⊓actualSourceUnion T m
  calc
    p⊓(c m⊓actualSourceUnion T m)=(p⊓actualSourceUnion T m)⊓c m := by ac_rfl
    _=p⊓actualSourceUnion T m := inf_eq_left.mpr
      (bitsBelowValue_apply_r256 (actualSourceUnion_below_cap_r356 T) m)

theorem actualPaddedSource_inter_source_r364 {p : B} {c : ℕ → B} {L : (ℕ → B) → ℕ → B}
    (T : ActualStageTower B p c L) (x : ℕ → B) (hX : p≤bitsBelowValue x (actualSourceUnion T)) :
    p≤realEqValue (bitsMeet (bitsMeet c (actualPaddedInput T x)) (actualSourceUnion T)) x := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  let A := actualPaddingUnion T m
  let D := actualSourceUnion T m
  let C := c m
  let X := x m
  have hD : p⊓X≤D := bitsBelowValue_apply_r256 hX m
  have hC : p⊓X≤C := bitsBelowValue_apply_r256
    (bitsBelowValue_trans_r324 hX (actualSourceUnion_below_cap_r356 T)) m
  have hA : p⊓(A⊓D)=⊥ := actualPadding_disjoint_source_r356 T m
  change p⊓((C⊓(A⊔X))⊓D)=p⊓X
  calc
    p⊓((C⊓(A⊔X))⊓D)=((p⊓D)⊓C)⊓(A⊔X) := by ac_rfl
    _=(((p⊓D)⊓C)⊓A)⊔(((p⊓D)⊓C)⊓X) := inf_sup_left _ _ _
    _=((p⊓(A⊓D))⊓C)⊔(((p⊓X)⊓D)⊓C) := by ac_rfl
    _=p⊓X := by rw [hA,bot_inf_eq,bot_sup_eq,inf_eq_left.mpr hD,inf_eq_left.mpr hC]

theorem actualBlockClamp_harmEq_r364 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x))) :
    LocalEq true p (actualBlockClamp T) (F.toName (actualSourceUnion T)) := by
  let I := F.restrict_r246 (show p≤p from le_rfl)
  let D := actualSourceUnion T
  let X := bitsMeet c (actualPaddedInput T D)
  have hD : p≤bitsBelowValue D D := bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl)
  have hA : LocalEq true p (actualRawOutput T D) (F.toName X) :=
    (actualRawOutput_harmEq_padded_r363 T D hD).symm_r236.trans_r236 (hL (actualPaddedInput T D))
  have hB : LocalEq true p (L D) (F.toName D) :=
    (hL D).trans_r236 (I.mapLocalEq_r239 (LocalEq.of_realEq_r246 false (actualCap_acceptsSource_r364 T)))
  have he := (hA.meet_congr_r239 hB).trans_r236 (I.mapMeet_r237 X D).symm_r236
  exact he.trans_r236 (I.mapLocalEq_r239 (LocalEq.of_realEq_r246 false (actualPaddedSource_inter_source_r364 T D hD)))

theorem actualClampedOutput_harmEq_r364 {p : B} (F : CoherentSelectedIso B p)
    {c : ℕ → B} {L : (ℕ → B) → ℕ → B} (T : ActualStageTower B p c L)
    (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (x : ℕ → B) (hX : p≤bitsBelowValue x (actualSourceUnion T)) :
    LocalEq true p (actualClampedOutput T x) (F.toName x) := by
  let I := F.restrict_r246 (show p≤p from le_rfl)
  let D := actualSourceUnion T
  let X := bitsMeet c (actualPaddedInput T x)
  have hA : LocalEq true p (actualRawOutput T x) (F.toName X) :=
    (actualRawOutput_harmEq_padded_r363 T x hX).symm_r236.trans_r236 (hL (actualPaddedInput T x))
  have he := (hA.meet_congr_r239 (actualBlockClamp_harmEq_r364 F T hL)).trans_r236
    (I.mapMeet_r237 X D).symm_r236
  exact he.trans_r236 (I.mapLocalEq_r239 (LocalEq.of_realEq_r246 false (actualPaddedSource_inter_source_r364 T x hX)))

end SetLanguage
end JSP000933
