import JSP000933SelectedQuotientOrderIso

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem LocalLE.meet_bounds_r237 (h : Bool) (p : B) (x y : ℕ → B) :
    LocalLE h p (bitsMeet x y) x ∧ LocalLE h p (bitsMeet x y) y :=
  LocalLE.meet_right_r236.mp (LocalLE.refl_r236 h p (bitsMeet x y))

theorem LocalLE.join_bounds_r237 (h : Bool) (p : B) (x y : ℕ → B) :
    LocalLE h p x (bitsJoin x y) ∧ LocalLE h p y (bitsJoin x y) :=
  LocalLE.join_left_r236.mp (LocalLE.refl_r236 h p (bitsJoin x y))

theorem SelectedQuotientIso.mapMeet_r237 {p : B} (F : SelectedQuotientIso B p) (x y : ℕ → B) :
    LocalEq true p (F.toName (bitsMeet x y)) (bitsMeet (F.toName x) (F.toName y)) := by
  let t := bitsMeet (F.toName x) (F.toName y)
  let r := F.invName t
  have hR : LocalEq true p t (F.toName r) := F.inv_har t
  have hT := LocalLE.meet_bounds_r237 true p (F.toName x) (F.toName y)
  have hS := LocalLE.meet_bounds_r237 false p x y
  constructor
  · exact LocalLE.meet_right_r236.mpr
      ⟨(F.order _ _).mp hS.1,(F.order _ _).mp hS.2⟩
  · have hRX : LocalLE false p r x :=
      (F.order _ _).mpr (hR.2.trans_r236 hT.1)
    have hRY : LocalLE false p r y :=
      (F.order _ _).mpr (hR.2.trans_r236 hT.2)
    have hRM : LocalLE false p r (bitsMeet x y) := LocalLE.meet_right_r236.mpr ⟨hRX,hRY⟩
    exact hR.1.trans_r236 ((F.order _ _).mp hRM)

theorem SelectedQuotientIso.mapJoin_r237 {p : B} (F : SelectedQuotientIso B p) (x y : ℕ → B) :
    LocalEq true p (F.toName (bitsJoin x y)) (bitsJoin (F.toName x) (F.toName y)) := by
  let t := bitsJoin (F.toName x) (F.toName y)
  let r := F.invName t
  have hR : LocalEq true p t (F.toName r) := F.inv_har t
  have hT := LocalLE.join_bounds_r237 true p (F.toName x) (F.toName y)
  have hS := LocalLE.join_bounds_r237 false p x y
  constructor
  · have hXR : LocalLE false p x r :=
      (F.order _ _).mpr (hT.1.trans_r236 hR.1)
    have hYR : LocalLE false p y r :=
      (F.order _ _).mpr (hT.2.trans_r236 hR.1)
    have hJR : LocalLE false p (bitsJoin x y) r := LocalLE.join_left_r236.mpr ⟨hXR,hYR⟩
    exact ((F.order _ _).mp hJR).trans_r236 hR.2
  · exact LocalLE.join_left_r236.mpr
      ⟨(F.order _ _).mp hS.1,(F.order _ _).mp hS.2⟩

theorem SelectedQuotientIso.mapBot_r237 {p : B} (F : SelectedQuotientIso B p) :
    LocalEq true p (F.toName (fun _ => ⊥)) (fun _ => ⊥) := by
  let z : ℕ → B := fun _ => ⊥
  let r := F.invName z
  have hR : LocalEq true p z (F.toName r) := F.inv_har z
  exact ⟨((F.order _ _).mp (LocalLE.bot_r236 false p r)).trans_r236 hR.2,
    LocalLE.bot_r236 true p _⟩

theorem SelectedQuotientIso.mapTop_r237 {p : B} (F : SelectedQuotientIso B p) :
    LocalEq true p (F.toName (fun _ => ⊤)) (fun _ => ⊤) := by
  let z : ℕ → B := fun _ => ⊤
  let r := F.invName z
  have hR : LocalEq true p z (F.toName r) := F.inv_har z
  exact ⟨LocalLE.top_r236 true p _,hR.1.trans_r236
    ((F.order _ _).mp (LocalLE.top_r236 false p r))⟩

end SetLanguage
end JSP000933
