import JSP000933SetSentence

open Fol

namespace JSP000933
namespace SetLanguage

def wordCylinder_f {n : ℕ} (w A : STerm n) : SForm n :=
  exIn omega fun m =>
    exIn (powerset m) fun S =>
      bd_and (bd_equal (up2 w) (pair' (up m) S))
        (allIn (up m) fun i =>
          bd_biimp (mem' i (up3 A)) (mem' i (up S)))

def openEdge_f {n : ℕ} (W A B : STerm n) : SForm n :=
  bd_and (bd_not (bd_equal A B))
    (sEx fun u => sEx fun v =>
      bd_and
        (bd_or (mem' (pair' (up u) v) (up2 W)) (mem' (pair' v (up u)) (up2 W)))
        (bd_and (wordCylinder_f (up u) (up2 A)) (wordCylinder_f v (up2 B))))

def countableSet_f {n : ℕ} (C : STerm n) : SForm n :=
  sEx fun G =>
    bd_and
      (allIn (up C) fun y => exIn omega fun i => value_f (up2 G) i (up y))
      (allIn omega fun i => allIn (up2 C) fun y => allIn (up3 C) fun z =>
        bd_imp (bd_and (value_f (up3 G) (up2 i) (up y)) (value_f (up3 G) (up2 i) z))
          (bd_equal (up y) z))

def openClique_f {n : ℕ} (X W C : STerm n) : SForm n :=
  bd_and (subset'' C X)
    (bd_and (bd_not (countableSet_f C))
      (allIn C fun A => allIn (up C) fun B =>
        bd_imp (bd_not (bd_equal (up A) B)) (openEdge_f (up2 W) (up A) B)))

def closedCodeAt_f {n : ℕ} (H i A : STerm n) : SForm n :=
  sAll fun w => bd_imp (value_f (up H) (up i) w) (bd_not (wordCylinder_f w (up A)))

def closedIndependentCover_f {n : ℕ} (X W H : STerm n) : SForm n :=
  bd_and
    (allIn X fun A => exIn omega fun i => closedCodeAt_f (up2 H) i (up A))
    (allIn omega fun i => allIn (up X) fun A => allIn (up2 X) fun B =>
      bd_imp (bd_and (closedCodeAt_f (up3 H) (up2 i) (up A))
        (closedCodeAt_f (up3 H) (up2 i) B))
        (bd_not (openEdge_f (up3 W) (up A) B)))

def cantorOCA_f : sentence L_ZFC :=
  sAll fun X => sAll fun W =>
    bd_imp (subset'' (up X) omegaSubsets)
      (bd_or (sEx fun C => openClique_f (up2 X) (up W) C)
        (sEx fun H => closedIndependentCover_f (up2 X) (up W) H))

end SetLanguage
end JSP000933
