import Seam_Generic_Classification_Theorem

/-!
# REST Seam Classification

Canonical seam classification predicates and window lemmas.
-/

namespace RESTSeamOverlap

/-- Parent COMPLETE classifier (`11,12,13`) in the 14-state seam chart. -/
def isParentComplete (s : Nat) : Prop := s = 11 ∨ s = 12 ∨ s = 13

/-- Child SEED classifier (`1,2,3`) in the 14-state seam chart. -/
def isChildSeed (s : Nat) : Prop := s = 1 ∨ s = 2 ∨ s = 3

theorem isParentComplete_iff_window (r : Nat) (hr : r ≤ 3) :
    isParentComplete (10 + r) ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  have h := SeamGeneric.isShiftedWindow123_at_add_iff_window123 10 r hr
  simpa [isParentComplete, SeamGeneric.isShiftedWindow123, SeamGeneric.isWindow123] using h

theorem isChildSeed_iff_window (r : Nat) (_hr : r ≤ 3) :
    isChildSeed r ↔ (r = 1 ∨ r = 2 ∨ r = 3) := by
  simp [isChildSeed]

end RESTSeamOverlap
