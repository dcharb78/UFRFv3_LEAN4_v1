import Mathlib
import Trinity_HalfStep_Dual_Theorem

/-!
# Breathing-Cycle LOG / Checkpoint Partition (Discrete, Bounded)

This module defines a purely combinatorial partition of the 13-cycle into:

- LOG blocks: `1..3`, `4..6`, `7..9`
- REST: `10`
- Bridge/Return tail: `11,12,13` with `13 ≡ 0 (mod 13)`

It proves (no placeholders):
- the blocks cover all positions (`Fin 13`) and do not overlap,
- the checkpoint set `{1,4,7,10}` lies in the core (LOG+REST),
- the "flip" midpoint is witnessed discretely by the 26-cycle half-step index:
  `2*6 < (2*6+1) < 2*7`, with `halfIndex 6 = 13`.

This is intentionally *mechanism only* (no physics interpretation).
-/

namespace BreathingCycleLOGPartition

/-- Discrete 13-cycle positions. -/
abbrev Pos := Fin 13

def log1 : Finset Pos := { (1 : Pos), (2 : Pos), (3 : Pos) }
def log2 : Finset Pos := { (4 : Pos), (5 : Pos), (6 : Pos) }
def log3 : Finset Pos := { (7 : Pos), (8 : Pos), (9 : Pos) }

/-- The REST hub position (convention: `10`). -/
def rest : Finset Pos := { (10 : Pos) }

/--
Bridge/return tail:

Positions `11,12,13` where `13` is represented as `0` in `Fin 13`.
-/
def bridge : Finset Pos := { (11 : Pos), (12 : Pos), (0 : Pos) }

def core : Finset Pos := log1 ∪ log2 ∪ log3 ∪ rest
def allPhases : Finset Pos := core ∪ bridge

theorem allPhases_eq_univ : allPhases = Finset.univ := by
  native_decide

theorem core_eq_univ_without_bridge : core = Finset.univ \ bridge := by
  native_decide

theorem bridge_eq_tail : bridge = { (0 : Pos), (11 : Pos), (12 : Pos) } := by
  native_decide

def checkpoints : Finset Pos := { (1 : Pos), (4 : Pos), (7 : Pos), (10 : Pos) }

theorem checkpoints_subset_core : checkpoints ⊆ core := by
  native_decide

theorem pairwise_disjoint_partition :
    Disjoint log1 log2
    ∧ Disjoint log1 log3
    ∧ Disjoint log1 rest
    ∧ Disjoint log1 bridge
    ∧ Disjoint log2 log3
    ∧ Disjoint log2 rest
    ∧ Disjoint log2 bridge
    ∧ Disjoint log3 rest
    ∧ Disjoint log3 bridge
    ∧ Disjoint rest bridge := by
  native_decide

theorem card_log1 : log1.card = 3 := by native_decide
theorem card_log2 : log2.card = 3 := by native_decide
theorem card_log3 : log3.card = 3 := by native_decide
theorem card_rest : rest.card = 1 := by native_decide
theorem card_bridge : bridge.card = 3 := by native_decide

/--
Checkpoint-overlap windows (a discrete “3+1 closure window” view):

`{1,2,3,4}`, `{4,5,6,7}`, `{7,8,9,10}`, `{10,11,12,0}`.
Adjacent blocks overlap exactly on the checkpoint `{4,7,10}`.
-/
def block1 : Finset Pos := { (1 : Pos), (2 : Pos), (3 : Pos), (4 : Pos) }
def block2 : Finset Pos := { (4 : Pos), (5 : Pos), (6 : Pos), (7 : Pos) }
def block3 : Finset Pos := { (7 : Pos), (8 : Pos), (9 : Pos), (10 : Pos) }
def block4 : Finset Pos := { (10 : Pos), (11 : Pos), (12 : Pos), (0 : Pos) }

def blocksCover : Finset Pos := block1 ∪ block2 ∪ block3 ∪ block4

theorem card_block1 : block1.card = 4 := by native_decide
theorem card_block2 : block2.card = 4 := by native_decide
theorem card_block3 : block3.card = 4 := by native_decide
theorem card_block4 : block4.card = 4 := by native_decide

theorem blocksCover_eq_univ : blocksCover = Finset.univ := by
  native_decide

theorem block_overlaps_are_checkpoints :
    (block1 ∩ block2 = { (4 : Pos) })
    ∧ (block2 ∩ block3 = { (7 : Pos) })
    ∧ (block3 ∩ block4 = { (10 : Pos) })
    ∧ (block1 ∩ block3 = ∅)
    ∧ (block1 ∩ block4 = ∅)
    ∧ (block2 ∩ block4 = ∅) := by
  native_decide

def overlap_window_decomposition_stmt : Prop :=
    blocksCover = Finset.univ
    ∧ block1.card = 4
    ∧ block2.card = 4
    ∧ block3.card = 4
    ∧ block4.card = 4
    ∧ (block1 ∩ block2 = { (4 : Pos) })
    ∧ (block2 ∩ block3 = { (7 : Pos) })
    ∧ (block3 ∩ block4 = { (10 : Pos) })
    ∧ (block1 ∩ block3 = ∅)
    ∧ (block1 ∩ block4 = ∅)
    ∧ (block2 ∩ block4 = ∅)

theorem overlap_window_decomposition : overlap_window_decomposition_stmt := by
  unfold overlap_window_decomposition_stmt
  refine ⟨blocksCover_eq_univ, card_block1, card_block2, card_block3, card_block4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact block_overlaps_are_checkpoints.1
  · exact block_overlaps_are_checkpoints.2.1
  · exact block_overlaps_are_checkpoints.2.2.1
  · exact block_overlaps_are_checkpoints.2.2.2.1
  · exact block_overlaps_are_checkpoints.2.2.2.2.1
  · exact block_overlaps_are_checkpoints.2.2.2.2.2

/--
Half-step flip witness:

In the doubled cycle (`26 = 2*13`), integer position `k` corresponds to the even index `2k`.
The midpoint between `6` and `7` is the unique odd index `2*6+1`, which is `13`.
-/
theorem flip_midpoint_witness :
    (2 * 6 < TrinityHalfStepDual.halfIndex 6)
    ∧ (TrinityHalfStepDual.halfIndex 6 < 2 * 7)
    ∧ TrinityHalfStepDual.halfIndex 6 = 13 := by
  refine ⟨?_, ?_, TrinityHalfStepDual.halfIndex_flip⟩
  · native_decide
  · native_decide

theorem flip_midpoint_axis_signature :
    (TrinityHalfStepDual.halfIndex 6 ≡ 0 [MOD 13])
    ∧ (TrinityHalfStepDual.halfIndex 6 ≡ 1 [MOD 2]) := by
  -- Reuse the already-certified signature of the flip element `13`.
  simpa [TrinityHalfStepDual.halfIndex_flip] using TrinityHalfStepDual.flip_axis_signature

/-!
## Packaged statement

Downstream files can import this module and refer to a single `Prop` if needed.
-/

def breathing_cycle_log_checkpoint_partition_stmt : Prop :=
    allPhases = Finset.univ
    ∧ checkpoints ⊆ core
    ∧
      (Disjoint log1 log2
        ∧ Disjoint log1 log3
        ∧ Disjoint log1 rest
        ∧ Disjoint log1 bridge
        ∧ Disjoint log2 log3
        ∧ Disjoint log2 rest
        ∧ Disjoint log2 bridge
        ∧ Disjoint log3 rest
        ∧ Disjoint log3 bridge
        ∧ Disjoint rest bridge)
    ∧ (2 * 6 < TrinityHalfStepDual.halfIndex 6 ∧ TrinityHalfStepDual.halfIndex 6 < 2 * 7)
    ∧ (TrinityHalfStepDual.halfIndex 6 = 13)

theorem breathing_cycle_log_checkpoint_partition :
    breathing_cycle_log_checkpoint_partition_stmt := by
  refine ⟨allPhases_eq_univ, checkpoints_subset_core, pairwise_disjoint_partition, ?_, ?_⟩
  · exact ⟨flip_midpoint_witness.1, flip_midpoint_witness.2.1⟩
  · exact flip_midpoint_witness.2.2

/-!
## Digit → Phase Lens (0→1 refinement view)

Given a position/digit in `Fin 13`, define a total, deterministic classifier that returns
exactly one of the five phase classes: `LOG1`, `LOG2`, `LOG3`, `REST`, `BRIDGE`.

This is a bounded, discrete “lens” that lets downstream modules talk about phases
without re-proving membership disjointness.
-/

inductive Phase : Type
  | L1 | L2 | L3 | Rest | Bridge
  deriving DecidableEq, Repr

instance : Fintype Phase :=
  ⟨{ .L1, .L2, .L3, .Rest, .Bridge }, by
    intro p
    cases p <;> simp⟩

def phaseSet : Phase → Finset Pos
  | .L1 => log1
  | .L2 => log2
  | .L3 => log3
  | .Rest => rest
  | .Bridge => bridge

def phaseOf (x : Pos) : Phase :=
  if x ∈ log1 then .L1
  else if x ∈ log2 then .L2
  else if x ∈ log3 then .L3
  else if x ∈ rest then .Rest
  else .Bridge

theorem phaseOf_total : ∀ x : Pos, x ∈ phaseSet (phaseOf x) := by
  native_decide

theorem phaseOf_deterministic : ∀ x : Pos, ∀ p : Phase, x ∈ phaseSet p → phaseOf x = p := by
  native_decide

theorem mem_phaseSet_iff_phaseOf_eq :
    ∀ x : Pos, ∀ p : Phase, x ∈ phaseSet p ↔ phaseOf x = p := by
  intro x p
  constructor
  · intro hx
    exact phaseOf_deterministic x p hx
  · intro hEq
    -- Rewrite by `hEq` and use totality.
    simpa [hEq] using phaseOf_total x

def digit_phase_lens_stmt : Prop :=
    (∀ x : Pos, x ∈ phaseSet (phaseOf x))
    ∧ (∀ x : Pos, ∀ p : Phase, x ∈ phaseSet p → phaseOf x = p)

theorem digit_phase_lens : digit_phase_lens_stmt := by
  exact ⟨phaseOf_total, phaseOf_deterministic⟩

/-!
## Phase Successor Dynamics (Bounded, Discrete)

Define a wrap-around successor on `Fin 13` and prove that the `phaseOf` classifier only changes
at a small boundary set (the end-of-block closure points + REST + bridge return).
-/

def succ13 (x : Pos) : Pos :=
  ⟨(x.1 + 1) % 13, by
    have h : 0 < 13 := by decide
    exact Nat.mod_lt _ h⟩

def phaseBoundaries : Finset Pos := { (0 : Pos), (3 : Pos), (6 : Pos), (9 : Pos), (10 : Pos) }

theorem phaseOf_succ13_eq_of_not_boundary :
    ∀ x : Pos, x ∉ phaseBoundaries → phaseOf (succ13 x) = phaseOf x := by
  native_decide

theorem phaseOf_succ13_boundary_table :
    phaseOf (succ13 (3 : Pos)) = Phase.L2
    ∧ phaseOf (succ13 (6 : Pos)) = Phase.L3
    ∧ phaseOf (succ13 (9 : Pos)) = Phase.Rest
    ∧ phaseOf (succ13 (10 : Pos)) = Phase.Bridge
    ∧ phaseOf (succ13 (0 : Pos)) = Phase.L1 := by
  native_decide

def phase_successor_dynamics_stmt : Prop :=
    (∀ x : Pos, x ∉ phaseBoundaries → phaseOf (succ13 x) = phaseOf x)
    ∧ (phaseOf (succ13 (3 : Pos)) = Phase.L2)
    ∧ (phaseOf (succ13 (6 : Pos)) = Phase.L3)
    ∧ (phaseOf (succ13 (9 : Pos)) = Phase.Rest)
    ∧ (phaseOf (succ13 (10 : Pos)) = Phase.Bridge)
    ∧ (phaseOf (succ13 (0 : Pos)) = Phase.L1)

theorem phase_successor_dynamics : phase_successor_dynamics_stmt := by
  unfold phase_successor_dynamics_stmt
  refine ⟨phaseOf_succ13_eq_of_not_boundary, ?_, ?_, ?_, ?_, ?_⟩
  · exact phaseOf_succ13_boundary_table.1
  · exact phaseOf_succ13_boundary_table.2.1
  · exact phaseOf_succ13_boundary_table.2.2.1
  · exact phaseOf_succ13_boundary_table.2.2.2.1
  · exact phaseOf_succ13_boundary_table.2.2.2.2

end BreathingCycleLOGPartition
