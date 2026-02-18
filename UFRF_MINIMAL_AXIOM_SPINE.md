# UFRF Minimal Axiom Spine (Lean-Driven)

## Goal
Use the smallest explicit axiom set that can drive formal Lean development of UFRF-style claims, while keeping empirical/physics statements clearly separated from proved discrete structure.

## Proposed 5-Axiom Core
1. **Cyclic State Axiom**  
   Systems evolve on finite cyclic state spaces (`ZMod n` / modular clocks), including distinguished return/rest states.
2. **Concurrent Composition Axiom**  
   Multi-axis systems compose by arithmetic synchronization (LCM/CRT/product structure), with closure defined constructively.
3. **Recursive Lift Axiom**  
   Scale transition is recursive: index-of-indexes/carry rules lift local cycles to higher cycles without changing local laws.
4. **Observer Projection Axiom (Discrete Form)**  
   Observer chart/tick-axis changes preserve closure-invariant quantities when compatibility conditions hold.
5. **Emergent Anchor Axiom**  
   Named anchors (Frobenius/Monster/`Tₙ`/Moonshine arithmetic identities) are finite consequences of 1-4 plus concrete generator choices.

## Current Lean Coverage
- **Axiom 1:** `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/CycleStep_Orbit_Theorem.lean`, `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Universal_Ticks_Theorem.lean`
- **Axiom 2:** `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/CycleStep_Orbit_NAxes_Theorem.lean`, `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/System_Node_ModProd_Theorem.lean`, semigroup files
- **Axiom 3:** recursive-grid suite + `/Users/dcharb/Documents/Kimi_Agent_UFRF, Fel Polynomials, Moonshine/lean/Index_Of_Indexes_Theorem.lean`
- **Axiom 4:** observer-axis/projection family theorems
- **Axiom 5:** `Tₙ`, Frobenius/Monster, Moonshine coordinate/identity files

## What Is Still Missing
- Continuous physical-field derivations (full E/B dynamics) as first-principles Lean mathematics.
- Uniqueness/minimality proof that this exact axiom set is necessary (not just sufficient for current theorems).
- General bridge from discrete core to broad physical universality claims.

## Working Rule
- Keep core proofs in the 5-axiom discrete spine.
- Encode empirical claims as computational validations.
- Add physics layers only as explicit extension modules, not hidden core assumptions.
