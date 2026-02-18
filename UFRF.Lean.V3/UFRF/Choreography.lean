import UFRF.Waveform
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
-- import Mathlib.Algebra.BigOperators.Basic -- Not needed?

/-!
# UFRF.Choreography

**The Superposition of Primes**

"The primes don't follow a choreography. They ARE the choreography."

This module defines the superposition of breathing waveforms across
prime-numbered periods.

## The Model
The total field state $S(t)$ at global time $t$ is the sum of
individual oscillators, each resonating at a prime period $P_k$.

$$ S(t) = \sum_{p \in Primes} W\left( \frac{t \cdot 13}{p} \pmod{13} \right) $$

where:
- $W$ is the universal `waveform`
- $P$ is the prime period (e.g., 13, 39, 65...)
- The argument is scaled so that the waveform completes 1 cycle
  in $P$ units of global time.
-/

namespace UFRF.Dynamics

namespace UFRF.Dynamics

-- open UFRF.Constants -- No namespace


-- import Mathlib.Algebra.Order.Floor.Ring -- Moved to top

/--
Helper: Modulo for Reals.
x % m = x - m * floor(x / m)
-/
noncomputable def real_rem (x m : ℝ) : ℝ :=
  x - m * (Int.floor (x / m) : ℝ)

/--
Calculate the phase position within a specific oscillator's cycle.
`t`: Global time
`period`: The duration of one full cycle for this oscillator
Returns position in $[0, 13)$.
-/
noncomputable def local_phase (t : ℝ) (period : ℝ) : ℝ :=
  let scaled_t := t * 13 / period
  real_rem scaled_t 13

/--
The contribution of a single prime oscillator at time `t`.
-/
noncomputable def oscillator_output (t : ℝ) (prime : ℕ) : ℝ :=
  let period := (prime : ℝ) * 13  -- Period scales with prime
  let pos := local_phase t period
  waveform pos

/--
**The Choreography (Superposition)**
Sum of oscillator outputs for a given list of primes.
-/
noncomputable def superposition (t : ℝ) (primes : List ℕ) : ℝ :=
  (primes.map (fun p => oscillator_output t p)).sum

/-!
## Theoretical Predictions

1. **Quasi-Crystalline Modulation**: Because primes are incommensurate,
   `superposition` effectively never repeats for realistic timeframes.
   
2. **Vacuum Energy**: The "baseline" energy of the system is the
   average value of this superposition.
-/

end UFRF.Dynamics
