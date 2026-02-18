import math
import matplotlib.pyplot as plt
import numpy as np

# UFRF Constants
PHI = (1 + math.sqrt(5)) / 2
SQRT_PHI = math.sqrt(PHI)

def waveform(t):
    """
    Universal Breathing Waveform
    t: position in cycle [0, 13)
    Output: Amplitude
    """
    t = t % 13 # Ensure scalar wrap
    
    if t < 3:
        # SEED: Linear warmup 0 -> 1
        return t / 3
    elif t < 6:
        # EXPANSION: Accelerating 1 -> 2
        return 1 + (t - 3) / 3
    elif t < 6.5:
        # FLIP APPROACH: Peak intensity
        return 2.0
    elif t < 9:
        # CONTRACTION: Decelerating 2 -> 1
        return 2.0 - (t - 6.5) / 2.5
    elif t < 10.5:
        # REST: sqrt(phi) enhancement
        return SQRT_PHI
    elif t < 12:
        # BRIDGE: Transitioning down
        return SQRT_PHI - (t - 10.5) / 1.5 * 0.5
    else:
        # RETURN: Void state
        return 0.1

def superposition(t, primes):
    """
    Sum of oscillators at time t.
    Each prime p has period 13 * p.
    """
    total = 0
    for p in primes:
        period = 13 * p
        # Map global time t to local phase [0, 13)
        local_phase = (t / period) * 13
        total += waveform(local_phase)
    return total

def visualize():
    # Simulation Parameters
    primes = [1, 3, 5, 7, 11] # First 5 odd primes (treating 1 as fundamental)
    duration = 13 * 11 * 2 # Two cycles of the largest prime
    resolution = 1000
    
    times = np.linspace(0, duration, resolution)
    amplitudes = [superposition(t, primes) for t in times]
    
    # Plotting
    plt.figure(figsize=(15, 6))
    plt.plot(times, amplitudes, label=f"Superposition of Primes {primes}", color='purple', linewidth=1.5)
    plt.title("UFRF Prime Choreography: The Interference Pattern")
    plt.xlabel("Global Epochs")
    plt.ylabel("Combined Amplitude")
    plt.grid(True, which='both', linestyle='--', alpha=0.5)
    plt.legend()
    
    # Highlight the structure
    # Mark fundamental cycles (every 13)
    for i in range(0, int(duration), 13):
        plt.axvline(x=i, color='gray', linestyle=':', alpha=0.3)
        
    output_file = "choreography_plot.png"
    plt.savefig(output_file)
    print(f"Plot saved to {output_file}")

if __name__ == "__main__":
    visualize()
