
import numpy as np, json, os

def run_fdtd_1d(nx=400, nt=600, c=1.0, dx=1.0, dt=0.5, outdir="results"):
    # μ=ε=1 units so c=1; CFL: c*dt/dx <= 1
    E = np.zeros(nx, dtype=float)
    H = np.zeros(nx, dtype=float)  # H at i+1/2 (we'll shift indices modulo nx)

    # initial right-moving Gaussian in E
    x = np.arange(nx)
    E = np.exp(-0.5*((x - nx//3)/12.0)**2)

    # Evolution
    for n in range(nt):
        # H^{n+1/2}_{i+1/2} = H^{n-1/2}_{i+1/2} + (dt/(μ dx)) [E^n_{i+1} - E^n_i]
        curlE = (E[(np.arange(nx)+1)%nx] - E) / dx
        H += dt * curlE  # μ=1
        
        # E^{n+1}_i = E^n_i + (dt/(ε dx)) [H^{n+1/2}_{i} - H^{n+1/2}_{i-1}]
        curlH = (H - H[(np.arange(nx)-1)%nx]) / dx
        E += dt * curlH  # ε=1

    # invariants for plane-wave class (approx, using E and H)
    I1 = float(np.mean(E**2 - (c**2)*(H**2)))
    I2 = float(np.mean(E * H))

    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "maxwell_fdtd_summary.json"), "w") as f:
        json.dump({"I1_mean": I1, "I2_mean": I2, "nx": nx, "nt": nt, "cfl": c*dt/dx}, f, indent=2)
    return I1, I2

if __name__ == "__main__":
    I1, I2 = run_fdtd_1d(outdir="results")
    print("I1=<E^2 - c^2 H^2>:", I1)
    print("I2=<E·H>:", I2)
