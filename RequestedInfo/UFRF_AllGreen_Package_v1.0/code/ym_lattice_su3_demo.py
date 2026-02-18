import numpy as np, math, json, os

# Gell-Mann matrices
def gell_mann():
    l = []
    l.append(np.array([[0,1,0],[1,0,0],[0,0,0]], dtype=complex))
    l.append(np.array([[0,-1j,0],[1j,0,0],[0,0,0]], dtype=complex))
    l.append(np.array([[1,0,0],[0,-1,0],[0,0,0]], dtype=complex))
    l.append(np.array([[0,0,1],[0,0,0],[1,0,0]], dtype=complex))
    l.append(np.array([[0,0,-1j],[0,0,0],[1j,0,0]], dtype=complex))
    l.append(np.array([[0,0,0],[0,0,1],[0,1,0]], dtype=complex))
    l.append(np.array([[0,0,0],[0,0,-1j],[0,1j,0]], dtype=complex))
    l.append(np.array([[1/np.sqrt(3),0,0],[0,1/np.sqrt(3),0],[0,0,-2/np.sqrt(3)]], dtype=complex))
    return l

def su3_exp_from_algebra(a, eps=0.1):
    # a: 8 random coefficients
    l = gell_mann()
    H = sum(a[i]*l[i] for i in range(8))
    # anti-Hermitian, traceless generator i*H (H is Hermitian)
    M = 1j*eps*H
    # matrix exponential via scaling + pade (numpy.linalg.expm if available; here do series approx for small eps)
    # For small eps, second-order is fine
    I = np.eye(3, dtype=complex)
    return I + M + 0.5*(M@M)

def su3_identity(): return np.eye(3, dtype=complex)

def initialize_lattice(Lx=6, Ly=6):
    Ux = {}; Uy = {}
    I = su3_identity()
    for x in range(Lx):
        for y in range(Ly):
            Ux[(x,y)] = I.copy()
            Uy[(x,y)] = I.copy()
    return {"U": [Ux, Uy], "Lx": Lx, "Ly": Ly}

def staple(U, x, mu, lat):
    Lx, Ly = lat["Lx"], lat["Ly"]
    xm, ym = x
    sum_staple = np.zeros((3,3), dtype=complex)
    for nu in [0,1]:
        if nu==mu: continue
        # forward staple
        xp = ((xm + (mu==0))%Lx, (ym + (mu==1))%Ly)
        xnu = ((xm + (nu==0))%Lx, (ym + (nu==1))%Ly)
        sum_staple += U[nu][x] @ U[mu][xnu] @ U[nu][xp].conj().T
        # backward staple
        xn = ((xm - (nu==0))%Lx, (ym - (nu==1))%Ly)
        sum_staple += U[nu][xn].conj().T @ U[mu][xn] @ U[nu][((xn[0]+(mu==0))%Lx, (xn[1]+(mu==1))%Ly)]
    return sum_staple

def delta_action(U_old, U_new, x, mu, lat, beta):
    st = staple(lat["U"], x, mu, lat)
    # action contribution proportional to Re Tr(U V) with V = staple
    def term(U): return np.real(np.trace(U @ st))
    # Wilson action change  S ~ - (beta/N) ReTr(U V), N=3
    return (beta/3.0)*(term(U_new)-term(U_old))

def avg_plaquette(lat):
    Lx, Ly = lat["Lx"], lat["Ly"]
    U = lat["U"]
    pl = 0.0
    for x in range(Lx):
        for y in range(Ly):
            Ux = U[0][(x,y)]
            Uy = U[1][(x,y)]
            Up = Ux @ U[1][((x+1)%Lx, y)] @ U[0][(x, (y+1)%Ly)].conj().T @ Uy.conj().T
            pl += np.real(np.trace(Up))/3.0
    return pl/(Lx*Ly)

def metropolis_sweep(lat, beta=6.0, eps=0.2, rng=None):
    if rng is None: rng = np.random.default_rng(123)
    accept=0; total=0
    for mu in [0,1]:
        keys = list(lat["U"][mu].keys())
        rng.shuffle(keys)
        for x in keys:
            U_old = lat["U"][mu][x]
            a = rng.normal(size=8)
            R = su3_exp_from_algebra(a, eps=eps)
            U_new = R @ U_old
            dS = delta_action(U_old, U_new, x, mu, lat, beta)
            if dS <= 0 or rng.random() < math.exp(-dS):
                lat["U"][mu][x] = U_new
                accept += 1
            total += 1
    return accept, total

def run_su3(L=6, beta=12.0, sweeps_therm=60, sweeps_meas=60, eps=0.12, outdir="results", rng=None):
    if rng is None: rng = np.random.default_rng(7)
    lat = initialize_lattice(L, L)
    for _ in range(sweeps_therm):
        metropolis_sweep(lat, beta=beta, eps=eps, rng=rng)
    plaqs=[]
    for _ in range(sweeps_meas):
        metropolis_sweep(lat, beta=beta, eps=eps, rng=rng)
        plaqs.append(avg_plaquette(lat))
    summary = {
        "beta": beta,
        "avg_plaquette_mean": float(np.mean(plaqs)),
        "avg_plaquette_std": float(np.std(plaqs)),
        "L": L
    }
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "ym_su3_summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    return summary

if __name__ == "__main__":
    s = run_su3(outdir="results")
    print(json.dumps(s, indent=2))
