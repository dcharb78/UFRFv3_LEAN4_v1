import numpy as np, math, json, os, time

# SU(2) utilities
def su2_random_near_identity(eps=0.1, rng=None):
    if rng is None: rng = np.random.default_rng()
    # random axis n, small angle theta ~ eps
    n = rng.normal(size=3)
    n = n/np.linalg.norm(n)
    theta = eps * rng.normal()
    a0 = math.cos(theta/2.0)
    a = n*math.sin(theta/2.0)
    # Quaternion to SU(2) 2x2
    return np.array([[a0+1j*a[2], a[1]+1j*a[0]],[-a[1]+1j*a[0], a0-1j*a[2]]], dtype=complex)

def su2_identity():
    return np.eye(2, dtype=complex)

def su2_herm_trace(M):
    return np.real(np.trace(M))

def staple(U, x, mu, lat):
    # Sum of staples around link (x,mu)
    Lx, Ly = lat["Lx"], lat["Ly"]
    # coordinates
    xm, ym = x
    Ufield = lat["U"]
    sum_staple = np.zeros((2,2), dtype=complex)
    for nu in [0,1]:
        if nu == mu: continue
        # forward staple
        xp = ((xm + (mu==0))%Lx, (ym + (mu==1))%Ly)
        xnu = ((xm + (nu==0))%Lx, (ym + (nu==1))%Ly)
        xpnu = ((xp[0] + (nu==0))%Lx, (xp[1] + (nu==1))%Ly)
        sum_staple += Ufield[nu][x] @ Ufield[mu][xnu] @ Ufield[nu][xp].conj().T
        # backward staple
        xn = ((xm - (nu==0))%Lx, (ym - (nu==1))%Ly)
        sum_staple += Ufield[nu][xn].conj().T @ Ufield[mu][xn] @ Ufield[nu][xn if mu==nu else ( (xn[0]+(mu==0))%Lx, (xn[1]+(mu==1))%Ly )]
    return sum_staple

def action_delta(U_old, U_new, x, mu, lat, beta):
    # Wilson action change for a single link update
    S = 0.0
    st = staple(U_old, x, mu, lat)
    # Re Tr(U V) with V = staple
    def link_term(U):
        return np.real(np.trace(U @ st))
    # old/new contribution difference (normalized for SU(2) where N=2)
    return (beta/2.0) * (link_term(U_new) - link_term(U_old))

def avg_plaquette(lat):
    Lx, Ly = lat["Lx"], lat["Ly"]
    U = lat["U"]
    plaq = 0.0
    for x in range(Lx):
        for y in range(Ly):
            # U_p = Ux(x,y) Uy(x+1,y) Ux^\dagger(x,y+1) Uy^\dagger(x,y)
            Ux = U[0][(x,y)]
            Uy = U[1][(x,y)]
            Ux_p = U[0][((x+1)%Lx, y)]
            Uy_p = U[1][(x, (y+1)%Ly)]
            Up = Ux @ U[1][((x+1)%Lx, y)] @ U[0][(x, (y+1)%Ly)].conj().T @ Uy.conj().T
            plaq += np.real(np.trace(Up))/2.0
    return plaq/(Lx*Ly)

def initialize_lattice(Lx=8, Ly=8):
    Ux = {}
    Uy = {}
    for x in range(Lx):
        for y in range(Ly):
            Ux[(x,y)] = su2_identity()
            Uy[(x,y)] = su2_identity()
    return {"U": [Ux, Uy], "Lx": Lx, "Ly": Ly}

def metropolis_sweep(lat, beta=4.0, eps=0.3, rng=None):
    if rng is None: rng = np.random.default_rng()
    accept = 0; total = 0
    for mu in [0,1]:
        keys = list(lat["U"][mu].keys())
        rng.shuffle(keys)
        for x in keys:
            U_old = lat["U"][mu][x]
            R = su2_random_near_identity(eps=eps, rng=rng)
            U_new = R @ U_old
            dS = action_delta(U_old, U_new, x, mu, lat, beta)
            if dS <= 0 or rng.random() < math.exp(-dS):
                lat["U"][mu][x] = U_new
                accept += 1
            total += 1
    return accept, total

def wilson_loop(lat, R=1, T=1):
    Lx, Ly = lat["Lx"], lat["Ly"]
    U = lat["U"]
    acc = 0.0; count = 0
    for x in range(Lx):
        for y in range(Ly):
            # rectangle from (x,y) of size R in x and T in y
            xx, yy = x, y
            W = np.eye(2, dtype=complex)
            # +x
            for i in range(R):
                W = W @ U[0][((xx+i)%Lx, yy)]
            # +y
            for j in range(T):
                W = W @ U[1][(((x+R)%Lx), (yy+j)%Ly)]
            # -x
            for i in range(R):
                W = W @ U[0][(((x+R-1-i)%Lx), ((y+T)%Ly))].conj().T
            # -y
            for j in range(T):
                W = W @ U[1][(x, ((y+T-1-j)%Ly))].conj().T
            acc += np.real(np.trace(W))/2.0
            count += 1
    return acc/count

def correlator_plaquette_line(lat, sep_max=5):
    # crude connected correlator along x at fixed y
    Lx, Ly = lat["Lx"], lat["Ly"]
    U = lat["U"]
    # compute local plaquette observable P(x,y) = ReTr(Up)/2
    P = np.zeros((Lx, Ly), dtype=float)
    for x in range(Lx):
        for y in range(Ly):
            Up = U[0][(x,y)] @ U[1][((x+1)%Lx, y)] @ U[0][(x, (y+1)%Ly)].conj().T @ U[1][(x,y)].conj().T
            P[x,y] = np.real(np.trace(Up))/2.0
    Pmean = np.mean(P)
    corr = []
    for r in range(sep_max+1):
        vals = []
        for y in range(Ly):
            for x in range(Lx):
                xp = (x+r)%Lx
                vals.append((P[x,y]-Pmean)*(P[xp,y]-Pmean))
        corr.append(float(np.mean(np.abs(vals))))
    return corr

def run_su2(L=10, beta=2.2, sweeps_therm=50, sweeps_meas=50, eps=0.3, outdir="results", rng=None):
    if rng is None: rng = np.random.default_rng(42)
    lat = initialize_lattice(L, L)
    # Thermalize
    for _ in range(sweeps_therm):
        metropolis_sweep(lat, beta=beta, eps=eps, rng=rng)
    # Measurements
    plaqs = []
    loops = []
    for s in range(sweeps_meas):
        metropolis_sweep(lat, beta=beta, eps=eps, rng=rng)
        plaqs.append(avg_plaquette(lat))
        # measure few small loops
        loops.append({(1,1): wilson_loop(lat,1,1),
                      (1,2): wilson_loop(lat,1,2),
                      (2,2): wilson_loop(lat,2,2)})
    # correlator (single snapshot at end)
    corr = correlator_plaquette_line(lat, sep_max=min(6, L//2))
    # crude correlation length by exponential fit C(r) ~ A exp(-r/xi)
    xs = np.arange(1, len(corr))
    ys = np.array(corr[1:])
    ys = np.where(ys>1e-12, ys, 1e-12)
    xi = None
    try:
        coeffs = np.polyfit(xs, np.log(ys), 1)
        if coeffs[0] < 0:
            xi = -1.0/coeffs[0]
        else:
            # ratio fallback
            r = ys[0]/(corr[0]+1e-12)
            if r < 1:
                xi = -1.0/np.log(r)
    except Exception:
        xi = None

    summary = {
        "beta": beta,
        "avg_plaquette_mean": float(np.mean(plaqs)),
        "avg_plaquette_std": float(np.std(plaqs)),
        "wilson_loops_last": {str(k): float(v) for k,v in loops[-1].items()},
        "corr": corr,
        "xi_est_lattice_units": None if xi is None else float(xi),
        "mass_proxy": None if xi is None else float(1.0/xi)
    }
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "ym_su2_summary.json"), "w") as f:
        json.dump(summary, f, indent=2)
    return summary

if __name__ == "__main__":
    s = run_su2(outdir="results")
    print(json.dumps(s, indent=2))
