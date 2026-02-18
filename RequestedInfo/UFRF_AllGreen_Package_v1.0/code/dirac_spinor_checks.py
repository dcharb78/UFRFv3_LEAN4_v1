import numpy as np, json, os

def dirac_representation():
    # Dirac gamma matrices in standard (Dirac) representation
    I2 = np.eye(2)
    zero = np.zeros((2,2))
    sigma_x = np.array([[0,1],[1,0]], dtype=complex)
    sigma_y = np.array([[0,-1j],[1j,0]], dtype=complex)
    sigma_z = np.array([[1,0],[0,-1]], dtype=complex)

    gamma0 = np.block([[I2, zero],[zero, -I2]])
    gammai = []
    for s in (sigma_x, sigma_y, sigma_z):
        gammai.append(np.block([[zero, s],[-s, zero]]))
    return gamma0, gammai

def anticomm_test():
    g0, gi = dirac_representation()
    g = [g0] + gi
    eta = np.diag([1,-1,-1,-1])
    max_err = 0.0
    for mu in range(4):
        for nu in range(4):
            lhs = g[mu]@g[nu] + g[nu]@g[mu]
            rhs = 2.0*eta[mu,nu]*np.eye(4)
            err = np.max(np.abs(lhs - rhs))
            if err > max_err: max_err = float(err)
    return max_err

def factorization_test(p=None, m=1.0):
    # Check (gamma·p - m)(gamma·p + m) = (p^2 - m^2) I
    g0, gi = dirac_representation()
    g = [g0] + gi
    if p is None:
        # choose a random 4-vector with time-like component ~ few m
        rng = np.random.default_rng(1234)
        p = np.array([2.0*m, 0.3*m, -0.1*m, 0.2*m], dtype=float)
    gp = p[0]*g[0] - p[1]*g[1] - p[2]*g[2] - p[3]*g[3]  # sign with metric (+,-,-,-)
    A = (gp - m*np.eye(4)) @ (gp + m*np.eye(4))
    scalar = (p[0]**2 - p[1]**2 - p[2]**2 - p[3]**2 - m**2)
    err = np.max(np.abs(A - scalar*np.eye(4)))
    return float(err), p.tolist(), float(scalar)

def run_checks(outdir="results"):
    os.makedirs(outdir, exist_ok=True)
    anti_err = anticomm_test()
    fac_err, p, scalar = factorization_test()
    with open(os.path.join(outdir, "dirac_checks_summary.json"), "w") as f:
        json.dump({"anticommutator_max_error": anti_err, "factorization_error": fac_err, "p": p, "p2_minus_m2": scalar}, f, indent=2)
    return anti_err, fac_err

if __name__ == "__main__":
    anti_err, fac_err = run_checks(outdir="results")
    print("Max Clifford anticommutator error:", anti_err)
    print("Factorization error:", fac_err)
