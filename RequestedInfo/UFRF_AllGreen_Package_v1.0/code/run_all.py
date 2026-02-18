import subprocess
import sys
from pathlib import Path


def run(script_path: Path) -> None:
    cmd = [sys.executable, str(script_path)]
    print(">>>", " ".join(cmd))
    subprocess.run(cmd, check=True)


def main() -> None:
    pkg_root = Path(__file__).resolve().parent.parent
    (pkg_root / "results").mkdir(exist_ok=True)

    code_dir = pkg_root / "code"
    run(code_dir / "maxwell_fdtd_1d.py")
    run(code_dir / "dirac_spinor_checks.py")
    run(code_dir / "ym_lattice_su2_demo.py")
    run(code_dir / "ym_lattice_su3_demo.py")

    print("\nAll runs complete. See results/*.json.")

if __name__ == "__main__":
    main()
