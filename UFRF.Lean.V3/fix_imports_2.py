import os

def replace_imports(filepath):
    with open(filepath, 'r') as f:
        content = f.read()

    new_content = content.replace(
        'import Mathlib.Data.Rat.Basic',
        'import Mathlib.Data.Rat.Defs\nimport Mathlib.Data.Rat.Lemmas'
    ).replace(
        'import Mathlib.Data.Int.Floor',
        'import Mathlib.Algebra.Order.Floor'
    ).replace(
        'import Mathlib.Tactic.Omega',
        'import Mathlib.Tactic'
    )

    if new_content != content:
        with open(filepath, 'w') as f:
            f.write(new_content)
        print(f"Updated imports in {filepath}")

def main():
    ufrf_dir = 'UFRF'
    if not os.path.exists(ufrf_dir):
        print(f"Directory {ufrf_dir} not found")
        return

    for filename in os.listdir(ufrf_dir):
        if filename.endswith(".lean"):
            replace_imports(os.path.join(ufrf_dir, filename))

if __name__ == "__main__":
    main()
