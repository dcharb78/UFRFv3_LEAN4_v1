# UFRF Lean Project: 3rd Party Validation Guide

To independently verify the mathematical proofs in this repository, you need the following standard Lean 4 environment.

## 1. Required Files

The following files constitute the "Source of Truth" for the project. If you are receiving this as a zip file, ensure these are present:

*   **`lean-toolchain`**: Specifies the exact Lean compiler version (e.g., `v4.15.0-rc1`).
*   **`lakefile.lean`**: The build configuration identifying dependencies (Mathlib).
*   **`lake-manifest.json`**: The lockfile ensuring you use the exact same version of Mathlib that successfully built this project.
*   **`UFRF/`**: The directory containing all `.lean` source files.

## 2. Prerequisites

*   **Lean 4**: Install via [elan](https://github.com/leanprover/elan) (the standard Lean version manager).
    ```bash
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
    *On Mac with Homebrew, you can also use `brew install elan-init`.*

## 3. Verification Steps

1.  **Navigate to the project root** (where `lakefile.lean` is located).
2.  **Get Dependencies**:
    ```bash
    lake update
    ```
    *This downloads Mathlib4 based on the manifest.*
3.  **Build and Verify**:
    ```bash
    lake build
    ```

## 4. Interpreting Results

*   **Success**: If `lake build` completes with exit code 0 and no error messages, **all proofs in the project are formally verified** by the Lean kernel.
*   **Code Transparency**:
    *   This project contains **NO `sorry`** placeholders (axioms admitted without proof).
    *   This project contains **NO `native_decide`** tactics (proofs relying on opacity).
    *   All theorems are proven essentially or constructionally from the base axioms defined in `Trinity.lean`.
