#!/usr/bin/env python3
"""Untrusted SymPy certificate producer for CertifiedTorusPreimage.

Input JSON: {"rows": m, "cols": n, "matrix": [[...], ...], "target": [...]}
Output JSON contains integer data, a solution or obstructing row, and a kernel
generating matrix. --lean emits a kernel-checkable fixture to stdout instead.
Requires SymPy 1.14.0. No SymPy result is trusted by the Lean theorem.
"""

import argparse
import json
import sys
import subprocess
from pathlib import Path
import os

# Fix the arithmetic backend so generated regression fixtures are reproducible
# even on hosts with optional FLINT/gmpy integrations installed.
os.environ["SYMPY_GROUND_TYPES"] = "python"

from sympy import Matrix, eye, zeros, ZZ
from sympy import __version__ as sympy_version
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp


def integers(value):
    return isinstance(value, int) and not isinstance(value, bool)


def generate(data):
    m, n = data["rows"], data["cols"]
    if not integers(m) or not integers(n) or min(m, n) < 0:
        raise ValueError("rows and cols must be nonnegative integers")
    rows, target = data["matrix"], data["target"]
    if len(rows) != m or any(len(row) != n for row in rows):
        raise ValueError("matrix dimensions do not match rows and cols")
    if len(target) != m or not all(integers(x) for row in rows for x in row):
        raise ValueError("invalid matrix entries or target dimension")
    if not all(integers(x) for x in target):
        raise ValueError("target entries must be integers")
    A = Matrix(m, n, [x for row in rows for x in row])
    if m == 0 or n == 0:
        S, L, V = zeros(m, n), eye(m), eye(n)
    else:
        dm = DomainMatrix([[ZZ(x) for x in row] for row in rows], (m, n), ZZ)
        sm, lm, vm = smith_normal_decomp(dm)
        S, L, V = sm.to_Matrix(), lm.to_Matrix(), vm.to_Matrix()
    Linv = L.inv()
    d = [int(S[i, i]) if i < n else 0 for i in range(m)]
    R = zeros(n, m)
    for i in range(min(m, n)):
        if d[i]:
            R[:, i] = V[:, i]
    LA = L * A
    T = zeros(m, n)
    for i in range(m):
        for j in range(n):
            if d[i]:
                if LA[i, j] % d[i]:
                    raise ArithmeticError("nonintegral certificate quotient")
                T[i, j] = LA[i, j] / d[i]
            elif LA[i, j] != 0:
                raise ArithmeticError("nonzero entry in a free obstruction row")
    D = Matrix.diag(*d) if m else zeros(0, 0)
    if Linv * L != eye(m) or LA != D * T or LA * R != D:
        raise ArithmeticError("certificate identities failed")
    K = eye(n) - R * T
    if A * K != zeros(m, n):
        raise ArithmeticError("kernel generator check failed")
    z = Matrix(m, 1, target)
    y = L * z
    failed = next((i for i in range(m) if
                   (y[i] != 0 if d[i] == 0 else y[i] % d[i] != 0)), None)
    candidate = None
    if failed is None:
        quotients = Matrix(m, 1, [y[i] / d[i] if d[i] else 0 for i in range(m)])
        candidate = R * quotients
        if A * candidate != z:
            raise ArithmeticError("candidate check failed")
    def matrix_list(B):
        return [[int(B[i, j]) for j in range(B.cols)] for i in range(B.rows)]
    return {
        "rows": m, "cols": n, "matrix": rows, "target": target,
        "certificate": {"L": matrix_list(L), "Linv": matrix_list(Linv),
                        "R": matrix_list(R), "T": matrix_list(T), "d": d},
        "kernel_generator": matrix_list(K),
        "outcome": ({"solved": [int(x) for x in candidate]} if failed is None
                    else {"obstructed": failed, "modulus": d[failed],
                          "transformed_target": int(y[failed]),
                          "row": matrix_list(L)[failed]}),
    }


def lean_vector(xs):
    return "![]" if not xs else "![" + ", ".join(str(x) for x in xs) + "]"


def lean_matrix(rows):
    return "![]" if not rows else "![" + ", ".join(lean_vector(r) for r in rows) + "]"


def emit_lean(result, name):
    m, n = result["rows"], result["cols"]
    c = result["certificate"]
    lines = [f"namespace {name}", f"def A : Mat {m} {n} := {lean_matrix(result['matrix'])}",
             f"def z : Vec {m} := {lean_vector(result['target'])}",
             f"def cert : Certificate {m} {n} where"]
    lines += [f"  {field} := {lean_matrix(c[field])}" for field in ("L", "Linv", "R", "T")]
    lines += [f"  d := {lean_vector(c['d'])}",
              "theorem valid : cert.Valid A := by decide",
              f"theorem kernel_data : cert.kernelGenerator = {lean_matrix(result['kernel_generator'])} := by decide"]
    outcome = result["outcome"]
    if "solved" in outcome:
        answer = f".solved {lean_vector(outcome['solved'])}"
        failure = "none"
    else:
        answer = f".obstructed ⟨{outcome['obstructed']}, by decide⟩"
        failure = f"some ⟨{outcome['obstructed']}, by decide⟩"
        i = f"(⟨{outcome['obstructed']}, by decide⟩ : Fin {m})"
        lines += [f"theorem obstruction_data : cert.d {i} = {outcome['modulus']} ∧",
                  f"    cert.transformed z {i} = {outcome['transformed_target']} ∧",
                  f"    cert.L {i} = {lean_vector(outcome['row'])} := by decide"]
    lines += [f"theorem answer : solve A cert z = {answer} := by",
              f"  have hf : cert.firstFailure z = {failure} := by decide",
              "  rw [solve, if_pos valid, hf]"]
    if "solved" in outcome:
        lines += [f"  exact congrArg Outcome.solved (by decide : cert.candidate z = {lean_vector(outcome['solved'])})"]
    lines += ["theorem topological_answer : Torus.TopologicallyCorrect A cert z (solve A cert z) :=",
              "  Torus.solve_topologically_correct A cert z",
              f"theorem checked_answer : Torus.TopologicallyCorrect A cert z ({answer}) := by",
              "  rw [← answer]",
              "  exact topological_answer", f"end {name}"]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="input JSON file; - reads stdin")
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--lean", action="store_true")
    output.add_argument("--verify", action="store_true",
                        help="check the generated certificate and answer in Lean before output")
    parser.add_argument("--name", default="GeneratedCase")
    args = parser.parse_args()
    if not args.name.isascii() or not args.name.isidentifier():
        parser.error("--name must be a simple ASCII Lean identifier")
    try:
        if args.input == "-":
            data = json.load(sys.stdin)
        else:
            with open(args.input, encoding="utf-8") as stream:
                data = json.load(stream)
        result = generate(data)
        if args.verify:
            repo = Path(__file__).resolve().parents[1]
            build = subprocess.run(
                ["lake", "build", "ComputationalPaths.Path.Topology.CertifiedTorusPreimage"],
                cwd=repo, capture_output=True, text=True, timeout=300)
            if build.returncode:
                parser.exit(1, "Lean dependency build failed; no verified answer.\n" +
                            build.stdout + build.stderr)
            source = ("import ComputationalPaths.Path.Topology.CertifiedTorusPreimage\n"
                      "open ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage\n"
                      "set_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n" +
                      emit_lean(result, args.name))
            checked = subprocess.run(["lake", "env", "lean", "--stdin", "-M", "4096"],
                                     cwd=repo, input=source, capture_output=True,
                                     text=True, timeout=300)
            if checked.returncode:
                parser.exit(1, "Lean verification failed; no verified answer.\n" +
                            checked.stdout + checked.stderr)
            result["verification"] = {
                "lean_kernel": "accepted",
                "scope": "certificate, literal answer, kernel matrix, obstruction data, and topology"}
        print(emit_lean(result, args.name) if args.lean else json.dumps(result, indent=2))
    except subprocess.TimeoutExpired:
        parser.exit(1, "Lean verification timed out; no verified answer.\n")
    except (ValueError, KeyError, TypeError, ArithmeticError) as error:
        parser.exit(2, f"invalid input or certificate generation failure: {error}\n")


if __name__ == "__main__":
    main()
