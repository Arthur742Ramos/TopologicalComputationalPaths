# Certified preimages of finite-torus loop classes

Status: implemented research prototype, 2026-09-06. No publication, registry
acceptance, independent expert review, or mathematical priority is claimed.

## Abstract

For an arbitrary rectangular integer matrix A and an integer target winding z,
we implement a certificate-driven solver for preimages of the standard target
loop class under the induced map between finite tori. A successful answer gives
a concrete source winding and a finite integer matrix parameterizing every
source homotopy class with that image. A negative answer identifies a row
divisibility obstruction, including zero-modulus equations in rank-deficient
cases. Malformed certificates are rejected separately. Lean proves that valid
certificates exist for every matrix and that each executed answer has its stated
meaning for fixed, explicitly defined torus loops and maps. An untrusted SymPy
producer supplies certificate data; its output is checked by Lean. We do not
claim a verified producer or a complexity theorem.

## 1. Problem and fixed semantics

Let T^n = (R/Z)^n with zero basepoint. For z in Z^n, the standard loop has
coordinate t ↦ t z_i mod Z. Its based homotopy class is denoted [z]. An integer
m-by-n matrix A defines the continuous map F_A(x)_i = sum_j A_ij x_j. The
problem is to describe all based loop classes q with (F_A)_*(q) = [z].

This is a preimage problem for **homotopy classes**. It is not a claim that
arbitrary paths lift pointwise, that F_A is a covering map, or that every
continuous path admits a computable finite encoding. Input vectors encode
standard representatives. The existing winding classification proves that
these represent all based loop classes, but computing winding from an arbitrary
black-box continuous loop is outside the executable interface.

## 2. Certificate and algorithm

The certificate is integer data (L, Linv, R, T, d), with dimensions
L,Linv: m-by-m; R: n-by-m; T: m-by-n; d: m. The checker verifies:

1. Linv L = I;
2. LA = diag(d) T;
3. LAR = diag(d);
4. each row T_i is zero whenever d_i = 0.

There is no supplied winding function, arbitrary equivalence, cost observable,
or assumed solution in this data. We need neither ordered Smith factors nor
positive factors. A certificate may therefore come from any suitable producer.

After validation, compute y = Lz. If some d_i does not divide y_i, return the
first such row. Otherwise compute u_i = y_i / d_i, taking 0/0 = 0, and return
x0 = Ru together with K = I - RT. Every solution class is exactly

    [x0 + K v],  v in Z^n.

K is a generating matrix and a projection onto the integer kernel, not
necessarily a basis. Parameters can be redundant; we do not claim uniqueness
of v or minimal encoding size.

## 3. Correctness argument and formal endpoints

Necessity follows from LA = diag(d)T: if Ax=z, every d_i divides (Lz)_i.
For sufficiency, LARu=diag(d)u=Lz; Linv L=I then gives ARu=z. The argument
includes d_i=0 because feasibility forces y_i=0 in that row.

Next LAK=LA-diag(d)T=0, hence AK=0. If Ax=0, then diag(d)Tx=0.
Nonzero d_i force (Tx)_i=0 by cancellation; zero d_i force it by condition 4.
Thus Kx=x for every kernel vector. This proves K^2=K and the complete affine
solution formula. The fixed winding classification transports it to actual
loop homotopy classes. For canonical representatives the candidate's mapped
loop even equals the standard target loop pointwise.

The fourth certificate condition is essential to this proof. A tampering test
changes a zero-modulus row while preserving the first three identities; the
checker rejects the certificate. Without the condition, the displayed K could
omit genuine kernel directions.

The principal declarations, under
`ComputationalPaths.Path.GeometricTopology.CertifiedTorusPreimage`, are:

- `solve_correct`: every returned algebraic answer is sound, with all solutions.
- `Certificate.kernel_iff` and `kernelGenerator_idempotent`: the computed K is
  an exact integer-kernel projection.
- `Torus.candidate_loop`: the successful candidate specifies a concrete loop.
- `Torus.solve_topologically_correct`: the answer has its literal topological meaning.
- `exists_valid_certificate`: the certificate format covers every rectangular A.

The last theorem uses Mathlib's noncomputable Smith basis only to prove
existence. It is **not** used to execute `solve`. The standalone Comparator
endpoint `TorusPreimageSubmission.main_result` selects existence of valid
certificates and topological correctness for every input certificate and target.
Its statement is in `PreimageChallenge.lean`, with only Mathlib imports, and its
implementation is in `PreimageSolution.lean`. The older broad follow-up remains
a separate artifact and is not silently replaced in the registry metadata.

## 4. Executable boundary and reproduction

The producer `scripts/torus-preimage-certificate.py` uses SymPy 1.14.0's
`smith_normal_decomp`. Given S = LAV, it constructs R from the active columns
of V and forms T by exact row division. SymPy, Python, JSON output, and these
producer-side checks are untrusted. Generated Lean fixtures establish both
certificate validity and the literal solver answer using `decide`, without
`native_decide`. They also check the serialized kernel matrix and the negative
answer's modulus, transformed target, and row against the Lean definitions.
A producer bug cannot establish a false Lean theorem; it can
still cause generation failure or excessive resource use.

```sh
python3 -m pip install -r scripts/requirements-preimage.txt
bash scripts/check-preimage.sh
bash scripts/verify-comparator.sh comparator-preimage.json
python3 scripts/torus-preimage-certificate.py examples/preimage-coupled.json --verify
```

The producer's `--lean` output is a namespace fragment intended after the import
and options shown in `PreimageTests.lean`. The checked-in fixtures are generated
by `python3 scripts/test-torus-preimage.py --lean`; the quality gate checks exact
regeneration parity. `--verify` builds the dependency and checks the generated
proof through Lean's stdin interface before labeling its JSON answer verified.
Without that flag the JSON is only an untrusted producer result. Unknown input
fields cannot inject verification status into the output. These tools do not
transmit input data to an external service; Lake may fetch build dependencies
when they are not already cached.

## 5. Application and evaluation

The parameterized application has three source phases and four observed
winding channels, with rows (2,4,0), (0,3,3), (2,7,3), (4,8,0). For 2|a and 3|b,
all source classes producing (a,b,a+b,2a) are precisely

    [(a/2 - 2t, t, b/3 - t)],  t in Z.

Changing either redundant channel inconsistently makes the preimage empty.
`TorusConstraintApplication.lean` proves both statements for all parameters.
This is a worked application and regression family, not evidence by itself of
nonroutine research significance.

The 13 kernel-checked fixtures cover empty dimensions, no variables, no
constraints, negative matrix entries, divisibility failure, free obstructions,
wide/tall/singular maps, and coupled observations. Separate adversarial tests
alter certificate fields. Another 100 seeded known-image inputs exercise the
Python producer; those randomized cases are not all replayed by Lean.

Five additional deterministic benchmark fixtures use matrices from 3-by-5 to
8-by-5 and 5-by-8, with full-rank and dependent-row cases. Their certificates
and answers are also kernel checked. `evidence/preimage-producer-benchmark.json`
records dimensions, certificate JSON sizes, producer timings, and environment.
Those timings measure the Python producer only, not certificate replay or the
Lean solver. They are small regression measurements, not a scalability study,
algorithm comparison, or asymptotic complexity result.

## 6. Prior work and contribution boundary

| Source inspected | Existing contribution | Relation to this artifact |
| --- | --- | --- |
| [Hatcher, Algebraic Topology, Chapter 1](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) | Classical circle and finite-torus fundamental groups | Background, not a novelty claim here |
| [Cano et al., 2016](https://arxiv.org/abs/1601.07472) | Verified Smith algorithms and finitely presented module classification in Coq | Rules out treating verified Smith computation as new in general |
| [Divasón, AFP, 2020](https://isa-afp.org/entries/Smith_Normal_Form.html) | Verified Smith algorithm over Euclidean domains and more general existence/uniqueness results | Broader algebraic background; not a Lean dependency |
| [Ji, 2026](https://arxiv.org/abs/2607.22524) and [artifact scope](https://github.com/JJYYY-JJY/lean-normal-forms/blob/3f80f9524d88a124a49330eb36a2acb5ed41e179/SCOPE.md) | Lean value-producing Smith reduction and arithmetic bit-cost bounds for nonsingular square matrices | Published scope excludes rectangular/singular inputs and applications; our checker is complementary, not a stronger verified algorithm |
| [SymPy normal-form implementation](https://github.com/sympy/sympy/blob/sympy-1.14.0/sympy/polys/matrices/normalforms.py) | Executable Smith decomposition with transformation matrices | Actual untrusted producer dependency; credited and pinned |

The September 6 comparison examined these published descriptions, the Lean
artifact's scope and README, and the installed SymPy producer implementation.
The external formalizations were not independently replayed. This is not an
exhaustive priority survey. No external code was copied into the Lean proofs.

The implemented contribution is a compact, complete certificate interface
joining computation, all-solution parameterization, and fixed torus semantics
across all dimensions and ranks. The underlying mathematics is classical.
Whether this interface and its formalization warrant a research note remains
an open editorial question. The worked example and smoke benchmarks do not
establish that threshold. Independent expert comparison and a substantial
research use case remain necessary before presenting the artifact as
"extremely strong" or resubmitting on a novelty-based claim.
