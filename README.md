# Peephole Optimization Verification in ACL2

Formal verification of a peephole optimizer for a simple stack/register machine, mechanically proved correct in the [ACL2 theorem prover](https://www.cs.utexas.edu/users/moore/acl2/).

## What This Project Does

A peephole optimizer scans a program's instruction list and removes redundant patterns:

| Pattern | Example | Action |
|---------|---------|--------|
| PUSH-POP | `(PUSH 3) (POP)` | Remove both |
| Self-MOV | `(MOV R1 R1)` | Remove |

The optimizer iterates a single-pass core to a **fixpoint**, catching cascading redundancies (e.g. `(PUSH 1) (PUSH 2) (POP) (POP)` reduces to `nil`).

We prove the optimizer **correct** for all possible inputs:

```lisp
(defthm peephole-correct
  (implies (consp st)
           (equal (run (peephole instrs) st)
                  (run instrs st))))
```

This is a mathematical proof checked by ACL2 — not a test suite.

## Files

| File | Description |
|------|-------------|
| `peephole.lisp` | Complete ACL2 source: machine model, optimizer, lemmas, proofs, and tests |
| `report.md` | Full project report with line-by-line walkthrough |
| `presentation.md` | 5-slide final presentation content |

## Running

Requires [ACL2](https://www.cs.utexas.edu/users/moore/acl2/current/HTML/installation/installation.html) (tested with v8.6).

```bash
# Start ACL2
/path/to/saved_acl2

# At the ACL2 !> prompt, load the file
(ld "peephole.lisp")
```

All definitions should be admitted, all theorems proved (Q.E.D.), and all 14 tests passed.

## Architecture

```
peephole-pass       Single left-to-right scan removing PUSH-POP and self-MOV
    │
    ▼
peephole            Iterates peephole-pass until fixpoint (no changes)
```

**Proof chain:**

```
mov-self-no-op ───────┐
push-pop-cancel ──────┼──▶ peephole-pass-correct ──┐
consp-run ────────────┘                             ├──▶ peephole-correct
peephole-pass-shrinks ──▶ peephole (admitted) ──────┘
```

## Author

Yoga Sri Varshan Varadharajan (yv2857)
