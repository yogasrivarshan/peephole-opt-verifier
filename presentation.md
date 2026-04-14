# Final Presentation: Verification of Peephole Optimizations in ACL2

All slides: footer = **Yoga Sri Varshan Varadharajan — EID: yv2857**

---

## Slide 1 — Project Overview and Motivation

**Title:** Verification of Peephole Optimizations in ACL2

➔ Peephole optimizations are local compiler optimizations that replace
  inefficient instruction sequences with more efficient ones without
  changing program semantics

◆ `(PUSH n) (POP)` → ε  (redundant push-pop)
◆ `(MOV R1 R1)` → ε  (self-assignment)

➔ Goal: formally prove in ACL2 that the optimizer preserves program
  semantics for **all** inputs — not just tests

➔ Key result:

```lisp
(defthm peephole-correct
  (implies (consp st)
           (equal (run (peephole instrs) st)
                  (run instrs st))))
```

➔ Multi-pass fixpoint design catches cascading redundancies

◆ `((PUSH 1) (PUSH 2) (POP) (POP))` → `nil`

---

## Slide 2 — Language and Machine Model

**Title:** Language and Machine Model

➔ Instruction Set (4 instructions)

◆ `(PUSH n)` — push constant onto stack
◆ `(POP)` — remove top of stack
◆ `(ADD)` — add top two stack elements
◆ `(MOV r1 r2)` — copy register r2 into r1

➔ Machine State = `(cons stack registers)`

◆ Stack: LIFO list of values
◆ Registers: association list mapping names to values

➔ Operational Semantics:

```lisp
(defun exec-instr (instr s)
  (let ((stk (get-stack s)) (regs (get-regs s)))
    (cond
      ((push-instrp instr)
       (mk-state (cons (push-val instr) stk) regs))
      ((pop-instrp instr)
       (if (consp stk) (mk-state (cdr stk) regs) s))
      ((add-instrp instr) ...)
      ((mov-instrp instr)
       (if (equal r1 r2) s       ;; self-MOV: no-op
         (mk-state stk (set-reg r1 (get-reg r2 regs) regs))))
      (t s))))
```

➔ Evaluator: `(run instrs s)` — executes instructions left-to-right recursively

---

## Slide 3 — Two-Layer Optimizer Architecture

**Title:** Two-Layer Optimizer Architecture

➔ Layer 1: `peephole-pass` — single left-to-right scan

◆ Pattern 1: `(PUSH x) (POP)` → drop both
◆ Pattern 2: `(MOV r r)` → drop
◆ Default: keep instruction, recurse on tail

➔ Layer 2: `peephole` — iterate to fixpoint

```lisp
(defun peephole (instrs)
  (let ((result (peephole-pass instrs)))
    (if (equal result instrs)
        result
      (peephole result))))
```

➔ Why fixpoint? Single pass misses cascading patterns

◆ Trace:

```
Input:   (PUSH 1) (PUSH 2) (POP) (POP)
Pass 1:  (PUSH 1) (POP)            ← inner pair removed
Pass 2:  nil                        ← revealed pair removed
Pass 3:  nil = input → stop         ← fixpoint reached
```

---

## Slide 4 — Proof Strategy

**Title:** Proof Strategy

➔ Two-tier proof

◆ Tier 1: `peephole-pass-correct` — single pass preserves semantics
◆ Tier 2: `peephole-correct` — fixpoint preserves semantics (follows from Tier 1)

➔ Key Lemmas:

```lisp
;; Self-MOV is a no-op
(defthm mov-self-no-op
  (implies (equal r1 r2)
           (equal (exec-instr (list 'MOV r1 r2) s) s)))

;; PUSH then POP cancels
(defthm push-pop-cancel
  (implies (consp s)
           (equal (exec-instr '(POP)
                    (exec-instr (list 'PUSH n) s))
                  s)))
```

➔ Fixpoint termination requires two length lemmas

◆ `peephole-pass-len`: output length ≤ input length
◆ `peephole-pass-shrinks-when-changed`: if output differs, it is strictly shorter

➔ Custom induction scheme `peephole-pass-induct` mirrors `peephole-pass`
  case structure while threading state like `run`

➔ Proof dependency chain:

```
mov-self-no-op ───────┐
push-pop-cancel ──────┼──▶ peephole-pass-correct ──┐
consp-run ────────────┘                             ├──▶ peephole-correct
peephole-pass-shrinks ──▶ peephole (admitted) ──────┘
```

---

## Slide 5 — Results

**Title:** Results

➔ All definitions admitted, all theorems proved, all 14 tests passed

➔ Summary:

| Form                                  | Result  |
|---------------------------------------|---------|
| `peephole-pass`                       | Admitted |
| `peephole-pass-correct`               | Q.E.D.  |
| `peephole-pass-len`                   | Q.E.D.  |
| `peephole-pass-shrinks-when-changed`  | Q.E.D.  |
| `peephole` (fixpoint)                 | Admitted |
| `peephole-correct`                    | Q.E.D.  |
| 14 `assert-event` tests              | All PASSED |

➔ Sample test results:

```lisp
;; Cascading pattern fully reduced
(assert-event
  (equal (peephole '((PUSH 1) (PUSH 2) (POP) (POP)))
         nil))

;; Semantic correctness on concrete program
(assert-event
  (equal (run (peephole '((PUSH 5) (PUSH 5) (ADD)
                           (PUSH 3) (POP)
                           (MOV X X) (PUSH 7))) *s0*)
         (run '((PUSH 5) (PUSH 5) (ADD)
                 (PUSH 3) (POP)
                 (MOV X X) (PUSH 7)) *s0*)))
```

➔ Key takeaway: the theorem covers **all** possible programs and states
  — not just the test cases

➔ Source: single self-contained file `peephole.lisp`
