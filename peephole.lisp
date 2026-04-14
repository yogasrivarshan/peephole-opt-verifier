;; ============================================================
;; Peephole Optimization Verification in ACL2
;; Yoga Sri Varshan Varadharajan — yv2857
;; ============================================================
;;
;; We define a simple stack+register machine, implement two
;; peephole optimizations, and prove the optimizer correct.
;; The optimizer iterates a single-pass core to a fixpoint,
;; catching cascading redundancies.
;;
;; Optimizations:
;;   1. PUSH-POP elimination:  (PUSH n) (POP)  → ε
;;   2. Self-MOV elimination:  (MOV r r)        → ε
;;
;; Main theorem:
;;   (implies (consp st)
;;            (equal (run (peephole instrs) st)
;;                   (run instrs st)))

;; ============================================================
;; Phase 1: Language and Semantics
;; ============================================================

;; ------------------------------------------------------------
;; 1.1  Machine State
;; ------------------------------------------------------------
;; State = (cons stack registers)
;;   stack     — a list used as a LIFO stack
;;   registers — an association list mapping names to values

(defun mk-state (stk regs)
  (cons stk regs))

(defun get-stack (s)
  (car s))

(defun get-regs (s)
  (cdr s))

;; ------------------------------------------------------------
;; 1.2  Instruction Set
;; ------------------------------------------------------------

;; (PUSH n)  — encoded as the list (PUSH n)
(defun push-instrp (instr)
  (and (consp instr)
       (equal (car instr) 'PUSH)
       (consp (cdr instr))
       (not (consp (cddr instr)))))

(defun push-val (instr)
  (cadr instr))

;; (POP)  — encoded as the list (POP)
(defun pop-instrp (instr)
  (and (consp instr)
       (equal (car instr) 'POP)
       (not (consp (cdr instr)))))

;; (ADD)  — encoded as the list (ADD)
(defun add-instrp (instr)
  (and (consp instr)
       (equal (car instr) 'ADD)
       (not (consp (cdr instr)))))

;; (MOV r1 r2) — encoded as the list (MOV r1 r2)
;; Semantics: copy value of r2 into r1
(defun mov-instrp (instr)
  (and (consp instr)
       (equal (car instr) 'MOV)
       (consp (cdr instr))
       (consp (cddr instr))
       (not (consp (cdddr instr)))))

;; ------------------------------------------------------------
;; 1.3  Operational Semantics
;; ------------------------------------------------------------

;; Register accessors
(defun get-reg (r regs)
  (cdr (assoc-equal r regs)))

(defun set-reg (r v regs)
  (put-assoc-equal r v regs))

;; Single-instruction evaluator
;; NOTE: self-MOV (r1 = r2) returns s unchanged.  This mirrors
;; the real-hardware fact that r := r is a no-op, and lets us
;; prove the optimizer correct without hypotheses on register
;; existence.
(defun exec-instr (instr s)
  (let ((stk  (get-stack s))
        (regs (get-regs s)))
    (cond
     ;; PUSH n — push n onto the stack
     ((push-instrp instr)
      (mk-state (cons (push-val instr) stk) regs))

     ;; POP — remove the top element (no-op if stack empty)
     ((pop-instrp instr)
      (if (consp stk)
          (mk-state (cdr stk) regs)
        s))

     ;; ADD — pop two, push their sum (no-op if < 2 elements)
     ((add-instrp instr)
      (if (and (consp stk) (consp (cdr stk)))
          (mk-state (cons (+ (car stk) (cadr stk))
                          (cddr stk))
                    regs)
        s))

     ;; MOV r1 r2 — copy r2 into r1  (identity when r1=r2)
     ((mov-instrp instr)
      (let ((r1 (cadr instr))
            (r2 (caddr instr)))
        (if (equal r1 r2)
            s
          (mk-state stk (set-reg r1 (get-reg r2 regs) regs)))))

     ;; Unknown instruction — no-op
     (t s))))

;; Multi-instruction evaluator (recursive)
(defun run (instrs s)
  (if (endp instrs)
      s
    (run (cdr instrs) (exec-instr (car instrs) s))))

;; ============================================================
;; Phase 2: The Optimizer
;; ============================================================

;; The peephole optimizer eliminates:
;;   - (PUSH x) immediately followed by (POP)
;;   - (MOV r r)  (self-assignment)
;;
;; peephole-pass is the single-pass core.  The top-level peephole
;; function (defined after the supporting lemmas) iterates the
;; single pass to a fixpoint, catching cascading patterns such as
;; ((PUSH 1) (PUSH 2) (POP) (POP)) → nil.

(defun peephole-pass (instrs)
  (declare (xargs :measure (len instrs)))
  (if (endp instrs)
      nil
    (let ((i1   (car instrs))
          (rest (cdr instrs)))
      (if (endp rest)
          ;; --- exactly one instruction left ---
          (if (and (mov-instrp i1)
                   (equal (cadr i1) (caddr i1)))
              (peephole-pass rest)             ; drop self-MOV
            (cons i1 (peephole-pass rest)))    ; keep it
        ;; --- at least two instructions ---
        (let ((i2    (car rest))
              (rest2 (cdr rest)))
          ;; Pattern 1: PUSH-POP elimination
          (if (and (push-instrp i1)
                   (pop-instrp i2))
              (peephole-pass rest2)            ; drop both

            ;; Pattern 2: Self-MOV elimination
            (if (and (mov-instrp i1)
                     (equal (cadr i1) (caddr i1)))
                (peephole-pass rest)           ; drop self-MOV

              ;; No pattern matched — keep i1, optimize the tail
              (cons i1 (peephole-pass rest)))))))))

;; ============================================================
;; Phase 3: Proof Infrastructure (Lemmas)
;; ============================================================

;; ------------------------------------------------------------
;; 3.1  Termination helpers (linear rules)
;; ------------------------------------------------------------
;; The optimizer uses (cdr rest) = (cddr instrs) in the
;; PUSH-POP branch.  These linear rules help ACL2 see that
;; the measure (len instrs) strictly decreases.

(defthm len-cdr-<
  (implies (consp x)
           (< (len (cdr x)) (len x)))
  :rule-classes :linear)

(defthm len-cddr-<
  (implies (and (consp x) (consp (cdr x)))
           (< (len (cddr x)) (len x)))
  :rule-classes :linear)

;; ------------------------------------------------------------
;; 3.2  Frame Lemma: Self-MOV is a no-op
;; ------------------------------------------------------------
;; Built into exec-instr's MOV branch: when r1=r2, return s.

(defthm mov-self-no-op
  (implies (equal r1 r2)
           (equal (exec-instr (list 'MOV r1 r2) s) s)))

;; ------------------------------------------------------------
;; 3.3  Step Equivalence: PUSH then POP cancels
;; ------------------------------------------------------------
;; (exec-instr POP (exec-instr (PUSH n) s))
;;   = (mk-state (cdr (cons n stk)) regs)
;;   = (mk-state stk regs)
;;   = (cons (car s) (cdr s))
;;   = s                   when (consp s)
;;
;; '(POP) is a quoted constant (no free variables).
;; (list 'PUSH n) uses LIST because n is a free variable
;; that ACL2 must universally quantify over.

(defthm push-pop-cancel
  (implies (consp s)
           (equal (exec-instr '(POP) (exec-instr (list 'PUSH n) s))
                  s)))

;; ------------------------------------------------------------
;; 3.4  consp preservation through exec-instr and run
;; ------------------------------------------------------------

(defthm consp-exec-instr
  (implies (consp s)
           (consp (exec-instr instr s))))

(defthm consp-run
  (implies (consp s)
           (consp (run instrs s))))

;; ============================================================
;; Phase 4: The Main Correctness Theorem
;; ============================================================

;; ------------------------------------------------------------
;; 4.1  Custom induction scheme
;; ------------------------------------------------------------
;; Mirrors the recursion of peephole-pass while threading state
;; so ACL2 can see how run unfolds in lockstep.

(defun peephole-pass-induct (instrs st)
  (declare (xargs :measure (len instrs)))
  (if (endp instrs)
      st
    (let ((i1   (car instrs))
          (rest (cdr instrs)))
      (if (endp rest)
          ;; single instruction
          (if (and (mov-instrp i1) (equal (cadr i1) (caddr i1)))
              (peephole-pass-induct rest st)
            (peephole-pass-induct rest (exec-instr i1 st)))
        (let ((i2    (car rest))
              (rest2 (cdr rest)))
          (if (and (push-instrp i1) (pop-instrp i2))
              ;; PUSH-POP  →  skip both
              (peephole-pass-induct rest2 st)
            (if (and (mov-instrp i1) (equal (cadr i1) (caddr i1)))
                ;; self-MOV  →  skip
                (peephole-pass-induct rest st)
              ;; default → keep i1, step st
              (peephole-pass-induct rest (exec-instr i1 st)))))))))

;; ------------------------------------------------------------
;; 4.2  Single-pass correctness
;; ------------------------------------------------------------

(defthm peephole-pass-correct
  (implies (consp st)
           (equal (run (peephole-pass instrs) st)
                  (run instrs st)))
  :hints (("Goal" :induct (peephole-pass-induct instrs st))))

;; ------------------------------------------------------------
;; 4.3  Length properties of peephole-pass
;; ------------------------------------------------------------
;; The single pass never increases program length, and when it
;; changes anything it strictly shrinks it.  These two facts let
;; ACL2 admit the multi-pass fixpoint below.

(defthm peephole-pass-len
  (<= (len (peephole-pass instrs)) (len instrs))
  :rule-classes :linear)

(defthm peephole-pass-shrinks-when-changed
  (implies (not (equal (peephole-pass instrs) instrs))
           (< (len (peephole-pass instrs)) (len instrs)))
  :rule-classes :linear)

;; ------------------------------------------------------------
;; 4.4  Multi-pass fixpoint optimizer
;; ------------------------------------------------------------
;; Iterate peephole-pass until no further reductions occur.
;; Terminates because each productive pass strictly shrinks
;; the instruction list (by peephole-pass-shrinks-when-changed).

(defun peephole (instrs)
  (declare (xargs :measure (len instrs)))
  (let ((result (peephole-pass instrs)))
    (if (equal result instrs)
        result
      (peephole result))))

;; ------------------------------------------------------------
;; 4.5  Multi-pass correctness
;; ------------------------------------------------------------

(defthm peephole-correct
  (implies (consp st)
           (equal (run (peephole instrs) st)
                  (run instrs st))))

;; ============================================================
;; Phase 5: Tests  (assert-event)
;; ============================================================

;; A well-formed initial state: empty stack, no registers
(defconst *s0* (cons nil nil))

;; --- Optimizer output tests ---

;; PUSH-POP elimination
(assert-event
 (equal (peephole '((PUSH 3) (POP) (PUSH 5)))
        '((PUSH 5))))

;; Self-MOV elimination
(assert-event
 (equal (peephole '((MOV R1 R1) (PUSH 7)))
        '((PUSH 7))))

;; Combined patterns
(assert-event
 (equal (peephole '((MOV R1 R1) (PUSH 10) (POP) (PUSH 42)))
        '((PUSH 42))))

;; No optimization needed — preserved
(assert-event
 (equal (peephole '((PUSH 1) (PUSH 2) (ADD) (MOV R1 R2)))
        '((PUSH 1) (PUSH 2) (ADD) (MOV R1 R2))))

;; Empty program
(assert-event
 (equal (peephole nil) nil))

;; Cascading pattern — the fixpoint catches both layers:
;; pass 1 removes inner (PUSH 2)(POP), pass 2 removes (PUSH 1)(POP)
(assert-event
 (equal (peephole '((PUSH 1) (PUSH 2) (POP) (POP)))
        nil))

;; Multiple consecutive self-MOVs — all removed
(assert-event
 (equal (peephole '((MOV R1 R1) (MOV R2 R2) (MOV R3 R3)))
        nil))

;; PUSH-POP at the tail of a program
(assert-event
 (equal (peephole '((PUSH 1) (PUSH 2) (ADD) (PUSH 99) (POP)))
        '((PUSH 1) (PUSH 2) (ADD))))

;; Single self-MOV as the only instruction
(assert-event
 (equal (peephole '((MOV X X)))
        nil))

;; Single non-self MOV — preserved
(assert-event
 (equal (peephole '((MOV R1 R2)))
        '((MOV R1 R2))))

;; --- Semantic correctness on concrete programs ---

;; PUSH-POP program
(assert-event
 (equal (run (peephole '((PUSH 3) (POP) (PUSH 5))) *s0*)
        (run '((PUSH 3) (POP) (PUSH 5)) *s0*)))

;; Self-MOV program
(assert-event
 (equal (run (peephole '((MOV R1 R1) (PUSH 7))) *s0*)
        (run '((MOV R1 R1) (PUSH 7)) *s0*)))

;; Mixed program with ADD
(assert-event
 (equal (run (peephole '((PUSH 1) (PUSH 2) (ADD)
                          (MOV R1 R1) (PUSH 10) (POP))) *s0*)
        (run '((PUSH 1) (PUSH 2) (ADD)
                (MOV R1 R1) (PUSH 10) (POP)) *s0*)))

;; Larger mixed program
(assert-event
 (equal (run (peephole '((PUSH 5) (PUSH 5) (ADD)
                          (PUSH 3) (POP)
                          (MOV X X)
                          (PUSH 7))) *s0*)
        (run '((PUSH 5) (PUSH 5) (ADD)
                (PUSH 3) (POP)
                (MOV X X)
                (PUSH 7)) *s0*)))

;; ============================================================
;; End of peephole.lisp
;; ============================================================
