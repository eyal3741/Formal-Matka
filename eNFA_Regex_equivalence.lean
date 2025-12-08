import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
open Set

universe u v

variable {alphabet : Type u} { Q : Type v}

theorem Regex_to_εNFA (r: RegularExpression alphabet) : ∃ (A: εNFA alphabet ℕ), r.matches' = A.accepts := by
    induction r
    case zero =>
        let A : εNFA alphabet ℕ := {
            start  := ∅
            accept := ∅
            step   := fun q a => ∅
        }
        use A
        simp only [RegularExpression.zero_def, RegularExpression.matches'_zero, Language.zero_def, εNFA.accepts]
        simp only [mem_empty_iff_false, false_and, exists_false, setOf_false, ne_eq, not_true_eq_false, A]

    case epsilon =>
        let A : εNFA alphabet ℕ := {
            start  := {0}
            accept := {0}
            step   := fun q a => ∅
        }
        use A
        simp only [RegularExpression.one_def, RegularExpression.matches'_epsilon, Language.one_def]
        rw [@Language.ext_iff]
        intro x
        rw [@mem_singleton_iff]

        have accepts_non_empty : A.accept ∩ (A.eval []) ≠ ∅ := by
            unfold εNFA.eval εNFA.evalFrom
            simp
            rw [@singleton_inter_eq_empty]
            push_neg
            constructor
            exact rfl

        constructor
        case mp =>
            intro hx
            subst hx
            unfold εNFA.accepts
            simp_all only [εNFA.eval_nil, ne_eq, singleton_inter_eq_empty, not_not, mem_singleton_iff, exists_eq_left, A]
            exact accepts_non_empty
        case mpr =>
            intro hx

            induction x
            case nil => tauto
            case cons σ tail _ =>
                rw [@List.eq_nil_iff_length_eq_zero]
                have : (σ :: tail).length ≠ 0 := by
                    exact Ne.symm (Nat.zero_ne_add_one tail.length)

                contradiction
    case char =>
        sorry
    case plus =>
        sorry
    case comp =>
        sorry
    case star =>
        sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry
