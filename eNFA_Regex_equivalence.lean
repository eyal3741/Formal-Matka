import Mathlib.Tactic
import Mathlib.Computability.Language
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA
import Mathlib.Computability.EpsilonNFA

universe u v

variable {alphabet : Type u} { Q : Type v}

theorem Regex_to_εNFA (r: RegularExpression alphabet) : ∃ (A: εNFA alphabet Q), r.matches' = A.accepts := by
    sorry

theorem εNFA_to_Regex (A: εNFA alphabet Q) : ∃ (r: RegularExpression alphabet), r.matches' = A.accepts := by
    sorry
