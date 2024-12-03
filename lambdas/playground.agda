module lambdas.playground where

-- In this file, we see what goes wrong when we try to substitute in a value that might
-- have free variables.

open import lambdas.language
open import lambdas.properties

open import Data.String using (_≟_)

open import Relation.Nullary using (yes; no; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

sub-pres′ : ∀ {Γ A B b y V}
    → Γ , y ⦂ A ⊢ b ⦂ B
    → Γ ⊢ V ⦂ A
    → Γ ⊢ b [ y := V ] ⦂ B
sub-pres′ ⊢true ⊢V = ⊢true
sub-pres′ ⊢false ⊢V = ⊢false
sub-pres′ ⊢zero ⊢V = ⊢zero
sub-pres′ (⊢if ⊢c ⊢th ⊢el) ⊢V = ⊢if (sub-pres′ ⊢c ⊢V) (sub-pres′ ⊢th ⊢V) (sub-pres′ ⊢el ⊢V)
sub-pres′ (⊢suc ⊢n) ⊢V = ⊢suc (sub-pres′ ⊢n ⊢V)
sub-pres′ (⊢zero? ⊢n) ⊢V = ⊢zero? (sub-pres′ ⊢n ⊢V)
sub-pres′ (⊢app ⊢f ⊢a) ⊢V = ⊢app (sub-pres′ ⊢f ⊢V) (sub-pres′ ⊢a ⊢V)
sub-pres′ {y = y} (⊢var {x = x} here) ⊢V with x ≟ y
... | yes refl = ⊢V
... | no  y≢y  = contradiction refl y≢y
sub-pres′ {y = y} (⊢var {x = x} (there x≢y x∈Γ)) ⊢V with x ≟ y
... | yes refl = contradiction refl x≢y
... | no  _    = ⊢var x∈Γ
sub-pres′ {Γ} {A} {B ⇒ C} {`λ x ⦂ B ⇒ b} {y} {V} (⊢lam {x = x} ⊢b) ⊢V with x ≟ y
... | yes refl = ⊢lam (weaken drop ⊢b)
... | no  x≢y  = let weak = weaken (swap x≢y) ⊢b in
    -- We need to prove that Γ , x ⦂ B ⊢ V ⦂ A
    -- BUT!  If V has free "x"s, it might not be true, we only know that Γ ⊢ V ⦂ A
    ⊢lam (sub-pres′ {V = V} weak {!   !})

preserve′ : ∀ {Γ t t′ T}
    → Γ ⊢ t ⦂ T
    → t —→ t′
    → Γ ⊢ t′ ⦂ T
preserve′ (⊢if ⊢c ⊢th ⊢el) if-true = ⊢th
preserve′ (⊢if ⊢c ⊢th ⊢el) if-false = ⊢el
preserve′ (⊢if ⊢c ⊢th ⊢el) (reduce-if c-step) = ⊢if (preserve′ ⊢c c-step) ⊢th ⊢el
preserve′ (⊢suc ⊢n) (reduce-suc n-step) = ⊢suc (preserve′ ⊢n n-step)
preserve′ (⊢zero? ⊢n) zero?-zero = ⊢true
preserve′ (⊢zero? ⊢n) (zero?-suc x) = ⊢false
preserve′ (⊢zero? ⊢n) (reduce-zero? n-step) = ⊢zero? (preserve′ ⊢n n-step)
preserve′ (⊢app ⊢f ⊢a) (reduce-func f-step) = ⊢app (preserve′ ⊢f f-step) ⊢a
preserve′ (⊢app ⊢f ⊢a) (reduce-arg _ a-step) = ⊢app ⊢f (preserve′ ⊢a a-step)
preserve′ (⊢app (⊢lam ⊢b) ⊢a) (subst a-val) = sub-pres′ ⊢b ⊢a
