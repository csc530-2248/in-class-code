# Playground

In this file, we see what goes wrong when we try to substitute in a value that might
have free variables.

## Imports

```agda
module lambdas.playground where

open import lambdas.language
open import lambdas.properties

open import Data.Empty using (⊥)
open import Data.String using (_≟_)
open import Data.Product using (∃-syntax; _×_; _,_)

open import Relation.Nullary using (yes; no; ¬_; contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
```

## `sub-pres`

If all we require is that `V` is of type `A` in `Γ` rather than the empty context, the
proof fails in the last lambda case.

```agda
sub-pres′ : ∀ {Γ b y A B V}
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
sub-pres′ {Γ} {`λ x ⦂ B ⇒ b} {y} {A} {B ⇒ C} {V} (⊢lam {x = x} ⊢b) ⊢V with x ≟ y
... | yes refl = ⊢lam (weaken drop ⊢b)
... | no  x≢y  = let weak = weaken (swap x≢y) ⊢b in
    -- We need to prove that Γ , x ⦂ B ⊢ V ⦂ A
    -- BUT!  If V has free "x"s, it might not be true, we only know that Γ ⊢ V ⦂ A
    ⊢lam (sub-pres′ {V = V} weak {!   !})
```

## Counterexample

And here's an explicit counter example showing why we could never fill that hole above.

The argument we're substituting in has a free "x" which will be captured.

```agda
my-Γ = ∅ , "x" ⦂ Nat
func = `λ "y" ⦂ (Nat ⇒ Nat) ⇒ `λ "x" ⦂ Bool ⇒ ` "y"
arg = `λ "z" ⦂ Nat ⇒ `suc ` "x"
result = `λ "x" ⦂ Bool ⇒ (`λ "z" ⦂ Nat ⇒ `suc ` "x")

-- The argument is a value, so we're allowed to substitute
arg-val : Value arg
arg-val = V-lam LV

-- The function is well typed
⊢func : my-Γ ⊢ func ⦂ (Nat ⇒ Nat) ⇒ Bool ⇒ (Nat ⇒ Nat)
⊢func = ⊢lam (⊢lam (⊢var (there (λ()) here)))

-- The argument is well typed
⊢arg : my-Γ ⊢ arg ⦂ Nat ⇒ Nat
⊢arg = ⊢lam (⊢suc (⊢var (there (λ()) here)))

-- So the application is well typed
⊢application : my-Γ ⊢ func · arg ⦂ Bool ⇒ (Nat ⇒ Nat)
⊢application = ⊢app ⊢func ⊢arg

-- The application steps to the (bad) result
app-step : func · arg —→ result
app-step = subst arg-val

-- And this (bad) result is not well typed
app-step-diff-type : ¬ my-Γ ⊢ result ⦂ Bool ⇒ (Nat ⇒ Nat)
app-step-diff-type (⊢lam (⊢lam (⊢suc (⊢var (there _ (there x≢x _)))))) =
    x≢x refl

-- So, in summary, preservation does not hold in all contexts (for our type system).
¬preserve : ¬ ∀ {Γ t t′ T}
    → Γ ⊢ t ⦂ T
    → t —→ t′
    → Γ ⊢ t′ ⦂ T
¬preserve hyp = app-step-diff-type (hyp ⊢application app-step)
```
