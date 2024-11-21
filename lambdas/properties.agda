module lambdas.properties where
open import lambdas.language

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (_≟_)

open import Relation.Nullary using (¬_; contradiction; yes; no)

Normal : Term → Set
Normal t = ∀ {t′ : Term} → ¬ (t —→ t′)

Stuck : Term → Set
Stuck t = Normal t × ¬ Value t

values-are-normal : ∀ {t : Term} → Value t → Normal t
values-are-normal (V-bool BV-true)  ()
values-are-normal (V-bool BV-false) ()
values-are-normal (V-nat NV-zero)   ()
values-are-normal (V-nat (NV-suc n-nv)) (reduce-suc n-step) =
    values-are-normal (V-nat n-nv) n-step
values-are-normal (V-lam LV)        ()

bool-vals : ∀ {Γ} {t : Term} → Value t → Γ ⊢ t ⦂ Bool → BoolValue t
bool-vals (V-bool BV-true)   t-bool = BV-true
bool-vals (V-bool BV-false)  t-bool = BV-false
bool-vals (V-nat NV-zero)    ()
bool-vals (V-nat (NV-suc x)) ()
bool-vals (V-lam LV)         ()

nat-vals : ∀ {Γ} {t : Term} → Value t → Γ ⊢ t ⦂ Nat → NatValue t
nat-vals (V-bool BV-true)      ()
nat-vals (V-bool BV-false)     ()
nat-vals (V-nat NV-zero)       _ = NV-zero
nat-vals (V-nat (NV-suc n-nv)) _ = NV-suc n-nv
nat-vals (V-lam LV)            ()

lam-vals : ∀ {Γ t A B} → Value t → Γ ⊢ t ⦂ A ⇒ B → LamValue t
lam-vals (V-bool BV-true)   ()
lam-vals (V-bool BV-false)  ()
lam-vals (V-nat NV-zero)    ()
lam-vals (V-nat (NV-suc _)) ()
lam-vals (V-lam LV)         t-func = LV

data Progress (t : Term) : Set where
    step : ∀ {t′ : Term} → t —→ t′ → Progress t
    done : Value t → Progress t

progress : ∀ {t : Term} {T : Type}
    → ∅ ⊢ t ⦂ T → Progress t
progress ⊢true  = done (V-bool BV-true)
progress ⊢false = done (V-bool BV-false)
progress ⊢zero  = done (V-nat NV-zero)
progress (⊢if ⊢c ⊢th ⊢el) with progress ⊢c
... | step c-step = step (reduce-if c-step)
... | done c-val with bool-vals c-val ⊢c
...   | BV-true  = step if-true
...   | BV-false = step if-false
progress (⊢suc ⊢n) with progress ⊢n
... | step n-step = step (reduce-suc n-step)
... | done n-val  = done (V-nat (NV-suc (nat-vals n-val ⊢n)))
progress (⊢zero? ⊢n) with progress ⊢n
... | step n-step = step (reduce-zero? n-step)
... | done n-val with nat-vals n-val ⊢n
...   | NV-zero      = step zero?-zero
...   | NV-suc pn-nv = step (zero?-suc pn-nv)
progress (⊢var ())
progress (⊢lam _) = done (V-lam LV)
progress (⊢app ⊢f ⊢a) with progress ⊢f
... | step f-step = step (reduce-func f-step)
... | done f-val
    with lam-vals f-val ⊢f
            | progress ⊢a
...    | LV | step a-step = step (reduce-arg (V-lam LV) a-step)
...    | LV | done a-val  = step (subst a-val)

sub-pres : ∀ {Γ y b A B V}
    → Γ , y ⦂ A ⊢ b ⦂ B
    → ∅ ⊢ V ⦂ A
    → Γ ⊢ b [ y := V ] ⦂ B
sub-pres ⊢true            _  = ⊢true
sub-pres ⊢false           _  = ⊢false
sub-pres ⊢zero            _  = ⊢zero
sub-pres (⊢suc   ⊢n)      ⊢V = ⊢suc (sub-pres ⊢n ⊢V)
sub-pres (⊢zero? ⊢n)      ⊢V = ⊢zero? (sub-pres ⊢n ⊢V)
sub-pres (⊢if ⊢c ⊢th ⊢el) ⊢V =
    ⊢if (sub-pres ⊢c ⊢V) (sub-pres ⊢th ⊢V) (sub-pres ⊢el ⊢V)
sub-pres (⊢app ⊢f ⊢a)     ⊢V =
    ⊢app (sub-pres ⊢f ⊢V) (sub-pres ⊢a ⊢V)
-- TODO: finish this lemma
sub-pres (⊢var x∈Γ)       ⊢V = {!   !}
sub-pres (⊢lam ⊢b)        ⊢V = {!   !}

preserve : ∀ {t t′ : Term} {T : Type}
    → ∅ ⊢ t ⦂ T → t —→ t′
    → ∅ ⊢ t′ ⦂ T
preserve (⊢if ⊢c ⊢th ⊢el)    if-true                   = ⊢th
preserve (⊢if ⊢c ⊢th ⊢el)    if-false                  = ⊢el
preserve (⊢if ⊢c ⊢th ⊢el)    (reduce-if c-step)        =
    ⊢if (preserve ⊢c c-step) ⊢th ⊢el
preserve (⊢suc   ⊢n)         (reduce-suc n-step)       = ⊢suc (preserve ⊢n n-step)
preserve (⊢zero? ⊢n)         zero?-zero                = ⊢true
preserve (⊢zero? ⊢n)         (zero?-suc n-nv)          = ⊢false
preserve (⊢zero? ⊢n)         (reduce-zero? n-step)     = ⊢zero? (preserve ⊢n n-step)
preserve (⊢app ⊢f ⊢a)        (reduce-func f-step)      = ⊢app (preserve ⊢f f-step) ⊢a
preserve (⊢app ⊢f ⊢a)        (reduce-arg f-val a-step) =
    ⊢app ⊢f (preserve ⊢a a-step)
preserve (⊢app (⊢lam ⊢b) ⊢a) (subst a-val) = sub-pres ⊢b ⊢a

unstuck : ∀ {t : Term} {T : Type} → ∅ ⊢ t ⦂ T → ¬ (Stuck t)
unstuck ⊢t (t-normal , t-not-val) with progress ⊢t
... | step t-step = contradiction t-step t-normal
... | done t-val  = contradiction t-val t-not-val

preserves : ∀ {t t₂ : Term} {T : Type}
    → ∅ ⊢ t ⦂ T
    → t —→* t₂
    → ∅ ⊢ t₂ ⦂ T
preserves ⊢t (t ∎) = ⊢t
preserves ⊢t (t —→⟨ t-fst-step ⟩ t-rst-steps) =
    preserves (preserve ⊢t t-fst-step) t-rst-steps

wttdgs : ∀ {t t′ : Term} {T : Type}
    → ∅ ⊢ t ⦂ T → t —→* t′
    → ¬ Stuck t′
wttdgs ⊢t t-steps = unstuck (preserves ⊢t t-steps)

data Finished (t : Term) : Set where
    done : Value t → Finished t
    timed-out : Finished t

data Steps (t : Term) : Set where
    steps : ∀ {t₂ : Term}
        → t —→* t₂
        → Finished t₂
        → Steps t

eval : ∀ {t : Term} {T : Type}
    → ℕ → ∅ ⊢ t ⦂ T → Steps t
eval {t} zero ⊢t = steps (t ∎) timed-out
eval {t} (suc time) ⊢t with progress ⊢t
... | done t-val = steps (t ∎) (done t-val)
... | step fst-step with eval time (preserve ⊢t fst-step)
...   | steps rst-steps fin = steps (t —→⟨ fst-step ⟩ rst-steps) fin
