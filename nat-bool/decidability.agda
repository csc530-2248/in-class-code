module nat-bool.decidability where
open import nat-bool.language

open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)

BoolValue? : ∀ t → Dec (BoolValue t)
BoolValue? `true         = yes BV-true
BoolValue? `false        = yes BV-false
BoolValue? (`if c th el) = no (λ ())
BoolValue? `zero         = no (λ ())
BoolValue? (`suc n)      = no (λ ())
BoolValue? (`zero? n)    = no (λ ())

-- suc-not-nat : ∀ {n} → ¬ NatValue n → ¬ NatValue (`suc n)
-- suc-not-nat ¬n-nv (NV-suc n-nv) = ¬n-nv n-nv

NatValue? : ∀ t → Dec (NatValue t)
NatValue? `true         = no (λ ())
NatValue? `false        = no (λ ())
NatValue? (`if t th el) = no (λ ())
NatValue? `zero         = yes NV-zero
NatValue? (`suc n) with NatValue? n
... | yes n-nv = yes (NV-suc n-nv)
... | no ¬n-nv = no suc-not-nat -- λ{ (NV-suc n-nv) → ¬n-nv n-nv }
    where
    suc-not-nat : ¬ NatValue (`suc n)
    suc-not-nat (NV-suc n-nv) = ¬n-nv n-nv
NatValue? (`zero? n)    = no (λ ())

Value? : ∀ t → Dec (Value t)
Value? t with BoolValue? t | NatValue? t
... | yes t-bv | _        = yes (V-bool t-bv)
... | no _     | yes t-nv = yes (V-nat t-nv)
... | no ¬t-bv | no ¬t-nv = no not-value
    where
    not-value : ¬ Value t
    not-value (V-bool t-bv) = ¬t-bv t-bv
    not-value (V-nat t-nv) = ¬t-nv t-nv

type-check : ∀ t T → Dec (⊢ t ⦂ T)
type-check `true Bool = yes ⊢true
type-check `true Nat = no (λ ())
type-check `false Bool = yes ⊢false
type-check `false Nat = no (λ ())
type-check `zero Bool = no (λ ())
type-check `zero Nat = yes ⊢zero
type-check (`suc n) Bool = no (λ ())
type-check (`suc n) Nat with type-check n Nat
... | yes n-nat = yes (⊢suc n-nat)
... | no ¬n-nat = no suc-not-nat
    where
    suc-not-nat : ¬ ⊢ (`suc n) ⦂ Nat
    suc-not-nat (⊢suc n-nat) = ¬n-nat n-nat
type-check (`zero? n) Bool with type-check n Nat
... | yes n-nat = yes (⊢zero? n-nat)
... | no ¬n-nat = no zero?-not-nat
    where
    zero?-not-nat : ¬ (⊢ `zero? n ⦂ Bool)
    zero?-not-nat (⊢zero? n-nat) = ¬n-nat n-nat
type-check (`zero? n) Nat = no (λ ())
type-check (`if c th el) T
    with type-check c Bool | type-check th T | type-check el T
... | no ¬c-bool | _        | _        = no cond-not-bool
    where
    cond-not-bool : ¬ ⊢ (`if c th el) ⦂ T
    cond-not-bool (⊢if c-bool _ _) = ¬c-bool c-bool
... | yes _      | no ¬th-T | _        = no then-not-T
    where
    then-not-T : ¬ ⊢ (`if c th el) ⦂ T
    then-not-T (⊢if _ th-T _) = ¬th-T th-T
... | yes _      | yes _    | no ¬el-T = no else-not-T
    where
    else-not-T : ¬ ⊢ (`if c th el) ⦂ T
    else-not-T (⊢if _ _ el-T) = ¬el-T el-T
... | yes c-bool | yes th-T | yes el-T = yes (⊢if c-bool th-T el-T)
