module nat-bool.language where

infix  8 `suc_
data Term : Set where
    `true  : Term
    `false : Term
    `if    : Term → Term → Term → Term
    `zero  : Term
    `suc_  : Term → Term
    `zero? : Term → Term

data BoolValue : Term → Set where
    BV-true  : BoolValue `true
    BV-false : BoolValue `false

data NatValue : Term → Set where
    NV-zero : NatValue `zero
    NV-suc  : ∀ {n : Term}
        → NatValue n
        → NatValue (`suc n)

data Value : Term → Set where
    V-bool : ∀ {t : Term} → BoolValue t → Value t
    V-nat  : ∀ {t : Term} → NatValue t → Value t

infix  4 _—→_
data _—→_ : Term → Term → Set where
    if-true : ∀ {th el : Term}
        → `if `true th el —→ th
    if-false : ∀ {th el : Term}
        → `if `false th el —→ el
    reduce-if : ∀ {c c′ th el : Term}
        → c —→ c′
        → `if c th el —→ `if c′ th el
    reduce-suc : ∀ {n n′ : Term}
        → n —→ n′
        → `suc n —→ `suc n′
    zero?-zero : `zero? `zero —→ `true
    zero?-suc : ∀ {n : Term}
        → NatValue n
        → `zero? (`suc n) —→ `false
    reduce-zero? : {n n′ : Term}
        → n —→ n′
        → `zero? n —→ `zero? n′

infix  2 _—→*_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎
data _—→*_ : Term → Term → Set where
    _∎ : ∀ (t : Term) → t —→* t
    step—→ : ∀ (t : Term) {t₁ t₂ : Term}
        → t₁ —→* t₂
        → t  —→  t₁
        → t  —→* t₂

pattern _—→⟨_⟩_ t t—→t₁ t₁—→*t₂ = step—→ t t₁—→*t₂ t—→t₁

begin_ : ∀ {t t₁} → t —→* t₁ → t —→* t₁
begin s = s

data Type : Set where
    Bool : Type
    Nat  : Type

infix  4 ⊢_⦂_
data ⊢_⦂_ : Term → Type → Set where
    ⊢true  : ⊢ `true ⦂ Bool
    ⊢false : ⊢ `false ⦂ Bool
    ⊢if    : ∀ {c th el : Term} {T : Type}
        → ⊢ c ⦂ Bool
        → ⊢ th ⦂ T
        → ⊢ el ⦂ T
        → ⊢ `if c th el ⦂ T
    ⊢zero  : ⊢ `zero ⦂ Nat
    ⊢suc   : ∀ {n : Term}
        → ⊢ n ⦂ Nat
        → ⊢ `suc n ⦂ Nat
    ⊢zero? : ∀ {n : Term}
        → ⊢ n ⦂ Nat
        → ⊢ `zero? n ⦂ Bool
