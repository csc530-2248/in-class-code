module lambdas.language where

open import Data.String using (String; _≟_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl)

Id = String

infixr 7 _⇒_
data Type : Set where
    Bool : Type
    Nat  : Type
    _⇒_  : Type → Type → Type

infix  5 `λ_⦂_⇒_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
data Term : Set where
    `true   : Term
    `false  : Term
    `if     : Term → Term → Term → Term
    `zero   : Term
    `suc_   : Term → Term
    `zero?  : Term → Term
    `_      : Id → Term
    `λ_⦂_⇒_ : Id → Type → Term → Term
    _·_     : Term → Term → Term

data BoolValue : Term → Set where
    BV-true  : BoolValue `true
    BV-false : BoolValue `false

data NatValue : Term → Set where
    NV-zero : NatValue `zero
    NV-suc  : ∀ {n : Term}
        → NatValue n
        → NatValue (`suc n)

data LamValue : Term → Set where
    LV : ∀ {x : Id} {A : Type} {body : Term}
        → LamValue (`λ x ⦂ A ⇒ body)

data Value : Term → Set where
    V-bool : ∀ {t : Term} → BoolValue t → Value t
    V-nat  : ∀ {t : Term} → NatValue t → Value t
    V-lam  : ∀ {t : Term} → LamValue t → Value t

infix 5 _[_:=_]
_[_:=_] : Term → Id → Term → Term
`true          [ y := V ] = `true
`false         [ y := V ] = `false
`zero          [ y := V ] = `zero
(`if c th el)  [ y := V ] =
    `if (c [ y := V ]) (th [ y := V ]) (el [ y := V ])
(`suc n)       [ y := V ] = `suc (n [ y := V ])
(`zero? n)     [ y := V ] = `zero? (n [ y := V ])
(func · arg)   [ y := V ] = (func [ y := V ]) · (arg [ y := V ])
(` x)          [ y := V ] with x ≟ y
... | yes _ = V
... | no  _ = ` x
(`λ x ⦂ A ⇒ b) [ y := V ] with x ≟ y
... | yes _ = `λ x ⦂ A ⇒ b
... | no  _ = `λ x ⦂ A ⇒ (b [ y := V ])

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
    reduce-func : {func func′ arg : Term}
        → func —→ func′
        → func · arg —→ func′ · arg
    reduce-arg : {func arg arg′ : Term}
        → Value func
        → arg —→ arg′
        → func · arg —→ func · arg′
    -- β-reduction
    subst : {x : Id} {A : Type} {body arg : Term}
        → Value arg
        → (`λ x ⦂ A ⇒ body) · arg —→ body [ x := arg ]

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

infixl 6 _,_⦂_
data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context

infix 4 _⦂_∈_
data _⦂_∈_ : Id → Type → Context → Set where
    here  : ∀ {Γ x A} → x ⦂ A ∈ Γ , x ⦂ A
    there : ∀ {Γ x y A B}
        → x ≢ y
        → x ⦂ A ∈ Γ
        → x ⦂ A ∈ Γ , y ⦂ B

infix  4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
    ⊢true  : ∀ {Γ} → Γ ⊢ `true ⦂ Bool
    ⊢false : ∀ {Γ} → Γ ⊢ `false ⦂ Bool
    ⊢if    : ∀ {Γ} {c th el : Term} {T : Type}
        → Γ ⊢ c ⦂ Bool
        → Γ ⊢ th ⦂ T
        → Γ ⊢ el ⦂ T
        → Γ ⊢ `if c th el ⦂ T
    ⊢zero  : ∀ {Γ} → Γ ⊢ `zero ⦂ Nat
    ⊢suc   : ∀ {Γ} {n : Term}
        → Γ ⊢ n ⦂ Nat
        → Γ ⊢ `suc n ⦂ Nat
    ⊢zero? : ∀ {Γ} {n : Term}
        → Γ ⊢ n ⦂ Nat
        → Γ ⊢ `zero? n ⦂ Bool
    ⊢var   : ∀ {Γ x A}
        → x ⦂ A ∈ Γ
        → Γ ⊢ ` x ⦂ A
    ⊢lam   : ∀ {Γ x b A B}
        → Γ , x ⦂ A ⊢ b ⦂ B
        → Γ ⊢ (`λ x ⦂ A ⇒ b) ⦂ A ⇒ B
    ⊢app   : ∀ {Γ f a A B}
        → Γ ⊢ f ⦂ A ⇒ B
        → Γ ⊢ a ⦂ A
        → Γ ⊢ f · a ⦂ B
