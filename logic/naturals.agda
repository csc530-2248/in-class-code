module logic.naturals where

prop1 : ∀ {A : Set} → A → A
prop1 a = a

prop2 : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
prop2 hyp1 hyp2 a = hyp2 (hyp1 a)

data ℕ : Set where
    zero : ℕ
    suc  : ℕ → ℕ

one = suc zero
two = suc one
three = suc two
seven = suc (suc (suc (suc three)))

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero  + n = n
(suc m) + n = suc (m + n)

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

infix 4 _≡_
data _≡_ {A : Set} : A → A → Set where
    refl : ∀ {x : A} → x ≡ x

easy-lemma : three ≡ three
easy-lemma = refl

lemma2 : one + two ≡ three
lemma2 = refl

sym : ∀ {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- trans (refl x) (refl .x) = refl x
trans refl y≡z = y≡z

cong : ∀ {A B : Set} {x y : A} (f : A → B)
    → x ≡ y → f x ≡ f y
cong f refl = refl

infix 1 begin_
begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin eq = eq

infixr 2 _≡⟨_⟩_
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A}
    → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

infix  3 _∎
_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

+-identityˡ : ∀ (n : ℕ) → zero + n ≡ n
+-identityˡ n = refl

+-identityʳ : ∀ (n : ℕ) → n + zero ≡ n
+-identityʳ zero    = refl
+-identityʳ (suc n) = cong suc (+-identityʳ n)

suc-+ : ∀ (m n : ℕ) → (suc m) + n ≡ suc (m + n)
suc-+ m n = refl

+-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- We need ≡ to be:
-- [✓] symmetric
-- [✓] transitive
-- [✓] preserve equality after function application.
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
-- base case:
-- [✓] zero + n ≡ n
-- [✓]          ≡ n + zero
+-comm zero    n = begin
    zero + n ≡⟨ +-identityˡ n ⟩
    n        ≡⟨ sym (+-identityʳ n) ⟩
    n + zero ∎
-- inductive step:
-- [✓] (suc k) + n ≡ suc (k + n)
-- [✓]             ≡ suc (n + k)
-- [✓]             ≡ n + suc k
+-comm (suc k) n = begin
    (suc k) + n ≡⟨ suc-+ k n ⟩
    suc (k + n) ≡⟨ cong suc (+-comm k n) ⟩
    suc (n + k) ≡⟨ sym (+-suc n k) ⟩
    n + suc k   ∎

-- FUTURE HOMEWORK!
-- +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
-- +-assoc m n p = {!   !}

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero    = refl
*-zeroʳ (suc n) = *-zeroʳ n

*-identityʳ : ∀ (n : ℕ) → n * one ≡ n
*-identityʳ zero = refl
*-identityʳ (suc n) = cong suc (*-identityʳ n)

-- *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
-- *-comm zero    n = {!   !}
-- *-comm (suc m) n = {!   !}

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc m n = {!   !}


*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m n = {!   !}

import Relation.Binary.PropositionalEquality
    using (_≡_; refl; cong; sym; trans)
import Data.Nat using (ℕ; zero; suc; _+_; _*_)
import Data.Nat.Properties
    using ( +-identityʳ; +-identityˡ; +-suc; +-assoc )
