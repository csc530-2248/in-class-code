module logic.decidability where

open import Relation.Nullary using (¬_; contradiction)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; cong)

data Bool : Set where
    true : Bool
    false : Bool

_==_ : ℕ → ℕ → Bool
zero  == zero  = true
zero  == suc n = false
suc m == zero  = false
suc m == suc n = m == n

_ : (2 == 4) ≡ false
_ = refl

_ : (3 == 3) ≡ true
_ = refl

-- \top
record ⊤ : Set where
    constructor tt

-- in Data.Bool
T : Bool → Set
T true  = ⊤
T false = ⊥

==→≡ : ∀ (m n : ℕ) → T (m == n) → m ≡ n
==→≡ zero    zero    m==n = refl
==→≡ zero    (suc n) ()
==→≡ (suc m) zero    ()
==→≡ (suc m) (suc n) m==n = cong suc (==→≡ m n m==n)

≡→== : ∀ (m n : ℕ) → m ≡ n → T (m == n)
≡→== zero    zero    m≡n = tt
≡→== zero    (suc n) ()
≡→== (suc m) zero    ()
≡→== (suc m) (suc n) refl = ≡→== m m refl

-- in Relation.Nullary
data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

suc-injective : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n
suc-injective m≢n refl = contradiction refl m≢n

0≢1+n : ∀ {n : ℕ} → 0 ≢ suc n
0≢1+n ()

1+n≢0 : ∀ {n : ℕ} → suc n ≢ 0
1+n≢0 ()

-- in Data.Nat
-- \?=
_≟_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≟ zero  = yes refl
zero  ≟ suc n = no 0≢1+n
suc m ≟ zero  = no 1+n≢0
suc m ≟ suc n with m ≟ n
... | yes eq = yes (cong suc eq)
... | no neq = no (suc-injective neq)
