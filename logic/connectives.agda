module logic.connectives where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)

infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
    constructor _,_
    field
        proj₁ : A
        proj₂ : B
open _×_

my-nat-pair : ℕ × ℕ
my-nat-pair = 5 , 7

first-nat : ℕ
first-nat = proj₁ my-nat-pair

-- _⇔_ : ∀ (A B : Set) → Set
-- A ⇔ B ＝ (A → B) × (B → A)

module ×-examples where
    prop1 : ∀ {A B C : Set} → ((A × B) → C) → (A → (B → C))
    prop1 hyp a b = hyp (a , b)

    prop2 : ∀ {A B C : Set} → (A → (B → C)) → ((A × B) → C)
    prop2 hyp a-and-b = hyp (proj₁ a-and-b) (proj₂ a-and-b)

    prop2′ : ∀ {A B C : Set} → (A → (B → C)) → ((A × B) → C)
    prop2′ hyp (a , b) = hyp a b

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
    inj₁ : A → A ⊎ B
    inj₂ : B → A ⊎ B

module ⊎-examples where
    prop1 : ∀ {A B C : Set} → (A × (B ⊎ C)) → ((A × B) ⊎ (A × C))
    prop1 (a , inj₁ b) = inj₁ (a , b)
    prop1 (a , inj₂ c) = inj₂ (a , c)

data ⊥ : Set where
-- intentionally blank

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

module ¬-examples where
    prop1 : ∀ {A B : Set} → (A → B) → (¬ B → ¬ A)
    prop1 a→b ¬b a = ¬b (a→b a)

    prop2 : ∀ {A B : Set} → ¬ (A ⊎ B) → (A → B)
    prop2 hyp a = ⊥-elim (hyp (inj₁ a))

    prop3 : ∀ {A B C : Set} → (A → (B ⊎ C)) → ¬ B → ¬ C → ¬ A
    prop3 hyp ¬b ¬c a with hyp a
    prop3 hyp ¬b ¬c a | inj₁ b = ¬b b
    prop3 hyp ¬b ¬c a | inj₂ c = ¬c c

    prop3′ : ∀ {A B C : Set} → (A → (B ⊎ C)) → ¬ B → ¬ C → ¬ A
    prop3′ hyp ¬b ¬c a with hyp a
    ... | inj₁ b = ¬b b
    ... | inj₂ c = ¬c c

    prop4 : ∀ {A B : Set} → ¬ (A ⊎ B) → ¬ A × ¬ B
    prop4 hyp = (λ a → hyp (inj₁ a)) , (λ b → hyp (inj₂ b))
    -- proj₁ (prop4 hyp) a = hyp (inj₁ a)
    -- proj₂ (prop4 hyp) b = hyp (inj₂ b)

record Σ (A : Set) (P : A → Set) : Set where
    constructor _,_
    field
        proj₁ : A
        proj₂ : P proj₁
open Σ

module Σ-example where
    prop1 : Σ ℕ (λ x → x ≡ 4)
    prop1 = 4 , refl

infix 2 Σ
syntax Σ A (λ x → P) = Σ[ x ∈ A ] P

module Σ-syntax-examples where
    prop1 : Σ[ x ∈ ℕ ] (x ≡ 4)
    prop1 = 4 , refl

    prop2 : ∀ {A B : Set} {P : A → Set}
        → (∀ (x : A) → (P x → B))
        → Σ[ x ∈ A ] (P x)
        → B
    prop2 hyp (a , pa) = hyp a pa

-- Σ-syntax is needed for the alternate version of the Σ seen above
import Data.Product using (_×_; _,_; proj₁; proj₂;
                           Σ; Σ-syntax)
import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Empty using (⊥; ⊥-elim)
import Relation.Nullary using (¬_; contradiction)
