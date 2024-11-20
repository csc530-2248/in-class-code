module nat-bool.examples where
open import nat-bool.language
open import nat-bool.properties
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

three : Term
three = `suc `suc `suc `zero

five : Term
five = `suc `suc three

program1 : Term
program1 = `if `true three five

program2 : Term
program2 = `if (`zero? three) three five

program3 : Term
program3 = `suc `true

three-is-value : Value three
three-is-value = V-nat (NV-suc (NV-suc (NV-suc NV-zero)))

p2-step : program2 —→ `if `false three five
p2-step = reduce-if (zero?-suc (NV-suc (NV-suc NV-zero)))

zero-normal : Normal `zero
zero-normal ()

suc-true-normal : Normal (`suc `true)
suc-true-normal (reduce-suc ())

suc-true-not-val : ¬ Value (`suc `true)
suc-true-not-val (V-nat (NV-suc ()))

suc-true-stuck : Stuck (`suc `true)
suc-true-stuck = suc-true-normal , suc-true-not-val

_ : `if `true three five —→* three
_ = begin `if `true three five —→⟨ if-true ⟩ three ∎

_ : `if (`zero? three) three five —→* five
_ = begin
        `if (`zero? three) three five
    —→⟨ reduce-if (zero?-suc (NV-suc (NV-suc NV-zero))) ⟩
        `if `false three five
    —→⟨ if-false ⟩
        five
    ∎

⊢three : ⊢ three ⦂ Nat
⊢three = ⊢suc (⊢suc (⊢suc ⊢zero))

⊢five : ⊢ five ⦂ Nat
⊢five = ⊢suc (⊢suc ⊢three)

⊢prog1 : ⊢ (`if `true three five) ⦂ Nat
⊢prog1 = ⊢if ⊢true ⊢three ⊢five

¬⊢prog3 : ∀ {T : Type} → ¬ ⊢ `suc `true ⦂ T
¬⊢prog3 (⊢suc ())
