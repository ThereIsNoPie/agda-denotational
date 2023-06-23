module Binary where

-- data Digit : Set where
--     one : Digit
--     zero : Digit

-- data Bin : Set where
--     base : Bin
--     suc : Digit -> Bin -> Bin

-- _+_ : Bin -> Bin -> Bin
-- base + b = b
-- suc x a + base = suc x a
-- suc one a + suc one b = suc one (suc zero (a + b))
-- suc one a + suc zero b = suc one (a + b)
-- suc zero a + suc one b = suc one (a + b)
-- suc zero a + suc zero b = a + b
-- -- hmmm

-- -- Denotation for binary arithmetic?
-- -- Bin -> Bin -> Bin

-- -- define a meaning function

-- open import Data.Nat using (ℕ)

-- Bin : Set
-- Bin = ℕ -> Digit 

-- _D+_ : Bin -> Bin -> Bin
-- (f D+ g) ℕ.zero = {! f ℕ.zero + g ℕ.zero   !}
-- (f D+ g) (ℕ.suc x) = {! f (ℕ.suc x) + g (ℕ.suc x) + (f D+ g) x  !}
--     where 
--     _dig+_ : Digit -> Digit -> 


open import Data.Nat using (ℕ; _≟_; suc; zero)
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; _xor_; not)
open import Data.List using (List; _∷_; [])
open import Data.List.Base using (any)
open import Relation.Nullary.Decidable using (⌊_⌋)


-- representation
Bin : Set
Bin = List ℕ 

-- meaning (how do we get here?)
⟦_⟧ : Bin -> (ℕ -> Bool)
(⟦ xs ⟧) n = any (λ x → ⌊ x ≟ n ⌋) xs

_+_ : (ℕ -> Bool) -> (ℕ -> Bool) -> (ℕ -> Bool)
(a + b) zero = (a zero) xor (b zero)
(a + b) (suc n) = (a (suc n)) xor (b (suc n)) xor (carry+ a b n)
    where 
    carry+ : (ℕ -> Bool) -> (ℕ -> Bool) -> (ℕ -> Bool)
    carry+ a b zero = (a zero) ∧ (b zero)
    carry+ a b (suc n) with (a (suc n)) | (b (suc n)) | (carry+ a b n) 
    ...| A | B | C = (A ∨ B) ∧ (B ∨ C) ∧ (A ∨ C)

const0Bin : ℕ -> Bool
const0Bin _ = false
