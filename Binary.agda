module Binary where
open import Data.Nat using (ℕ; _*_; suc; zero; _+_)
open import Data.Fin as Fin hiding (_+_)
open import Data.List.Base as List
-- representation

Digit : ℕ -> Set
Digit = Fin

BaseNum : ℕ -> Set 
BaseNum n = List (Digit n)


Bin : Set
Bin = BaseNum 2

Carry : Set 
Carry = Fin 2

open import Data.Product using (_,_; _×_)
open import Data.Nat.Properties 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)

open import Relation.Nullary using (Dec; yes; no)


cycAdd : ∀ {n : ℕ} -> ℕ -> Fin n -> Fin n 
cycAdd {n} m i with (m + toℕ i) Data.Nat.<? n
... | yes x = fromℕ< x 
... | no ¬x = {!   !}

addDigits : ∀ {n : ℕ} -> Carry -> Digit n -> Digit n -> Carry × Digit n 
addDigits {n} c d₁ d₂ = {!   !} 
-- with c +′ d₁ +′ d₂ 
-- ... | a = {!   !}
    
addBaseNum : ∀ {n : ℕ} -> Carry -> BaseNum n -> BaseNum n -> BaseNum n 
addBaseNum c [] y = y
addBaseNum c (x ∷ xs) [] = (x ∷ xs)
addBaseNum c (x ∷ xs) (y ∷ ys) with addDigits c x y 
... | carry , dig = dig ∷ (addBaseNum carry xs ys)

infixl 6 _+ᵇ_
_+ᵇ_ : Bin -> Bin -> Bin
_+ᵇ_  = addBaseNum zero

0ᵇ : Bin
0ᵇ = []

⟦_⟧ᵈ : ∀ {n : ℕ} -> Digit n -> ℕ 
⟦ zero ⟧ᵈ = zero
⟦ suc n ⟧ᵈ = suc ⟦ n ⟧ᵈ

⟦_⟧ : Bin -> ℕ 
⟦ [] ⟧ = 0
⟦ x ∷ xs ⟧ = ⟦ x ⟧ᵈ + ⟦ xs ⟧ * 2




0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = refl

_+ᴴ_ : ∀ (x y : Bin) → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
x +ᴴ y = {!   !}