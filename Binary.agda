module Binary where
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; T; not)

-- representation
data Digit : Set where
    one : Digit
    two : Digit

Bin : Set 
Bin = List Digit

_+carry_ : Digit -> Digit -> Bool × Digit 
one +carry one = false , two
one +carry two = true , one
two +carry one = true , one
two +carry two = true , two

_+ᵇ_ : Bin -> Bin -> Bin
[] +ᵇ b = b
(x ∷ a) +ᵇ [] = (x ∷ a)
(dig ∷ a) +ᵇ (dig2 ∷ b) = {!   !}

0ᵇ : Bin
0ᵇ = []

⟦_⟧ : Bin -> ℕ 
⟦ [] ⟧ = zero
⟦ one ∷ bin ⟧ = {!   !}
⟦ two ∷ bin ⟧ = {!   !}


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-identityʳ; *-distribʳ-+; +-assoc; +-comm)
0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = {!   !}

_+ᴴ_ : ∀ x y → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
a +ᴴ b = {!   !}