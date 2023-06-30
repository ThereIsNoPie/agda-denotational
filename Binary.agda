module Binary where
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)

-- representation
data Digit : Set where
    O : Digit
    I : Digit

data Bin : Set where
    zero : Bin
    append-to-I : Digit -> Bin 

_+ᵇ_ : Bin -> Bin -> Bin
zero +ᵇ b = b
append-to-I x +ᵇ zero = append-to-I x
append-to-I x +ᵇ append-to-I x₁ = {!   !}

0ᵇ : Bin
0ᵇ = zero

⟦_⟧ : Bin -> ℕ 
⟦ bin ⟧ = {!   !}


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-identityʳ; *-distribʳ-+; +-assoc; +-comm)
0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = {!   !}

_+ᴴ_ : ∀ x y → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
a +ᴴ b = {!   !}