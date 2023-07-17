module Binary where
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)
open import Data.Bool using (Bool; true; false; T; not)
open import Data.Fin.Base 

-- representation
Digit : ℕ -> Set
Digit = Fin

Bin : Set 
Bin = List (Digit 2)

_+carry_ : ∀ {n : ℕ} -> Digit n -> Digit n -> Digit n × Digit n 
x +carry y with x Data.Fin.Base.+ y 
... | a = {!   !}
-- zero +carry y = false , y
-- suc x +carry zero = false , (suc x)
-- suc x +carry suc y with x +carry y 
-- ... | false , snd = {!   !}
-- ... | true , snd = {!   !}

_+ᵇ_ : Bin -> Bin -> Bin
a +ᵇ b = {!   !}

0ᵇ : Bin
0ᵇ = []

⟦_⟧ : Bin -> ℕ 
⟦ [] ⟧ = 0
⟦ x ∷ x₁ ⟧ = {!   !}



import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-identityʳ; *-distribʳ-+; +-assoc; +-comm)
0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = {!   !}

-- _+ᴴ_ : ∀ (x y : Bin) → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
-- a +ᴴ b = {!   !}