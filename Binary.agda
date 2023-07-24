module Binary where
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)
open import Data.Nat.Binary as ℕᵇ using (ℕᵇ)
-- representation


Bin : Set 
Bin = ℕᵇ

_+ᵇ_ : Bin -> Bin -> Bin
_+ᵇ_  = ℕᵇ._+_

0ᵇ : Bin
0ᵇ = ℕᵇ.zero

⟦_⟧ : Bin -> ℕ 
⟦_⟧ = ℕᵇ.toℕ 



import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = refl

open import Data.Nat.Binary.Properties
_+ᴴ_ : ∀ (x y : Bin) → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
x +ᴴ y = toℕ-homo-+ x y

-- ℕᵇ.zero +ᴴ y = refl
-- ℕᵇ.2[1+ x ] +ᴴ ℕᵇ.zero = {! refl   !}
-- ℕᵇ.1+[2 x ] +ᴴ ℕᵇ.zero = {!   !}
-- ℕᵇ.2[1+ x ] +ᴴ ℕᵇ.2[1+ y ] = 
--     begin 
--         ⟦ ℕᵇ.2[1+ x ] +ᵇ ℕᵇ.2[1+ y ] ⟧ 
--     ≡⟨ {!   !} ⟩ 
--         ⟦ ℕᵇ.2[1+ x ] ⟧ + ⟦ ℕᵇ.2[1+ y ] ⟧
--     ∎
-- ℕᵇ.2[1+ x ] +ᴴ ℕᵇ.1+[2 y ] = {!   !}
-- ℕᵇ.1+[2 x ] +ᴴ ℕᵇ.2[1+ y ] = {!   !}
-- ℕᵇ.1+[2 x ] +ᴴ ℕᵇ.1+[2 y ] = {!   !}

-- import Data.Bin 
-- O  = zero
-- I = 1 + 2 * zero = 1+[2 O ] = I 
-- IO  = 2 * (1 + zero) = 2[1+ O ] = IO 
-- II = 1 + 2 * 1 = 1+[2 I ] = ... I I 
-- IOO = 2 * (1 + 1) = 2[1+ I ] = IOO
-- IOI = 1 + (2 * 2) = 1+[2 IO ] = IOI
-- IIO = 2 * (1 * 2) = 2[1+ IO ] = ...
