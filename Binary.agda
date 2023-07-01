module Binary where
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)

-- representation
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin -> Bin
    _I : Bin -> Bin

inc : Bin -> Bin
inc ⟨⟩ = ⟨⟩ I
inc (bin O) = bin I
inc (bin I) = (inc bin) O


_+ᵇ_ : Bin -> Bin -> Bin
⟨⟩ +ᵇ b = b
(a O) +ᵇ ⟨⟩ = (a O)
(a I) +ᵇ ⟨⟩ = (a I)
(a O) +ᵇ (b O) = (a +ᵇ b) O
(a O) +ᵇ (b I) = (a +ᵇ b) I
(a I) +ᵇ (b O) = (a +ᵇ b) I
(a I) +ᵇ (b I) = (inc (a +ᵇ b)) O
-- ⟨⟩ +ᵇ b = b
-- a +ᵇ ⟨⟩ = a 
-- (a O) +ᵇ (b O) = (a +ᵇ b) O
-- (a O) +ᵇ (b I) = (a +ᵇ b) I
-- (a I) +ᵇ (b O) = (a +ᵇ b) I
-- (a I) +ᵇ (b I) = (inc (a +ᵇ b)) O

0ᵇ : Bin
0ᵇ = ⟨⟩

⟦_⟧ : Bin -> ℕ 
⟦ ⟨⟩ ⟧ = zero
⟦ x O ⟧ = ⟦ x ⟧ * 2
⟦ x I ⟧ = ⟦ x ⟧ * 2 + 1


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-identityʳ; *-distribʳ-+; +-assoc; +-comm)
0ᴴ : ⟦ 0ᵇ ⟧ ≡ 0
0ᴴ = refl

inc-≡ : ∀ (bin : Bin) -> ⟦ inc bin ⟧ ≡ ⟦ bin ⟧ + 1
inc-≡ ⟨⟩ = refl
inc-≡ (bin O) = refl
inc-≡ (bin I) 
    rewrite inc-≡ bin 
    | *-distribʳ-+ 2 (⟦ bin ⟧) 1
    | +-assoc (⟦ bin ⟧ * 2) 1 1 = refl


_+ᴴ_ : ∀ x y → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
⟨⟩ +ᴴ b = refl
(a O) +ᴴ ⟨⟩ rewrite +-identityʳ (⟦ a ⟧ * 2) = refl
(a I) +ᴴ ⟨⟩ rewrite +-identityʳ (⟦ a ⟧ * 2 + 1) = refl
(a O) +ᴴ (b O) rewrite a +ᴴ b | *-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)  = refl
(a O) +ᴴ (b I) rewrite a +ᴴ b 
    | *-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)
    | +-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 1  = refl
(a I) +ᴴ (b O) 
    rewrite a +ᴴ b 
    | *-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)  -- ⟦ a ⟧ * 2 + ⟦ b ⟧ * 2 + 1 ≡ ⟦ a ⟧ * 2 + 1 + ⟦ b ⟧ * 2
    | +-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 1 -- ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + 1) ≡ ⟦ a ⟧ * 2 + 1 + ⟦ b ⟧ * 2
    | +-comm (⟦ b ⟧ * 2 ) 1 -- ⟦ a ⟧ * 2 + suc (⟦ b ⟧ * 2) ≡ ⟦ a ⟧ * 2 + 1 + ⟦ b ⟧ * 2
    | +-assoc (⟦ a ⟧ * 2) 1 (⟦ b ⟧ * 2)
    = refl
(a I) +ᴴ (b I) 
    rewrite inc-≡ (a +ᵇ b) 
    | a +ᴴ b -- (⟦ a ⟧ + ⟦ b ⟧ + 1) * 2 ≡ ⟦ a ⟧ * 2 + 1 + (⟦ b ⟧ * 2 + 1)
    | +-assoc (⟦ a ⟧ * 2) 1 (⟦ b ⟧ * 2 + 1)
    | +-comm 1 (⟦ b ⟧ * 2 + 1)
    | +-assoc (⟦ b ⟧ * 2) 1 1
    | sym (+-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 2)
    | *-distribʳ-+ 2 (⟦ a ⟧ + ⟦ b ⟧) (1)
    | *-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)
    = refl

    -- begin 
    --     ⟦ a +ᵇ b ⟧
    -- ≡⟨ {!   !} ⟩ 
    --     ⟦ a ⟧ + ⟦ b ⟧
    -- ∎ 