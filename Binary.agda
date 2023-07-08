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
inc-≡ (bin I) =
    begin
        ⟦ inc (bin I) ⟧
    ≡⟨⟩
        ⟦ (inc bin) O ⟧
    ≡⟨⟩
        ⟦ inc bin ⟧ * 2
    ≡⟨ cong (λ x -> x * 2) (inc-≡ bin) ⟩
        (⟦ bin ⟧ + 1) * 2
    ≡⟨ *-distribʳ-+ 2 (⟦ bin ⟧) 1 ⟩
        ⟦ bin ⟧ * 2 + 1 * 2
    ≡⟨ sym (+-assoc (⟦ bin ⟧ * 2) 1 1) ⟩
        ⟦ bin ⟧ * 2 + 1 + 1
    ≡⟨⟩ 
        ⟦ bin I ⟧ + 1
    ∎

_+ᴴ_ : ∀ x y → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
⟨⟩ +ᴴ b = refl
(a O) +ᴴ ⟨⟩ =
    begin 
        ⟦ (a O) +ᵇ ⟨⟩ ⟧
    ≡⟨⟩ 
        ⟦ a ⟧ * 2
    ≡⟨ sym (+-identityʳ (⟦ a ⟧ * 2)) ⟩ 
        ⟦ a ⟧ * 2 + zero
    ≡⟨⟩ 
        ⟦ a O ⟧ + ⟦ ⟨⟩ ⟧
    ∎ 
(a I) +ᴴ ⟨⟩ = 
    begin 
        ⟦ (a I) +ᵇ ⟨⟩ ⟧
    ≡⟨⟩ 
        ⟦ a ⟧ * 2 + 1
    ≡⟨ sym (+-identityʳ (⟦ a ⟧ * 2 + 1)) ⟩ 
        ⟦ a ⟧ * 2 + 1 + zero
    ≡⟨⟩ 
        ⟦ a I ⟧ + ⟦ ⟨⟩ ⟧
    ∎ 
(a O) +ᴴ (b O) =
    begin
        ⟦ (a O) +ᵇ (b O) ⟧
    ≡⟨⟩
        ⟦ a +ᵇ b ⟧ * 2
    ≡⟨ cong (_* 2) (a +ᴴ b) ⟩ 
        (⟦ a ⟧ + ⟦ b ⟧) * 2
    ≡⟨ *-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧) ⟩ 
        ⟦ a ⟧ * 2 + ⟦ b ⟧ * 2
    ≡⟨⟩ 
        ⟦ a O ⟧ + ⟦ b O ⟧
    ∎  
(a O) +ᴴ (b I) = 
    begin
        ⟦ (a O) +ᵇ (b I) ⟧
    ≡⟨⟩
        ⟦ a +ᵇ b ⟧ * 2 + 1 
    ≡⟨ cong (λ x -> x * 2 + 1) (a +ᴴ b) ⟩ 
        (⟦ a ⟧ + ⟦ b ⟧) * 2 + 1
    ≡⟨ cong (λ x → x + 1) (*-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)) ⟩ 
        ⟦ a ⟧ * 2 + ⟦ b ⟧ * 2 + 1
    ≡⟨ +-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 1 ⟩ 
        ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + 1)
    ≡⟨⟩ 
        ⟦ a O ⟧ + ⟦ b I ⟧
    ∎  
(a I) +ᴴ (b O) =
    begin 
        ⟦ (a I) +ᵇ (b O) ⟧
    ≡⟨⟩ 
        ⟦ a +ᵇ b ⟧ * 2 + 1
    ≡⟨ cong (λ x -> x * 2 + 1) (a +ᴴ b) ⟩ 
        (⟦ a ⟧ + ⟦ b ⟧) * 2 + 1
    ≡⟨ cong (_+ 1) (*-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)) ⟩ 
        ⟦ a ⟧ * 2 + ⟦ b ⟧ * 2 + 1
    ≡⟨ +-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 1 ⟩ 
        ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + 1)
    ≡⟨ cong ((⟦ a ⟧ * 2)  +_) (+-comm (⟦ b ⟧ * 2 ) 1) ⟩ 
        ⟦ a ⟧ * 2 + suc (⟦ b ⟧ * 2)
    ≡⟨ sym (+-assoc (⟦ a ⟧ * 2) 1 (⟦ b ⟧ * 2)) ⟩
        ⟦ a ⟧ * 2 + 1 + ⟦ b ⟧ * 2
    ≡⟨⟩ 
        ⟦ a I ⟧ + ⟦ b O ⟧
    ∎ 
(a I) +ᴴ (b I) = 
    begin 
        ⟦ (a I) +ᵇ (b I) ⟧
    ≡⟨⟩ 
        ⟦ inc (a +ᵇ b) ⟧ * 2 
    ≡⟨ cong (_* 2) (inc-≡ (a +ᵇ b)) ⟩ 
        (⟦ (a +ᵇ b) ⟧ + 1) * 2
    ≡⟨ cong (λ x → (x + 1) * 2) (a +ᴴ b) ⟩ 
        (⟦ a ⟧ + ⟦ b ⟧ + 1) * 2
    ≡⟨ *-distribʳ-+ 2 (⟦ a ⟧ + ⟦ b ⟧) (1) ⟩ 
        (⟦ a ⟧ + ⟦ b ⟧) * 2 + 2
    ≡⟨ cong (_+ 2) (*-distribʳ-+ 2 (⟦ a ⟧) (⟦ b ⟧)) ⟩         
        ⟦ a ⟧ * 2 + ⟦ b ⟧ * 2 + 2
    ≡⟨  +-assoc (⟦ a ⟧ * 2) (⟦ b ⟧ * 2) 2 ⟩         
        ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + 2)
    ≡⟨⟩ 
        ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + (1 + 1)) 
    ≡⟨ cong (λ x → ⟦ a ⟧ * 2 + x) (sym (+-assoc (⟦ b ⟧ * 2) 1 1)) ⟩ 
        ⟦ a ⟧ * 2 + (⟦ b ⟧ * 2 + 1 + 1) 
    ≡⟨ cong ((⟦ a ⟧ * 2) +_) (+-comm (⟦ b ⟧ * 2 + 1) 1) ⟩ 
        ⟦ a ⟧ * 2 + (1 + ⟦ b ⟧ * 2 + 1)     
    ≡⟨ sym (+-assoc (⟦ a ⟧ * 2) 1 (⟦ b ⟧ * 2 + 1)) ⟩ 
       ⟦ a ⟧ * 2 + 1 + (⟦ b ⟧ * 2 + 1)
    ≡⟨⟩ 
        ⟦ a I ⟧ + ⟦ b I ⟧
    ∎ 