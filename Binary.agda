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
a +ᵇ ⟨⟩ = a
a +ᵇ (b O) = (a +ᵇ b) +ᵇ b
a +ᵇ (b I) = inc ((a +ᵇ b) +ᵇ b)

0ᵇ : Bin
0ᵇ = ⟨⟩

⟦_⟧ : Bin -> ℕ 
⟦ ⟨⟩ ⟧ = zero
⟦ x O ⟧ = 2 * ⟦ x ⟧
⟦ x I ⟧ = 2 * ⟦ x ⟧ + 1


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat.Properties using (+-identityʳ; *-distribˡ-+; +-assoc; +-comm)
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
        2 * ⟦ inc bin ⟧ 
    ≡⟨ cong (2 *_) (inc-≡ bin) ⟩
        2 * (⟦ bin ⟧ + 1)
    ≡⟨ *-distribˡ-+ 2 ⟦ bin ⟧ 1 ⟩
        2 * ⟦ bin ⟧ + 2 * 1
    ≡⟨ sym (+-assoc (2 * ⟦ bin ⟧) 1 1) ⟩
        2 * ⟦ bin ⟧ + 1 + 1
    ≡⟨⟩ 
        ⟦ bin I ⟧ + 1 
    ∎

_+ᴴ_ : ∀ x y → ⟦ x +ᵇ y ⟧ ≡ ⟦ x ⟧ + ⟦ y ⟧
a +ᴴ ⟨⟩ = sym (+-identityʳ ⟦ a ⟧)
a +ᴴ (b O) = 
    begin 
        ⟦ (a +ᵇ b) +ᵇ b ⟧
    ≡⟨ (a +ᵇ b) +ᴴ b ⟩
        ⟦ a +ᵇ b ⟧  + ⟦ b ⟧
    ≡⟨ cong (_+ ⟦ b ⟧) (a +ᴴ b) ⟩
        ⟦ a ⟧ + ⟦ b ⟧ + ⟦ b ⟧
    ≡⟨ +-assoc ⟦ a ⟧ ⟦ b ⟧ ⟦ b ⟧ ⟩
        ⟦ a ⟧ + (⟦ b ⟧ + ⟦ b ⟧)
    ≡⟨ cong (λ x → ⟦ a ⟧ + (⟦ b ⟧ + x)) (sym (+-identityʳ ⟦ b ⟧)) ⟩
        ⟦ a ⟧ + (⟦ b ⟧ + (⟦ b ⟧ + zero))
    ≡⟨⟩ 
        ⟦ a ⟧ + ⟦ b O ⟧
    ∎

a +ᴴ (b I) =
    begin 
        ⟦ a +ᵇ (b I) ⟧ 
    ≡⟨⟩
        ⟦ inc ((a +ᵇ b) +ᵇ b) ⟧ 
    ≡⟨ inc-≡ ((a +ᵇ b) +ᵇ b) ⟩ 
        ⟦ (a +ᵇ b) +ᵇ b ⟧ + 1 
    ≡⟨ cong (_+ 1) ((a +ᵇ b) +ᴴ b) ⟩
        ⟦ a +ᵇ b ⟧  + ⟦ b ⟧ + 1
    ≡⟨ cong (_+ 1) (cong (_+ ⟦ b ⟧) (a +ᴴ b)) ⟩
        ⟦ a ⟧ + ⟦ b ⟧ + ⟦ b ⟧ + 1
    ≡⟨ cong (_+ 1) (+-assoc ⟦ a ⟧ ⟦ b ⟧ ⟦ b ⟧) ⟩
        ⟦ a ⟧ + (⟦ b ⟧ + ⟦ b ⟧) + 1
    ≡⟨ +-assoc ⟦ a ⟧ (⟦ b ⟧ + ⟦ b ⟧) 1 ⟩
        ⟦ a ⟧ + (⟦ b ⟧ + ⟦ b ⟧ + 1)
    ≡⟨ cong (λ x → ⟦ a ⟧ + (⟦ b ⟧ + x + 1)) (sym (+-identityʳ ⟦ b ⟧)) ⟩ 
        ⟦ a ⟧ + (⟦ b ⟧ + (⟦ b ⟧ + zero) + 1)
    ≡⟨⟩ 
        ⟦ a ⟧ + ⟦ b I ⟧
    ∎
 
