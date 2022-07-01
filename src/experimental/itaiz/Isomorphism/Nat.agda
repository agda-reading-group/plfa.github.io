module experimental.itaiz.Isomorphism.Nat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≡ x
    
open _≲_

≲-refl : {A : Set} → A ≲ A
≲-refl = record { to = id; from = id; from∘to = λ x → refl}

≲-trans : {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans {A} {B} {C} A≲B B≲C = record { to = to'; from = from'; from∘to = from∘to'}
  where
    to' : A → C
    to' = to B≲C ∘ to A≲B
    from' : C → A
    from' = from A≲B ∘ from B≲C
    from∘to' : (x : A) → from' (to' x) ≡ x
    from∘to' x rewrite from∘to B≲C (to A≲B x) | from∘to A≲B x = refl


record _≅_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≡ x
    to∘from : (y : B) → to (from y) ≡ y
    
open _≅_

≅-refl : {A : Set} → A ≅ A
≅-refl = record { to = id; from = id; from∘to = λ x → refl; to∘from = λ y → refl }

≅-trans : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
≅-trans {A} {B} {C} A≅B B≅C = record { to = to'; from = from'; from∘to = from∘to'; to∘from = to∘from' }
  where
    to' : A → C
    to' = to B≅C ∘ to A≅B
    from' : C → A
    from' = from A≅B ∘ from B≅C
    from∘to' : (x : A) → from' (to' x) ≡ x
    from∘to' x rewrite from∘to B≅C (to A≅B x) | from∘to A≅B x = refl
    to∘from' : (y : C) → to' (from' y) ≡ y
    to∘from' y rewrite to∘from A≅B (from B≅C y) | to∘from B≅C y = refl

module ℕ≅ℕ⊎ℕ where

  -- Slightly complicated due to termination.

  to'-with : ℕ ⊎ ℕ → ℕ ⊎ ℕ
  to'-with (inj₁ x) = inj₁ (suc x)
  to'-with (inj₂ y) = inj₂ (suc y)

  to' : ℕ → ℕ ⊎ ℕ
  to' zero = inj₁ zero
  to' (suc zero) = inj₂ zero
  to' (suc (suc n)) = to'-with (to' n)

  from' : ℕ ⊎ ℕ → ℕ
  from' (inj₁ zero) = zero
  from' (inj₁ (suc i)) = suc (suc (from' (inj₁ i)))
  from' (inj₂ zero) = suc zero
  from' (inj₂ (suc j)) = suc (suc (from' (inj₂ j)))

  from∘to'-with : (n : ℕ) (to'-n : ℕ ⊎ ℕ) → from' to'-n ≡ n → from' (to'-with to'-n) ≡ suc (suc n)
  from∘to'-with n (inj₁ i) q = cong (suc ∘ suc) q
  from∘to'-with n (inj₂ j) q = cong (suc ∘ suc) q

  from∘to' : (n : ℕ) → from' (to' n) ≡ n
  from∘to' zero = refl
  from∘to' (suc zero) = refl
  from∘to' (suc (suc n)) = from∘to'-with n (to' n) (from∘to' n)

  to∘from'-with₁ : (i n : ℕ) → (to'-[suc-n] : ℕ ⊎ ℕ) → to'-[suc-n] ≡ inj₁ i → to'-with to'-[suc-n] ≡ inj₁ (suc i)
  to∘from'-with₁ i n (inj₁ i') q = cong (inj₁ ∘ suc) (inj₁-injective q)

  to∘from'-with₂ : (i : ℕ) (from'-[inj₁-i] : ℕ) → to' from'-[inj₁-i] ≡ inj₁ i → to'-with (to' from'-[inj₁-i]) ≡ inj₁ (suc i)
  to∘from'-with₂ i zero q = cong (inj₁ ∘ suc) (inj₁-injective q)
  to∘from'-with₂ i (suc n) q = to∘from'-with₁ i n (to' (suc n)) q

  to∘from'-with₃ : (j n : ℕ) (to'-[suc-n] : ℕ ⊎ ℕ) → to'-[suc-n] ≡ inj₂ j → to'-with to'-[suc-n] ≡ inj₂ (suc j)
  to∘from'-with₃ j n (inj₂ j') q = cong (inj₂ ∘ suc) (inj₂-injective q)

  to∘from'-with₄ : (j from'-[inj₂-j] : ℕ) → to' from'-[inj₂-j] ≡ inj₂ j → to'-with (to' from'-[inj₂-j]) ≡ inj₂ (suc j)
  to∘from'-with₄ j (suc n) q = to∘from'-with₃ j n (to' (suc n)) q

  to∘from' : (ii : ℕ ⊎ ℕ) → to' (from' ii) ≡ ii
  to∘from' (inj₁ zero) = refl
  to∘from' (inj₁ (suc i)) = to∘from'-with₂ i (from' (inj₁ i)) (to∘from' (inj₁ i))
  to∘from' (inj₂ zero) = refl
  to∘from' (inj₂ (suc j)) = to∘from'-with₄ j (from' (inj₂ j)) (to∘from' (inj₂ j))

  ℕ≅ℕ⊎ℕ : ℕ ≅ (ℕ ⊎ ℕ)
  ℕ≅ℕ⊎ℕ = record { to = to' ; from = from' ; from∘to = from∘to' ; to∘from = to∘from' }
