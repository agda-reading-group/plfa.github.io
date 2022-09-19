module experimental.itaiz.Data.List where

open import Data.List using (List; _∷_; []; [_]; _++_) public
open import Data.Nat using (ℕ; zero; suc)

length : {A : Set} → List A → ℕ
length [] = zero
length (x ∷ xs) = suc (length xs)

data _∈_ {A : Set} : A → List A → Set where
  zero : {x : A} {xs : List A} → x ∈ (x ∷ xs)
  suc : {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)
