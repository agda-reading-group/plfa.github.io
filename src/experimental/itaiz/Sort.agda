module experimental.itaiz.Sort where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s; _≤?_; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; ≤-trans; ≤-pred)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

open import experimental.itaiz.Data.List

data Sorted : List ℕ → Set where
  [] : Sorted []
  _∷_ : (x : ℕ) → {xs : List ℕ} → ({w : ℕ} → w ∈ xs → x ≤ w) → Sorted (x ∷ xs)

merge : List ℕ → List ℕ → List ℕ
merge [] = id
merge (x ∷ xs) = go
  where
    go : List ℕ → List ℕ
    go [] = x ∷ xs
    go (y ∷ ys) with x ≤? y
    ... | yes _ = x ∷ merge xs (y ∷ ys)
    ... | no _ = y ∷ go ys

to : (w : ℕ) → (xs ys : List ℕ) → w ∈ merge xs ys → w ∈ xs ⊎ w ∈ ys
to w [] ys w∈ = inj₂ w∈
to w (x ∷ xs) [] w∈ = inj₁ w∈
to w (x ∷ xs) (y ∷ ys) w∈ with x ≤? y | w∈
to w (x ∷ xs) (y ∷ ys) w∈    | yes _  | zero = inj₁ zero
to w (x ∷ xs) (y ∷ ys) w∈    | yes _  | suc w∈xsyys with to w xs (y ∷ ys) w∈xsyys
to w (x ∷ xs) (y ∷ ys) w∈    | yes _  | suc w∈xsyys    | inj₁ w∈xs = inj₁ (suc w∈xs)
to w (x ∷ xs) (y ∷ ys) w∈    | yes _  | suc w∈xsyys    | inj₂ w∈yys = inj₂ w∈yys
to w (x ∷ xs) (y ∷ ys) w∈    | no _   | zero = inj₂ zero
to w (x ∷ xs) (y ∷ ys) w∈    | no _   | suc w∈xxsys with to w (x ∷ xs) ys w∈xxsys
to w (x ∷ xs) (y ∷ ys) w∈    | no _   | suc w∈xxsys    | inj₁ w∈xxs = inj₁ w∈xxs
to w (x ∷ xs) (y ∷ ys) w∈    | no _   | suc w∈xxsys    | inj₂ w∈ys = inj₂ (suc w∈ys)

fromˡ : (w : ℕ) →  (xs ys : List ℕ) → w ∈ xs → w ∈ merge xs ys
fromˡ w (x ∷ xs) [] w∈ = w∈
fromˡ w (x ∷ xs) (y ∷ ys) w∈ with x ≤? y | w∈
fromˡ w (x ∷ xs) (y ∷ ys) w∈    | yes _  | zero = zero
fromˡ w (x ∷ xs) (y ∷ ys) w∈    | yes _  | suc w∈xs = suc (fromˡ w xs (y ∷ ys) w∈xs)
fromˡ w (x ∷ xs) (y ∷ ys) w∈    | no _   | zero = suc (fromˡ w (x ∷ xs) ys zero)
fromˡ w (x ∷ xs) (y ∷ ys) w∈    | no _   | suc w∈xs = suc (fromˡ w (x ∷ xs) ys (suc w∈xs))

fromʳ : (w : ℕ) → (xs ys : List ℕ) → w ∈ ys → w ∈ merge xs ys
fromʳ w [] (y ∷ ys) w∈ = w∈
fromʳ w (x ∷ xs) (y ∷ ys) w∈ with x ≤? y | w∈
fromʳ w (x ∷ xs) (y ∷ ys) w∈    | yes _  | zero = suc (fromʳ w xs (y ∷ ys) zero)
fromʳ w (x ∷ xs) (y ∷ ys) w∈    | yes _  | suc w∈ys = suc (fromʳ w xs (y ∷ ys) w∈)
fromʳ w (x ∷ xs) (y ∷ ys) w∈    | no _   | zero = zero
fromʳ w (x ∷ xs) (y ∷ ys) w∈    | no _   | suc w∈ys = suc (fromʳ w (x ∷ xs) ys w∈ys)

from : (w : ℕ) → (xs ys : List ℕ) → (w ∈ xs) ⊎ (w ∈ ys) → w ∈ merge xs ys
from w xs ys (inj₁ w∈xs) = fromˡ w xs ys w∈xs
from w xs ys (inj₂ w∈ys) = fromʳ w xs ys w∈ys

from∘to : (w : ℕ) → (xs ys : List ℕ)
  → (w∈ : w ∈ merge xs ys)
  → from w xs ys (to w xs ys w∈) ≡ w∈
from∘to w [] (y ∷ ys) w∈ = refl
from∘to w (x ∷ xs) [] w∈ = refl
from∘to w (x ∷ xs) (y ∷ ys) w∈ = {!!}

to∘from : (w : ℕ) → (xs ys : List ℕ)
  → (w∈ : w ∈ xs ⊎ w ∈ ys)
  → to w xs ys (from w xs ys w∈) ≡ w∈
to∘from w [] (y ∷ ys) (inj₂ w∈ys) = refl
to∘from w (x ∷ xs) [] (inj₁ w∈xxs) = refl
to∘from w (x ∷ xs) (x₁ ∷ ys) w∈ = {!!}

≰→≤ : {m n : ℕ} → ¬ (m ≤ n) → n ≤ m
≰→≤ {zero} {n} m≰n = ⊥-elim (m≰n z≤n)
≰→≤ {suc m} {zero} m≰n = z≤n
≰→≤ {suc m} {suc n} m≰n = s≤s (≰→≤ (m≰n ∘ s≤s))

merge-Sorted : (xs ys : List ℕ) → Sorted xs → Sorted ys → Sorted (merge xs ys)
merge-Sorted [] ys Sxs Sys = Sys
merge-Sorted (x ∷ xs) [] Sxxs Sys = Sxxs
merge-Sorted (x ∷ xs) (y ∷ ys) (x ∷ Sxs) (y ∷ Sys) with x ≤? y
... | yes x≤y = x ∷ f
  where
    f : {w : ℕ} → w ∈ merge xs (y ∷ ys) → x ≤ w
    f {w} w∈ with to w xs (y ∷ ys) w∈
    ... | inj₁ w∈xs = Sxs w∈xs
    ... | inj₂ zero = x≤y
    ... | inj₂ (suc w∈ys) = ≤-trans x≤y (Sys w∈ys)
... | no x≰y = y ∷ f
  where
    f : {w : ℕ} → w ∈ merge (x ∷ xs) ys → y ≤ w
    f {w} w∈ with to w (x ∷ xs) ys w∈
    ... | inj₁ zero = ≰→≤ x≰y
    ... | inj₁ (suc w∈xs) = ≤-trans (≰→≤ x≰y) (Sxs w∈xs)
    ... | inj₂ w∈ys = Sys w∈ys

split : List ℕ → (List ℕ) × (List ℕ)
split [] = [] , []
split (x ∷ []) = [ x ] , []
split (y ∷ z ∷ xs) with split xs
... | ys , zs = y ∷ ys , z ∷ zs

sort : List ℕ → List ℕ
sort xs = go (length xs) xs
  where
    go : ℕ → List ℕ → List ℕ
    go zero _ = []
    go (suc n) [] = []
    go (suc n) (x ∷ []) = [ x ]
    go (suc n) xs@(_ ∷ _ ∷ _) with split xs
    ... | ys , zs = merge (go n ys) (go n zs)

