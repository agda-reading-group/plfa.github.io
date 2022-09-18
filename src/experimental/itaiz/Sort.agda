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

merge→ : (xs ys : List ℕ) → (w : ℕ) → w ∈ merge xs ys → w ∈ xs ⊎ w ∈ ys
merge→ [] ys w w∈ = inj₂ w∈
merge→ (x ∷ xs) [] w w∈ = inj₁ w∈
merge→ (x ∷ xs) (y ∷ ys) w w∈ with x ≤? y | w∈
merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | zero = inj₁ zero
merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xsyys with merge→ xs (y ∷ ys) w w∈xsyys
merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xxsys    | inj₁ w∈xs = inj₁ (suc w∈xs)
merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xxsys    | inj₂ w∈yys = inj₂ w∈yys
merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | zero = inj₂ zero
merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xxsys with merge→ (x ∷ xs) ys w w∈xxsys
merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xsyys    | inj₁ w∈xxs = inj₁ w∈xxs
merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xsyys    | inj₂ w∈ys = inj₂ (suc w∈ys)

merge←ˡ : (xs ys : List ℕ) → (w : ℕ) →  w ∈ xs → w ∈ merge xs ys
merge←ˡ (x ∷ xs) [] w w∈ = w∈
merge←ˡ (x ∷ xs) (y ∷ ys) w w∈ with x ≤? y | w∈
merge←ˡ (x ∷ xs) (y ∷ ys) .x w∈   | yes _  | zero = zero
merge←ˡ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xs = suc (merge←ˡ xs (y ∷ ys) w w∈xs)
merge←ˡ (x ∷ xs) (y ∷ ys) .x w∈   | no _   | zero = suc (merge←ˡ (x ∷ xs) ys x zero)
merge←ˡ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xs = suc (merge←ˡ (x ∷ xs) ys w (suc w∈xs))

merge←ʳ : (xs ys : List ℕ) → (w : ℕ) →  w ∈ ys → w ∈ merge xs ys
merge←ʳ [] (y ∷ ys) w w∈ = w∈
merge←ʳ (x ∷ xs) (y ∷ ys) w w∈ with x ≤? y | w∈
merge←ʳ (x ∷ xs) (y ∷ ys) .y w∈   | yes _  | zero = suc (merge←ʳ xs (y ∷ ys) y zero)
merge←ʳ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈ys = suc (merge←ʳ xs (y ∷ ys) w w∈)
merge←ʳ (x ∷ xs) (y ∷ ys) .y w∈   | no _   | zero = zero
merge←ʳ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈ys = suc (merge←ʳ (x ∷ xs) ys w w∈ys)

merge← : (xs ys : List ℕ) → (w : ℕ) → (w ∈ xs) ⊎ (w ∈ ys) → w ∈ merge xs ys
merge← xs ys w (inj₁ w∈xs) = merge←ˡ xs ys w w∈xs
merge← xs ys w (inj₂ w∈ys) = merge←ʳ xs ys w w∈ys

merge←∘merge→ : (xs ys : List ℕ) → (w : ℕ)
  → (w∈ : w ∈ merge xs ys)
  → merge← xs ys w (merge→ xs ys w w∈) ≡ w∈
merge←∘merge→ [] (y ∷ ys) w w∈ = refl
merge←∘merge→ (x ∷ xs) [] w w∈ = refl
merge←∘merge→ (x ∷ xs) (y ∷ ys) w w∈ = {!!}
{-
  where
    xxx : x ≤? y
    xxx = ?
-}

{-
--with x ≤? y
--... | q = {!!} --with x ≤? y | w∈

merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | zero = ?
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xsyys with merge→ xs (y ∷ ys) w w∈xsyys
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xxsys    | inj₁ w∈xs = ?
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | yes _  | suc w∈xxsys    | inj₂ w∈yys = ?
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | zero = ?
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xxsys with merge→ (x ∷ xs) ys w w∈xxsys
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xsyys    | inj₁ w∈xxs = ?
merge←ˡmerge←ʳ∘merge→ (x ∷ xs) (y ∷ ys) w w∈    | no _   | suc w∈xsyys    | inj₂ w∈ys = ?
-}

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
    f {w} w∈ with merge→ xs (y ∷ ys) w w∈
    ... | inj₁ w∈xs = Sxs w∈xs
    ... | inj₂ zero = x≤y
    ... | inj₂ (suc w∈ys) = ≤-trans x≤y (Sys w∈ys)
... | no x≰y = y ∷ f
  where
    f : {w : ℕ} → w ∈ merge (x ∷ xs) ys → y ≤ w
    f {w} w∈ with merge→ (x ∷ xs) ys w w∈
    ... | inj₁ zero = ≰→≤ x≰y
    ... | inj₁ (suc w∈xs) = ≤-trans (≰→≤ x≰y) (Sxs w∈xs)
    ... | inj₂ w∈ys = Sys w∈ys

split : List ℕ → (List ℕ) × (List ℕ)
split [] = [] , []
split (x ∷ []) = [ x ] , []
split (y ∷ z ∷ xs) with split xs
... | ys , zs = y ∷ ys , z ∷ zs
