module experimental.itaiz.Injection where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (∃-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)

infix 3 _⦉_

record _⦉_ (A B : Set) : Set where
  field
    to : A → B
    to-inj : (x y : A) → to x ≡ to y → x ≡ y

zero≢suc : {n : ℕ} → {j : Fin n} → Data.Fin.zero ≢ suc j
zero≢suc ()

suc-inj : {n : ℕ} → {i j : Fin n} → Data.Fin.suc i ≡ suc j → i ≡ j
suc-inj refl = refl

suc-inj' : {n : ℕ} → {i j : Fin n} → Data.Fin.suc i ≢ suc j → i ≢ j
suc-inj' si≢sj i≡j = si≢sj (cong suc i≡j)

-- Delete an element from a finite set to get a (map to a) smaller set.

del : {n : ℕ} → (c : Fin (suc n)) → ∃[ j ] c ≢ j → Fin n
del {n} zero (zero , c≢j) = ⊥-elim (c≢j refl)
del {suc n} zero (suc j , c≢j) = j
del {suc n} (suc c) (zero , c≢j) = zero
del {suc n} (suc c) (suc j , sc≢sj) = suc (del c (j , λ c≡j → sc≢sj (cong suc c≡j)))

-- With extensionality, we can even prove that `del c` is injective.

-- Can we do this with fewer cases?
del-inj : {n : ℕ} → (c : Fin (suc n)) → ((i j : ∃[ j ] c ≢ j) → del c i ≡ del c j → proj₁ i ≡ proj₁ j)
del-inj {zero} zero (zero , _) (zero , _) _ = refl
del-inj {suc n} zero (zero , _) (zero , _) _ = refl
del-inj {suc n} zero (zero , 0≢0) (suc j , 0≢sj) _ = ⊥-elim (0≢0 refl)
del-inj {suc n} zero (suc i , 0≢si) (zero , 0≢0) _ = ⊥-elim (0≢0 refl)
del-inj {suc n} zero (suc i , 0≢i) (suc j , 0≢j) refl = refl
del-inj {suc n} (suc c) (zero , sc≢i) (zero , sc≢j) _ = refl
del-inj {suc n} (suc c) (suc i , sc≢si) (suc j , sc≢sj) dsi≡dsj =
  cong suc (del-inj c (i , suc-inj' sc≢si) (j , suc-inj' sc≢sj) (suc-inj dsi≡dsj))

-- Idea of the proof:
--
--    suc :       Fin m                            ⦉ Σ[ j ∈ Fin (suc m) ] zero ≢ j
--    hypothesis: Σ[ j ∈ Fin (suc m) ] zero ≢ j    ⦉ Σ[ j ∈ Fin (suc n) ] to zero ≢ j
--    delete:     Σ[ j ∈ Fin (suc n) ] to zero ≢ j ⦉ Fin n
--
-- Since we need extensionality to show equality of Σ-types for injectivity, we
-- do it more directly instead.

Fs⦉F : {m n : ℕ} → Fin (suc m) ⦉ Fin (suc n) → Fin m ⦉ Fin n
Fs⦉F {m} {n} Fsm⦉Fsn = record
  { to = λ i → del t0 (ts i)
  ; to-inj = λ i j ti≡tj → suc-inj (to-inj (suc i) (suc j) (del-inj t0 (ts i) (ts j) ti≡tj))
  }
  where
    open _⦉_ Fsm⦉Fsn
    t0 : Fin (suc n)
    t0 = to  zero
    ts : Fin m → ∃[ j ] t0 ≢ j
    ts i = to (suc i) , λ t0≡ts → zero≢suc (to-inj zero (suc i) t0≡ts)

Fm⦉Fn→m≤n : {m n : ℕ} → Fin m ⦉ Fin n → m ≤ n
Fm⦉Fn→m≤n {zero} {n} F0⦉Fn = z≤n
Fm⦉Fn→m≤n {suc m} {zero} Fsm⦉F0 with _⦉_.to Fsm⦉F0 zero
... | ()
Fm⦉Fn→m≤n {suc m} {suc n} Fsm⦉Fsn = s≤s (Fm⦉Fn→m≤n (Fs⦉F Fsm⦉Fsn))

open import experimental.itaiz.Isomorphism
open Relation.Binary.PropositionalEquality.≡-Reasoning

≲→⦉ : {A B : Set} → A ≲ B → A ⦉ B
≲→⦉ A≲B = record
  { to = to
  ; to-inj = λ x y tx≡ty → (begin
    x
    ≡⟨ sym (from∘to x) ⟩
    from (to x)
    ≡⟨ cong from tx≡ty ⟩
    from (to y)
    ≡⟨ from∘to y ⟩
    y
    ∎)
  }
  where
    open _≲_ A≲B

Fm≲Fn→m≤n : {m n : ℕ} → Fin m ≲ Fin n → m ≤ n
Fm≲Fn→m≤n Fm≲Fn = Fm⦉Fn→m≤n (≲→⦉ Fm≲Fn)
