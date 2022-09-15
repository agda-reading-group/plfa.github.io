{-
  I used `sum ∘ count ≡ length` to prove that there is enough gas.
  This relation was very complicated to prove and use.
  count converts a list to a multiset.
  Of course, this relation should be part of a library, so proper use of a library should make it easy.
  Also, if we have a multiset library, and a library with relations between lists and multisets,
  isn't the permutation property of sort simpler?
  i.e. the following should be part of a library: `count xs ≡ count ys ⇔ Perm xs ys`
  In summary, this should be simpler if I don't switch styles half way through.
-}

module experimental.mdel.Sort where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Bool using (Bool; false; true; not)
open import Data.Empty
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Nullary -- When restricting import, make sure C-c C-c (false because proof) to (no p) works.
open import plfa.part1.Isomorphism using (_≃_; _⇔_; _≲_; extensionality; ∀-extensionality; ≃-trans; ≃-sym)
open plfa.part1.Isomorphism.≃-Reasoning

---------------- Util ----------------

m≤sm : (m : ℕ) → m ≤ suc m
m≤sm zero = z≤n
m≤sm (suc m) = s≤s (m≤sm m)

¬sm≤m : (m : ℕ) → ¬ suc m ≤ m
¬sm≤m (suc m) (s≤s sm≤m) = ¬sm≤m m sm≤m

<→≢ : {m n : ℕ} → m < n → ¬ (m ≡ n)
<→≢ {zero} {suc n} _ ()
<→≢ {suc m} {suc .m} (s≤s m<n) refl = ¬sm≤m m m<n

<→s≢ : {m n : ℕ} → n ≤ m → ¬ (suc m ≡ n)
<→s≢ {m} {n} m<n refl = ⊥-elim (¬sm≤m m m<n)

<→≤ : {m n : ℕ} → m < n → m ≤ n
<→≤ {zero} {suc n} (s≤s m<n) = z≤n
<→≤ {suc m} {suc n} (s≤s m<n) = s≤s (<→≤ m<n)

¬m<m : (m : ℕ) → ¬ m < m
¬m<m (suc m) (s≤s m<m) = ¬m<m m m<m

<→¬≡ : {m n : ℕ} → m < n → ¬ m ≡ n
<→¬≡ {m} {n} m<n refl = ¬m<m m m<n

≢-pred : {m n : ℕ} → suc m ≢ suc n → m ≢ n
≢-pred {m} {.m} sm≢sn refl = sm≢sn refl

≮-pred : {m n : ℕ} → suc m ≮ suc n → m ≮ n
≮-pred {m} {n} sm≮sn m<n = sm≮sn (s≤s m<n)

m≮n&m≤n : {m n : ℕ} → m ≮ n → m ≤ n → m ≡ n
m≮n&m≤n {zero} {zero} _ _ = refl
m≮n&m≤n {zero} {suc n} m≮n _ = ⊥-elim (m≮n (s≤s z≤n))
m≮n&m≤n {suc m} {suc n} m≮n (s≤s m≤n) = cong suc (m≮n&m≤n (≮-pred m≮n) m≤n)

><-m≡n : {m n : ℕ} → ¬ m < n → ¬ n < m → m ≡ n
><-m≡n {zero} {zero} ¬m<n ¬n<m = refl
><-m≡n {zero} {suc n} ¬m<n ¬n<m = ⊥-elim (¬m<n (s≤s z≤n))
><-m≡n {suc m} {zero} ¬m<n ¬n<m = ⊥-elim (¬n<m (s≤s z≤n))
><-m≡n {suc m} {suc n} ¬m<n ¬n<m = cong suc (><-m≡n (λ z → ¬m<n (s≤s z)) (λ z → ¬n<m (s≤s z)))

≤&≢→< : {m n : ℕ} → m ≤ n → m ≢ n → m < n
≤&≢→< {zero} {zero} z≤n m≢n = ⊥-elim (m≢n refl)
≤&≢→< {zero} {suc n} z≤n m≢n = s≤s z≤n
≤&≢→< {suc m} {suc n} (s≤s m≤n) m≢n = s≤s (≤&≢→< m≤n (≢-pred m≢n))

a+[b+c]≡b+[a+c] : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
a+[b+c]≡b+[a+c] a b c =
  begin
    a + (b + c)
  ≡⟨ sym (+-assoc a b c) ⟩
    (a + b) + c
  ≡⟨ cong (_+ c) (+-comm a b) ⟩
    (b + a) + c
  ≡⟨ +-assoc b a c ⟩
    b + (a + c)
  ∎

a+b+[c+d]≡a+[c+[b+d]] : (a b c d : ℕ) → a + b + (c + d) ≡ a + (c + (b + d))
a+b+[c+d]≡a+[c+[b+d]] a b c d =
  begin
    a + b + (c + d)
  ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))
  ≡⟨ cong (a +_) (a+[b+c]≡b+[a+c] b c d) ⟩
    a + (c + (b + d))
  ∎

a+b+[c+d]≡a+c+[b+d] : (a b c d : ℕ) → a + b + (c + d) ≡ a + c + (b + d)
a+b+[c+d]≡a+c+[b+d] a b c d =
  begin
    a + b + (c + d)
  ≡⟨ a+b+[c+d]≡a+[c+[b+d]] a b c d ⟩
    a + (c + (b + d))
  ≡⟨ sym (+-assoc a c (b + d)) ⟩
    a + c + (b + d)
  ∎

0<m+n→⊎ : {m n : ℕ} → 0 < m + n → 0 < m ⊎ 0 < n
0<m+n→⊎ {zero} {n} 0<m+n = inj₂ 0<m+n
0<m+n→⊎ {suc m} {n} 0<m+n = inj₁ (s≤s z≤n)

norm-sm+sn≤o : {m n o : ℕ} → suc (m + suc n) ≤ o → suc (suc (m + n)) ≤ o
norm-sm+sn≤o {m} {n} {o} pre rewrite +-suc m n = pre

norm-sm+sn≤o-pred : {m n o : ℕ} → suc (m + suc n) ≤ o → suc (m + n) ≤ o
norm-sm+sn≤o-pred {m} {n} pre = ≤-trans (m≤sm (suc (m + n))) (norm-sm+sn≤o pre)

⊔-≤-l : {m n o : ℕ} → m ⊔ n ≤ o → m ≤ o
⊔-≤-l {zero} {zero} {o} pre = pre
⊔-≤-l {suc m} {zero} {o} pre = pre
⊔-≤-l {zero} {suc n} {o} pre = z≤n
⊔-≤-l {suc m} {suc n} {suc o} (s≤s pre) = s≤s (⊔-≤-l pre)

⊔-≤-r : {m n o : ℕ} → m ⊔ n ≤ o → n ≤ o
⊔-≤-r {zero} {n} {o} pre = pre
⊔-≤-r {suc m} {zero} {o} pre = z≤n
⊔-≤-r {suc m} {suc n} {suc o} (s≤s pre) = s≤s (⊔-≤-r pre)

⊓→≡ : (m n : ℕ) → m ⊓ n ≡ m ⊎ m ⊓ n ≡ n
⊓→≡ zero n = inj₁ refl
⊓→≡ (suc m) zero = inj₂ refl
⊓→≡ (suc m) (suc n) with ⊓→≡ m n
... | inj₁ x = inj₁ (cong suc x)
... | inj₂ x = inj₂ (cong suc x)

m⊓n≤o→ : {m n o : ℕ} → m ⊓ n ≤ o → m ≤ o ⊎ n ≤ o
m⊓n≤o→ {m} {n} {o} pre with ⊓→≡ m n
... | inj₁ eq rewrite eq = inj₁ pre
... | inj₂ eq rewrite eq = inj₂ pre


m≤m⊔n⊔o : (m n o : ℕ) → m ≤ m ⊔ n ⊔ o
m≤m⊔n⊔o m n o = ≤-trans (m≤m⊔n m n) (m≤m⊔n (m ⊔ n) o)

n≤m⊔n⊔o : (m n o : ℕ) → n ≤ m ⊔ n ⊔ o
n≤m⊔n⊔o m n o = ≤-trans (m≤n⊔m m n) (m≤m⊔n (m ⊔ n) o)

o≤m⊔n⊔o : (m n o : ℕ) → o ≤ m ⊔ n ⊔ o
o≤m⊔n⊔o m n o = m≤n⊔m (m ⊔ n) o

---------------- List & Sort ----------------

data List : Set where
  [] : List
  _::_ : (x : ℕ) → (xs : List) → List
infixr 5 _::_

-- From Lists.lagda.md
data Any (P : ℕ → Set) : List → Set where
  here  : {x : ℕ} → {xs : List} → P x → Any P (x :: xs)
  there : {x : ℕ} → {xs : List} → Any P xs → Any P (x :: xs)
infix 4 _∈_
_∈_ : (x : ℕ) (xs : List) → Set
x ∈ xs = Any (x ≡_) xs

P-list : (P : ℕ → Set) → (xs : List) → Set
P-list P xs = (w : ℕ) → (w ∈ xs) → P w

≤-list : ℕ → List → Set
≤-list x xs = P-list (x ≤_) xs

≤-list-[] : (x : ℕ) → ≤-list x []
≤-list-[] x w ()

length : List → ℕ
length [] = 0
length (x :: xs) = suc (length xs)

_=n_ : ℕ → ℕ → ℕ
m =n n with m ≟ n
... | yes _ = 1
... | no _ = 0

=n-refl : (m : ℕ) → m =n m ≡ 1
=n-refl m with m ≟ m
... | yes p = refl
... | no ¬p = ⊥-elim (¬p refl)

=n-≢ : {m n : ℕ} → (m ≢ n) → m =n n ≡ 0
=n-≢ {m} {n} m≢n with m ≟ n
... | yes refl = ⊥-elim (m≢n refl)
... | no _ = refl

-- count converts a List into a multiset.
count : List → ℕ → ℕ
count [] w = 0
-- Why is paren necessary here? Even with `infix _=n_ 0`, it's necessary.
count (x :: xs) w = (x =n w) + count xs w

Perm : List → List → Set
Perm xs ys = (w : ℕ) → count xs w ≡ count ys w

count→∈ : (w : ℕ) → (xs : List) → 0 < count xs w → w ∈ xs
count→∈ w (x :: xs) 0<c with x ≟ w
... | yes refl = here refl
... | no ¬x≡w = there (count→∈ w xs 0<c)

∈→count : (w : ℕ) → (xs : List) → w ∈ xs → 0 < count xs w
∈→count w (.w :: xs) (here refl) rewrite =n-refl w = s≤s z≤n
∈→count w (x :: xs) (there w∈xs) =
  ≤-trans (∈→count w xs w∈xs) (m≤n+m (count xs w) (x =n w))

Is-bound : (ℕ → ℕ) → ℕ → Set
Is-bound f hi = (w : ℕ) → hi ≤ w → f w ≡ 0

sum-bound-help : (ℕ → ℕ) → ℕ → ℕ
sum-bound-help f zero = zero
sum-bound-help f (suc w) = f w + sum-bound-help f w

sum-bound : (f : ℕ → ℕ) → ∃[ hi ](Is-bound f hi) → ℕ
sum-bound f (hi , _) = sum-bound-help f hi

sum-bound-help-loosen : (f : ℕ → ℕ) → (m m' : ℕ) → Is-bound f m → (m ≤ m') → sum-bound-help f m ≡ sum-bound-help f m'
sum-bound-help-loosen f m m' is-bound m≤m' with m <? m'
... | no ¬m<m' with m≮n&m≤n ¬m<m' m≤m'
...    | refl = refl
sum-bound-help-loosen f m (suc m') is-bound _ | yes sm≤sm' rewrite is-bound m' (≤-pred sm≤sm') =
  sum-bound-help-loosen f m m' is-bound (≤-pred sm≤sm')

⊓-Is-bound : (f : ℕ → ℕ) → (is-b : ∃[ hi ](Is-bound f hi)) → (is-b' : ∃[ hi' ](Is-bound f hi'))
           → (∃[ hi⊓ ](Is-bound f hi⊓ × (hi⊓ ≤ proj₁ is-b) × (hi⊓ ≤ proj₁ is-b')))
⊓-Is-bound f (hi , is-b) (hi' , is-b') = hi ⊓ hi' , is-b⊓ , m⊓n≤m hi hi' , m⊓n≤n hi hi'
  where
    is-b⊓ : (w : ℕ) → hi ⊓ hi' ≤ w → f w ≡ 0
    is-b⊓ w ≤w with m⊓n≤o→ ≤w
    ... | inj₁ hi≤w = is-b w hi≤w
    ... | inj₂ hi'≤w = is-b' w hi'≤w

sum-bound-ignore : (f : ℕ → ℕ) → (is-b : ∃[ hi ](Is-bound f hi)) → (is-b' : ∃[ hi' ](Is-bound f hi'))
                  → sum-bound f is-b ≡ sum-bound f is-b'
sum-bound-ignore f is-b@(hi , _) is-b'@(hi' , _) with ⊓-Is-bound f is-b is-b'
... | hi⊓ , is-b⊓ , hi⊓≤hi , hi⊓≤hi' =
  begin
    sum-bound f is-b
  ≡⟨⟩
    sum-bound-help f hi
  ≡⟨ sym (sum-bound-help-loosen f hi⊓ hi is-b⊓ hi⊓≤hi) ⟩
    sum-bound-help f hi⊓
  ≡⟨ sum-bound-help-loosen f hi⊓ hi' is-b⊓ hi⊓≤hi' ⟩
    sum-bound-help f hi'
  ≡⟨⟩
    sum-bound f is-b'
  ∎

sum-bound-ignore-f' : (f f' : ℕ → ℕ) → (is-b : ∃[ hi ](Is-bound f hi)) → (is-b' : ∃[ hi' ](Is-bound f' hi'))
                    → f ≡ f' → sum-bound f is-b ≡ sum-bound f' is-b'
sum-bound-ignore-f' f f' is-b is-b' refl = sum-bound-ignore f is-b is-b'

_f+_ : {A : Set} → (A → ℕ) → (A → ℕ) → (A → ℕ)
f f+ g = λ a → f a + g a

mk-is-bound-f+ : (f f' : ℕ → ℕ) → (is-b : ∃[ hi ](Is-bound f hi)) → (is-b' : ∃[ hi' ](Is-bound f' hi'))
               → ∃[ hi+ ](Is-bound (f f+ f') hi+)
mk-is-bound-f+ f f' (hi , is-b) (hi' , is-b') = hi+ , is-b+
  where
    hi+ = hi ⊔ hi'
    is-b+ : (w : ℕ) → hi+ ≤ w → (f f+ f') w ≡ 0
    is-b+ w hi+≤ rewrite is-b w (≤-trans (m≤m⊔n hi hi') hi+≤) = is-b' w (≤-trans (m≤n⊔m hi hi') hi+≤)

sum-bound-help-f+ : (f f' : ℕ → ℕ) → (w : ℕ) → sum-bound-help (f f+ f') w ≡ sum-bound-help f w + sum-bound-help f' w
sum-bound-help-f+ f f' zero = refl
sum-bound-help-f+ f f' (suc w) rewrite sum-bound-help-f+ f f' w =
  a+b+[c+d]≡a+c+[b+d] (f w) (f' w) (sum-bound-help f w) (sum-bound-help f' w)

sum-bound-f+ : (f f' : ℕ → ℕ) → (is-b : ∃[ hi ](Is-bound f hi)) → (is-b' : ∃[ hi' ](Is-bound f' hi'))
             → (is-b+ : ∃[ hi+ ](Is-bound (f f+ f') hi+))
             → sum-bound (f f+ f') is-b+ ≡ sum-bound f is-b + sum-bound f' is-b'
sum-bound-f+ f f' (hi , is-b) (hi' , is-b') (hi+ , is-b+) =
  begin
    sum-bound-help (f f+ f') hi+
  ≡⟨ sum-bound-help-loosen (f f+ f') hi+ hi⊔ is-b+ hi+≤ ⟩
    sum-bound-help (f f+ f') hi⊔
  ≡⟨ sum-bound-help-f+ f f' hi⊔ ⟩
    sum-bound-help f hi⊔ + sum-bound-help f' hi⊔
  ≡⟨ cong (_+ sum-bound-help f' hi⊔) (sym (sum-bound-help-loosen f hi hi⊔ is-b hi≤)) ⟩
    sum-bound-help f hi + sum-bound-help f' hi⊔
  ≡⟨ cong (sum-bound-help f hi +_) (sym (sum-bound-help-loosen f' hi' hi⊔ is-b' hi'≤)) ⟩
    sum-bound-help f hi + sum-bound-help f' hi'
  ∎
  where
    hi⊔ = hi ⊔ hi' ⊔ hi+
    hi≤ : hi ≤ hi⊔
    hi≤ = m≤m⊔n⊔o hi hi' hi+
    hi'≤ : hi' ≤ hi⊔
    hi'≤ = n≤m⊔n⊔o hi hi' hi+
    hi+≤ : hi+ ≤ hi⊔
    hi+≤ = o≤m⊔n⊔o hi hi' hi+

is-bound-count : (xs : List) → ∃[ hi ](Is-bound (count xs) hi)
is-bound-count [] = 0 , λ _ _ → refl
is-bound-count (x :: xs) with is-bound-count xs
... | (hi , ≡0) = hi' , ≡0'
  where
    hi' = suc x ⊔ hi
    ≡0' : (w : ℕ) → hi' ≤ w → count (x :: xs) w ≡ 0
    ≡0' w hi'≤w with x ≟ w
    ... | yes refl = ⊥-elim (¬sm≤m w (⊔-≤-l {suc w} {hi} hi'≤w))
    ... | no ¬x≡w = ≡0 w (⊔-≤-r hi'≤w)

sum-count-help-small : (w x : ℕ) → (xs : List) → (w ≤ x) → sum-bound-help (count (x :: xs)) w ≡ sum-bound-help (count xs) w
sum-count-help-small zero _ _ _ = refl
sum-count-help-small (suc w) (suc x) xs (s≤s w≤x) with =n-≢ {suc x} {w} (<→s≢ w≤x)
... | sx=w=0 rewrite sx=w=0 = cong (count xs w +_) (sum-count-help-small w (suc x) xs (≤-trans w≤x (m≤sm x)))

sum-count-help-big : (w x : ℕ) → (xs : List) → (x < w) → sum-bound-help (count (x :: xs)) w ≡ suc (sum-bound-help (count xs) w)
sum-count-help-big (suc w) x xs (s≤s x≤w) with x ≟ w
... | yes refl = cong (λ hole → suc (count xs w + hole)) (sum-count-help-small w w xs ≤-refl)
... | no ¬x≡w =
  begin
    count xs w + sum-bound-help (count (x :: xs)) w
  ≡⟨ cong (count xs w +_) (sum-count-help-big w x xs (≤&≢→< x≤w ¬x≡w)) ⟩
    count xs w + suc (sum-bound-help (count xs) w)
  ≡⟨ +-suc (count xs w) (sum-bound-help (count xs) w) ⟩
    suc (count xs w + sum-bound-help (count xs) w)
  ∎

sum-count-:: : (x : ℕ) → (xs : List)
             → sum-bound (count (x :: xs)) (is-bound-count (x :: xs)) ≡ suc (sum-bound (count xs) (is-bound-count xs))
sum-count-:: x xs with is-bound-count (x :: xs) | is-bound-count xs
... | (hi' , is-bound') | (hi , is-bound) =
  begin
    sum-bound-help (count (x :: xs)) (suc x ⊔ hi)
  ≡⟨ sum-count-help-big (suc x ⊔ hi) x xs (m≤m⊔n (suc x) hi) ⟩
    suc (sum-bound-help (count xs) (suc x ⊔ hi))
  ≡⟨ cong suc (sym (sum-bound-help-loosen (count xs) hi (suc x ⊔ hi) is-bound ((m≤n⊔m (suc x) hi)))) ⟩
    suc (sum-bound-help (count xs) hi)
  ∎

sum-count≡length : (xs : List) → sum-bound (count xs) (is-bound-count xs) ≡ length xs
sum-count≡length [] = refl
sum-count≡length (x :: xs) =
  begin
    sum-bound (count (x :: xs)) (is-bound-count (x :: xs))
  ≡⟨ sum-count-:: x xs ⟩
    suc (sum-bound (count xs) (is-bound-count xs))
  ≡⟨ cong suc (sum-count≡length xs) ⟩
    suc (length xs)
  ≡⟨⟩
    length (x :: xs)
  ∎

count→len : (xs ys : List) → ((w : ℕ) → count xs w ≡ count ys w) → length xs ≡ length ys
count→len xs ys w→≡ =
  begin
    length xs
  ≡⟨ sym (sum-count≡length xs) ⟩
    sum-bound (count xs) (is-bound-count xs)
  ≡⟨ sum-bound-ignore-f' (count xs) (count ys) (is-bound-count xs) (is-bound-count ys) (extensionality w→≡) ⟩
    sum-bound (count ys) (is-bound-count ys)
  ≡⟨ sum-count≡length ys ⟩
    length ys
  ∎

count→len-+ : (xs ys zs : List) → ((w : ℕ) → count xs w ≡ count ys w + count zs w) → length xs ≡ length ys + length zs
count→len-+ xs ys zs w→c-≡ =
  begin
   length xs
  ≡⟨ sym (sum-count≡length xs) ⟩
   sum-bound (count xs) (is-bound-count xs)
  ≡⟨ sum-bound-ignore-f' (count xs) (count ys f+ count zs) (is-bound-count xs) is-b+ c-≡ ⟩
   sum-bound (count ys f+ count zs) is-b+
  ≡⟨ sum-bound-f+ (count ys) (count zs) (is-bound-count ys) (is-bound-count zs) is-b+ ⟩
   sum-bound (count ys) (is-bound-count ys) + sum-bound (count zs) (is-bound-count zs)
  ≡⟨ cong (_+ sum-bound (count zs) (is-bound-count zs)) (sum-count≡length ys) ⟩
   length ys + sum-bound (count zs) (is-bound-count zs)
  ≡⟨ cong (length ys +_) (sum-count≡length zs) ⟩
    length ys + length zs
  ∎
  where
    is-b+ : ∃[ hi+ ](Is-bound (count ys f+ count zs) hi+)
    is-b+ = mk-is-bound-f+ (count ys) (count zs) (is-bound-count ys) (is-bound-count zs)
    c-≡ : count xs ≡ (count ys f+ count zs)
    c-≡ = extensionality w→c-≡

-- Style is:
-- 1. Split each case into [] and (x :: xs).
--    This makes all clauses hold "definitionally", prevents the grey highlight,
--    and should make it easier for the proof structure to follow the function structure.
-- 2. Cases on (x <? y), which gives the property to proofs inside cases.
merge : ℕ → List → List → List
merge zero _ _ = [] -- do not care
merge (suc gas) [] ys = ys
merge (suc gas) (x :: xs) [] = x :: xs
merge (suc gas) (x :: xs) (y :: ys) with (x <? y) | (y <? x)
... | (yes _) | _ = x :: merge gas xs (y :: ys)
... | (no _) | (yes _) = y :: merge gas (x :: xs) ys
... | (no _) | (no _) = x :: y :: merge gas xs ys

merge-count : (w : ℕ) → (gas : ℕ) → (xs ys : List)
            → length xs + length ys < gas
            → count xs w + count ys w ≡ count (merge gas xs ys) w
merge-count w zero _ _ ()
merge-count w (suc gas) [] ys <-gas = refl
merge-count w (suc gas) (x :: xs) [] <-gas = +-identityʳ (count (x :: xs) w)
merge-count w (suc gas) (x :: xs) (y :: ys) (s≤s <-gas) with (x <? y) | (y <? x)
... | (yes _) | _ =
  begin
    count (x :: xs) w + count (y :: ys) w
  ≡⟨⟩
    x =n w + count xs w + count (y :: ys) w
  ≡⟨ +-assoc (x =n w) (count xs w) (count (y :: ys) w) ⟩
    x =n w + (count xs w + count (y :: ys) w)
  ≡⟨ cong (x =n w +_) (merge-count w gas xs (y :: ys) <-gas) ⟩
    x =n w + count (merge gas xs (y :: ys)) w
  ≡⟨⟩
    count (x :: merge gas xs (y :: ys)) w
  ∎
... | (no _) | (yes _) =
  begin
    count (x :: xs) w + count (y :: ys) w
  ≡⟨⟩
    count (x :: xs) w + (y =n w + count ys w)
  ≡⟨ a+[b+c]≡b+[a+c] (count (x :: xs) w) (y =n w) (count ys w) ⟩
    y =n w + (count (x :: xs) w + count ys w)
  ≡⟨ cong (y =n w +_) (merge-count w gas (x :: xs) ys (norm-sm+sn≤o <-gas)) ⟩
    y =n w + count (merge gas (x :: xs) ys) w
  ≡⟨⟩
    count (y :: merge gas (x :: xs) ys) w
  ∎
... | (no _) | (no _) =
  begin
    count (x :: xs) w + count (y :: ys) w
  ≡⟨⟩
    x =n w + count xs w + (y =n w + count ys w)
  ≡⟨ a+b+[c+d]≡a+[c+[b+d]] (x =n w) (count xs w) (y =n w) (count ys w) ⟩
    x =n w + (y =n w + (count xs w + count ys w))
  ≡⟨ cong (λ z → x =n w + (y =n w + z)) (merge-count w gas xs ys (norm-sm+sn≤o-pred <-gas)) ⟩
    x =n w + (y =n w + count (merge gas xs ys) w)
  ≡⟨⟩
    count (x :: y :: merge gas xs ys) w
  ∎

merge-∈-⊎ : (w : ℕ) → (gas : ℕ) → (xs ys : List)
          → length xs + length ys < gas
          → w ∈ merge gas xs ys → (w ∈ xs) ⊎ (w ∈ ys)
merge-∈-⊎ w gas xs ys <-gas w∈zs = Data.Sum.map (count→∈ w xs) (count→∈ w ys) (0<m+n→⊎ c-xs+ys)
  where
    zs = merge gas xs ys
    c-xs+ys : 0 < count xs w + count ys w
    c-xs+ys rewrite merge-count w gas xs ys <-gas = ∈→count w zs w∈zs

merge-P : (P : ℕ → Set) → (gas : ℕ) → (xs ys : List)
        → length xs + length ys < gas
        → P-list P xs → P-list P ys → P-list P (merge gas xs ys)
merge-P P gas xs ys <-gas p-xs p-ys w w∈zs with merge-∈-⊎ w gas xs ys <-gas w∈zs
... | inj₁ w∈xs = p-xs w w∈xs
... | inj₂ w∈ys = p-ys w w∈ys

merge-≤ : (w : ℕ) → (gas : ℕ) → (xs ys : List)
        → length xs + length ys < gas
        → ≤-list w xs → ≤-list w ys → ≤-list w (merge gas xs ys)
merge-≤ w = merge-P (w ≤_)

data Sorted : List → Set where
  sorted-[] : Sorted []
  sorted-:: : (x : ℕ) → (xs : List) → ≤-list x xs → Sorted xs → Sorted (x :: xs)

≤-list-head : (x y : ℕ) → (ys : List) → x ≤ y → Sorted (y :: ys) → ≤-list x (y :: ys)
≤-list-head x y ys x≤y (sorted-:: _ _ y≤ys _) _ (here refl) = x≤y
≤-list-head x y ys x≤y (sorted-:: _ _ y≤ys _) z (there z∈ys) = ≤-trans x≤y (y≤ys z z∈ys)

merge-sorted : (gas : ℕ) → (xs ys : List)
             → length xs + length ys < gas
             → Sorted xs → Sorted ys → Sorted (merge gas xs ys)
merge-sorted zero _ _ () _ _
merge-sorted (suc gas) [] ys <-gas _ s-ys = s-ys
merge-sorted (suc gas) (x :: xs) [] <-gas s-xs _ = s-xs
merge-sorted (suc gas) (x :: xs) (y :: ys) (s≤s <-gas)
  s-x::xs@(sorted-:: _ _ x≤xs s-xs) s-y::ys@(sorted-:: _ _ y≤ys s-ys)
  with (x <? y) | (y <? x)
... | (yes x<y) | _ = sorted-:: x zs x≤zs s-zs
  where
    zs = merge gas xs (y :: ys)
    s-zs : Sorted zs
    s-zs = merge-sorted gas xs (y :: ys) <-gas s-xs s-y::ys
    x≤zs : ≤-list x zs
    x≤zs = merge-≤ x gas xs (y :: ys) <-gas x≤xs (≤-list-head x y ys (<→≤ x<y) s-y::ys)
... | (no _) | (yes y<x) = sorted-:: y zs y≤zs s-zs
  where
    <-gas' = norm-sm+sn≤o <-gas
    zs = merge gas (x :: xs) ys
    s-zs : Sorted zs
    s-zs = merge-sorted gas (x :: xs) ys <-gas' s-x::xs s-ys
    y≤zs : ≤-list y zs
    y≤zs = merge-≤ y gas (x :: xs) ys <-gas' (≤-list-head y x xs (<→≤ y<x) s-x::xs) y≤ys
... | (no ¬x<y) | (no ¬y<x) with ><-m≡n ¬x<y ¬y<x
-- Sorted (x :: x :: merge gas xs ys)
...    | refl = sorted-:: x (x :: zs) x≤x::zs s-x::zs
  where
    <-gas' = norm-sm+sn≤o-pred <-gas
    zs = merge gas xs ys
    s-zs : Sorted zs
    s-zs = merge-sorted gas xs ys <-gas' s-xs s-ys
    x≤zs : ≤-list x zs
    x≤zs = merge-≤ x gas xs ys <-gas' x≤xs y≤ys
    s-x::zs : Sorted (x :: zs)
    s-x::zs = sorted-:: x zs x≤zs s-zs
    x≤x::zs : ≤-list x (x :: zs)
    x≤x::zs = ≤-list-head x x zs ≤-refl s-x::zs

split : List → List × List
split [] = ([] , [])
split (x :: []) = (x :: [] , [])
split (x :: (y :: xs)) = x :: proj₁ s , y :: proj₂ s
  where
    s = split xs

-- ceil ((2 + m) / 2) < 2 + m
split-len-1-help : (x x1 : ℕ) → (xs : List) → length (proj₁ (split (x :: x1 :: xs))) < suc (suc (length xs))
split-len-1-help-≤ : (xs : List) → length (proj₁ (split xs)) ≤ length xs
split-len-1-help-≤ [] = z≤n
split-len-1-help-≤ (x :: []) = s≤s z≤n
split-len-1-help-≤ (x :: x1 :: xs) = <→≤ (split-len-1-help x x1 xs)
split-len-1-help x x1 xs = s≤s (s≤s (split-len-1-help-≤ xs))

split-len-2-help : (x x1 : ℕ) → (xs : List) → length (proj₂ (split (x :: x1 :: xs))) < suc (suc (length xs))
split-len-2-help-≤ : (xs : List) → length (proj₂ (split xs)) ≤ length xs
split-len-2-help-≤ [] = z≤n
split-len-2-help-≤ (x :: []) = z≤n
split-len-2-help-≤ (x :: x1 :: xs) = <→≤ (split-len-2-help x x1 xs)
split-len-2-help x x1 xs = s≤s (s≤s (split-len-2-help-≤ xs))

split-len-1 : (m x x1 : ℕ) → (xs : List) → suc (suc (length xs)) ≤ m → length (proj₁ (split (x :: x1 :: xs))) < m
split-len-1 m x x1 xs pre = ≤-trans (split-len-1-help x x1 xs) pre

split-len-2 : (m x x1 : ℕ) → (xs : List) → suc (suc (length xs)) ≤ m → length (proj₂ (split (x :: x1 :: xs))) < m
split-len-2 m x x1 xs pre = ≤-trans (split-len-2-help x x1 xs) pre

split-count : (w : ℕ) → (xs : List) → count xs w ≡ count (proj₁ (split xs)) w + count (proj₂ (split xs)) w
split-count w [] = refl
split-count w (x :: []) = sym (+-identityʳ ((x =n w) + 0))
split-count w (x :: y :: xs) =
  begin
    (x =n w) + ((y =n w) + count xs w)
  ≡⟨ cong (λ z → (x =n w) + ((y =n w) + z)) (split-count w xs) ⟩
    (x =n w) + ((y =n w) + (count (proj₁ (split xs)) w + count (proj₂ (split xs)) w))
  ≡⟨ sym (a+b+[c+d]≡a+[c+[b+d]] ((x =n w)) (count (proj₁ (split xs)) w) ((y =n w)) (count (proj₂ (split xs)) w) ) ⟩
    (x =n w) + count (proj₁ (split xs)) w + ((y =n w) + count (proj₂ (split xs)) w)
  ∎

split-len : (xs : List) → length xs ≡ length (proj₁ (split xs)) + length (proj₂ (split xs))
split-len xs = count→len-+ xs (proj₁ (split xs)) (proj₂ (split xs)) λ w → split-count w xs

sort-gas : ℕ → List → List
sort-gas zero _ = []
sort-gas (suc gas) [] = []
sort-gas (suc gas) (x :: []) = x :: []
sort-gas (suc gas) (x :: x1 :: xs) =
  merge (suc gas) (sort-gas gas (proj₁ s)) (sort-gas gas (proj₂ s))
  where
    s = split (x :: x1 :: xs)

sort-gas-count : (w gas : ℕ) → (xs : List)
               → length xs < gas
               → count xs w ≡ count (sort-gas gas xs) w
sort-gas-len : (gas : ℕ) → (xs : List)
             → length xs < gas
             → length xs ≡ length (sort-gas gas xs)
sort-gas-len gas xs <-gas = count→len xs (sort-gas gas xs) λ w → sort-gas-count w gas xs <-gas
sort-gas-count w zero xs ()
sort-gas-count w (suc gas) [] _ = refl
sort-gas-count w (suc gas) (x :: []) _ = refl
sort-gas-count w (suc gas) ys@(x :: x1 :: xs) (s≤s <-gas) =
  begin
    count ys w
  ≡⟨ split-count w ys ⟩
    count ys1 w + count ys2 w
  ≡⟨ cong (_+ count ys2 w) (sort-gas-count w gas ys1 <-gas-1) ⟩
    count zs1 w + count ys2 w
  ≡⟨ cong (count zs1 w +_) (sort-gas-count w gas ys2 <-gas-2) ⟩
    count zs1 w + count zs2 w
  ≡⟨ merge-count w (suc gas) zs1 zs2 <-gas-merge ⟩
    count (merge (suc gas) zs1 zs2) w
  ∎
  where
    ys1 = proj₁ (split ys)
    ys2 = proj₂ (split ys)
    zs1 = sort-gas gas ys1
    zs2 = sort-gas gas ys2
    <-gas-1 : length ys1 < gas
    <-gas-1 = split-len-1 gas x x1 xs <-gas
    <-gas-2 : length ys2 < gas
    <-gas-2 = split-len-2 gas x x1 xs <-gas
    <-gas-merge : length zs1 + length zs2 < suc gas
    <-gas-merge rewrite sym (sort-gas-len gas ys1 <-gas-1)
                      | sym (sort-gas-len gas ys2 <-gas-2)
                      | sym (split-len ys)
                      = s≤s <-gas

sort-gas-sorted : (gas : ℕ) → (xs : List)
                → length xs < gas
                → Sorted (sort-gas gas xs)
sort-gas-sorted zero xs ()
sort-gas-sorted (suc gas) [] _ = sorted-[]
sort-gas-sorted (suc gas) (x :: []) _ = sorted-:: x [] (≤-list-[] x) sorted-[]
sort-gas-sorted (suc gas) ys@(x :: x1 :: xs) (s≤s <-gas) =
  merge-sorted (suc gas) zs1 zs2 <-gas-merge s-zs1 s-zs2
  where
    ys1 = proj₁ (split ys)
    ys2 = proj₂ (split ys)
    zs1 = sort-gas gas ys1
    zs2 = sort-gas gas ys2
    <-gas-1 : length ys1 < gas
    <-gas-1 = split-len-1 gas x x1 xs <-gas
    <-gas-2 : length ys2 < gas
    <-gas-2 = split-len-2 gas x x1 xs <-gas
    <-gas-merge : length zs1 + length zs2 < suc gas
    <-gas-merge rewrite sym (sort-gas-len gas ys1 <-gas-1)
                      | sym (sort-gas-len gas ys2 <-gas-2)
                      | sym (split-len ys)
                      = s≤s <-gas
    s-zs1 = sort-gas-sorted gas ys1 <-gas-1
    s-zs2 = sort-gas-sorted gas ys2 <-gas-2

sort : List → List
sort xs = sort-gas (suc (length xs)) xs

sort-perm : (xs : List) → Perm xs (sort xs)
sort-perm xs w = sort-gas-count w (suc (length xs)) xs ≤-refl

sort-sorted : (xs : List) → Sorted (sort xs)
sort-sorted xs = sort-gas-sorted (suc (length xs)) xs ≤-refl

sort-ok : (xs : List) → Sorted (sort xs) × Perm xs (sort xs)
sort-ok xs = sort-sorted xs , sort-perm xs
