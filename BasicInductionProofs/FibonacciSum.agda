module FibonacciSum where

import Data.Nat
open Data.Nat using (ℕ; suc; zero; _+_; _*_; pred; _≤_; z≤n; s≤s)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

+-id-r : ∀{n : ℕ} -> n + zero ≡ n
+-id-r {zero} = refl
+-id-r {suc n} = cong suc +-id-r

suc-lemma : ∀{n m : ℕ} -> suc (n + m) ≡ n + suc m
suc-lemma {zero} {m} = refl
suc-lemma {suc n} {m} =
  begin
    suc ((suc n) + m)
  ≡⟨ cong suc refl ⟩
    suc (suc (n + m))
  ≡⟨ cong suc suc-lemma ⟩
    suc (n + (suc m))
  ≡⟨⟩
    suc n + suc m
  ∎

+-comm : ∀ {n m : ℕ} -> n + m ≡ m + n
+-comm {zero} {m} =
  begin
    zero + m
  ≡⟨⟩
    m
  ≡⟨ sym +-id-r ⟩
    m + zero
  ∎
+-comm {suc n} {m} =
  begin
    suc n + m
  ≡⟨⟩
    suc (n + m)
  ≡⟨ cong suc (+-comm {n} {m}) ⟩
    suc (m + n)
  ≡⟨ suc-lemma ⟩
    m + suc n
  ∎


pred-suc-lemma : ∀ {n : ℕ} -> pred (suc n) ≡ n
pred-suc-lemma = refl

pred-lemma : ∀{n m : ℕ} -> (1 ≤ m)  -> pred (n + m) ≡ n + pred m
pred-lemma {n} {zero} ()
pred-lemma {n} {suc m} p =
  begin
    pred (n + suc m)
  ≡⟨ cong pred (sym (suc-lemma {n} {m})) ⟩
    pred (suc (n + m))
  ≡⟨ pred-suc-lemma ⟩
    n + m
  ≡⟨ cong (_+_ n) (sym pred-suc-lemma) ⟩
    n + (pred (suc m))
  ∎

-- More standard library affair
≤-trans : ∀ {n m l : ℕ} -> n ≤ m -> m ≤ l -> n ≤ l
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-symm : ∀ {n : ℕ} -> n ≤ n
≤-symm {zero} = z≤n
≤-symm {suc n} = s≤s ≤-symm

≤-suc : ∀ {n : ℕ} -> n ≤ suc n
≤-suc {zero} = z≤n
≤-suc {suc n} = s≤s ≤-suc

≤-l-+ : ∀ {n m l : ℕ} -> n ≤ m -> l + n ≤ (l + m)
≤-l-+ {n} {m} {zero} p = p 
≤-l-+ {n} {m} {suc l} p = s≤s (≤-l-+ p)

≤-r-+ : ∀{n m l : ℕ} -> n ≤ m -> (n + l) ≤ (m + l)
≤-r-+ {n} {m} {l} p rewrite +-comm {n} {l} | +-comm {m} {l} = ≤-l-+ p

fib : ℕ -> ℕ
fib 0 = 1
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib-mono-lemma : ∀ {n} -> fib n ≤ fib (suc n)
fib-mono-lemma {zero} = s≤s z≤n
fib-mono-lemma {suc zero} = s≤s z≤n
fib-mono-lemma {suc (suc n)} with fib-mono-lemma {n} | fib-mono-lemma {suc n}
... |                             p                  |  q 
    = ≤-trans ((≤-l-+ {_} {_} {fib n} q)) ((≤-r-+ {_} {_} {fib (suc (suc n))} p))


pos-fib-lemma : ∀ {n : ℕ} -> 1 ≤ fib n
pos-fib-lemma {zero} = s≤s z≤n
pos-fib-lemma {suc n} with pos-fib-lemma {n} 
... |                      p = ≤-trans p (fib-mono-lemma {n})
    

sumFib : ℕ -> ℕ
sumFib zero = fib (zero)
sumFib (suc n) = fib (suc n) + sumFib n


sumFibProp : ∀{n : ℕ} -> sumFib n ≡ pred (fib (suc (suc n)))
sumFibProp {zero} = refl
sumFibProp {suc n} =
  begin
    sumFib (suc n)
  ≡⟨⟩
    fib (suc n) + sumFib n
  ≡⟨ cong (_+_ (fib (suc n))) (sumFibProp {n}) ⟩
    fib (suc n) + pred (fib (suc (suc n)))
  ≡⟨ sym (pred-lemma {fib (suc n)} {fib (suc (suc n))} (pos-fib-lemma {suc (suc n)}) ) ⟩
    pred (fib (suc n) + (fib (suc (suc n))))
  ≡⟨ refl ⟩
    pred (fib (suc (suc (suc n))))
  ∎
