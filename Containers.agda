--{-# OPTIONS --inversion-max-depth=1000 #-}
open import Data.Product renaming (map₂ to map-π₂; map₁ to map-π₁)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin; zero; suc; toℕ; fromℕ<; reduce≥; #_)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟f_)

open import Data.Sum
open import Data.Empty

open import Function.Base
open import Function.Inverse using (_↔_; Inverse)
open import Function.Equality using (_⟨$⟩_) renaming (cong to pcong)
open import Function.LeftInverse using (LeftInverse)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality renaming ([_] to [_]i)
open import Relation.Binary.Core hiding (_⇒_)
open import Relation.Binary hiding (_⇒_)

instance
  auto≥ : ∀ {m n : ℕ} → {{_ : True (m ≥? n)}} → m ≥ n
  auto≥ {m} {n} {{c}} = toWitness c


-- A basic fact about division that is not yet in the stdlib.
/-mono-x : ∀ {a b c} → a < b * c → (c≢0 : False (c ≟ 0))
         → (a / c) {≢0 = c≢0} < b
/-mono-x {a}{b}{c} a<b*c c≢0 with <-cmp ((a / c) {≢0 = c≢0}) b
/-mono-x {a} {b} {c} a<b*c c≢0 | tri< l< _ _ = l<
/-mono-x {a} {b} {c} a<b*c c≢0 | tri≈ _ l≡ _ = let
     a<a/c*c = subst (a <_) (cong₂ _*_ (sym l≡) refl) a<b*c
     a/c*c≤a = m/n*n≤m a c {≢0 = c≢0}
     a<a = ≤-trans a<a/c*c a/c*c≤a
   in contradiction a<a (n≮n a)
/-mono-x {a} {b} {suc c} a<b*c c≢0 | tri> _ _ l> = let
     b*c<a/c*c = *-monoˡ-< c l>
     a/c*c≤a = m/n*n≤m a (suc c) {≢0 = c≢0}
     b*c≤a = ≤-trans b*c<a/c*c a/c*c≤a
     a<a = <-trans a<b*c b*c≤a
   in contradiction a<a (n≮n a)


n≢0⇒m%n<n : ∀ {m n} → (pf : n ≢ 0) → (m % n) {≢0 = fromWitnessFalse pf} < n
n≢0⇒m%n<n {n = zero} pf = contradiction refl pf
n≢0⇒m%n<n {m}{n = suc n} pf = m%n<n m n


-- Containers
record Con : Set₁ where
  constructor _◃_
  field
    Sh : Set
    Po : Sh → Set
  ⟦_⟧◃  : Set → Set
  ⟦_⟧◃ X = Σ Sh λ s → Po s → X
open Con public
infixr 1 _◃_

-- Container morphisms
record _⇒_ (C₁ C₂ : Con) : Set₁ where
  constructor _◃_
  field
    MSh : Sh C₁ → Sh C₂
    MPo : ∀ {a} → Po C₂ (MSh a) → Po C₁ a

  ⟪_⟫ : {X : Set} → ⟦ C₁ ⟧◃ X → ⟦ C₂ ⟧◃ X
  ⟪ s , γ ⟫ = MSh s , γ ∘ MPo
open _⇒_ public


-- Container linear? morphism
record _⊸_ (C₁ C₂ : Con) : Set₁ where
  constructor _◃_
  field
    MSh : Sh C₁ → Sh C₂
    MPo : ∀ {a} → Po C₂ (MSh a) ↔ Po C₁ a

  --⟪_⟫ : {X : Set} → ⟦ C₁ ⟧◃ X → ⟦ C₂ ⟧◃ X
  --⟪ s , γ ⟫ = MSh s , γ ∘ MPo
open _⊸_ public



-- Container operations
_⋄_ : Con → Con → Con
(S ◃ P) ⋄ (S₁ ◃ P₁) = ⟦ S ◃ P ⟧◃ S₁ ◃ λ { (s , γ) → (s₁ : P s) → P₁ (γ s₁) }

_∙_ : Con → Con → Con
(S ◃ P) ∙ (S₁ ◃ P₁) = ⟦ S ◃ P ⟧◃ S₁ ◃ λ { (s , γ) → Σ (P s) (P₁ ∘ γ) }

_⊗_ : Con → Con → Con
(S ◃ P) ⊗ (S₁ ◃ P₁) = S × S₁ ◃ λ { (s , s₁) → P s × P₁ s₁ }

_×c_ : Con → Con → Con
(S ◃ P) ×c (S₁ ◃ P₁) = S × S₁ ◃ λ { (s , s₁) → P s ⊎ P₁ s₁ }

magic-fin : ∀ {a}{X : Set a} → Fin 0 → X
magic-fin ()

--===== Preservation of ⇒ (ℕ ◃ Fin) under container operations =====--

-- XXX actually, we can decide at this point whether we do row major
-- flattening or column major.  Unfortunately ⇒ doesn't fix any of this,
-- it just tells us that there is a mapping, but there could be several
-- of them.

row-m₂ : ∀ {m n} → Fin (m * n) → Fin m × Fin n
row-m₂ {m} {zero}  i rewrite (*-comm m zero) = magic-fin i
row-m₂ {m} {suc n} i =
   -- i/n
   fromℕ< {n = m} (/-mono-x (toℕ<n i) tt) ,
   -- i % n
   fromℕ< {n = suc n} (m%n<n (toℕ i) n)


col-m₂ : ∀ {m n} → Fin (m * n) → Fin m × Fin n
col-m₂ {m} {n} o = let
    o′ = subst Fin (*-comm m n) o
    i′ , j′ = row-m₂ {m = n} {n = m} o′
  in j′ , i′


module test-rm/cm where
  m = 4
  n = 6
  o = 17
  o′ : Fin $ m * n
  o′ = fromℕ< {m = o} auto≥

  -- 17/6 = 2; 17%6 = 5
  -- if we treat 17 as row-major of shape [m,n]
  -- we should have 6*2 + 1*5 => 2,5
  test₁ : row-m₂ {m = m} {n = n} o′ ≡ (# 2 , # 5)
  test₁ = refl

  -- 17%4 = 1; 17/4 = 4
  -- if we treat 17 as column major of shape [m,n]
  -- we should have 1*1 + 4*4 => 1,4
  test₂ : col-m₂ {m = m} {n = n} o′ ≡ (# 1 , # 4)
  test₂ = refl

-- Container transformation to (ℕ ◃ Fin) is preserved under _⊗ (ℕ ◃ Fin)
morph-tensor-r : ∀ {C} → C ⇒ (ℕ ◃ Fin) → (C ⊗ (ℕ ◃ Fin)) ⇒ (ℕ ◃ Fin)
morph-tensor-r {A ◃ B} (s ◃ p) = (λ { (a , n) → s a * n}) ◃ map-π₁ p ∘ row-m₂

-- Container transformation to (ℕ ◃ Fin) is preserved under (ℕ ◃ Fin) ⊗_
morph-tensor-l : ∀ {C} → C ⇒ (ℕ ◃ Fin) → ((ℕ ◃ Fin) ⊗ C) ⇒ (ℕ ◃ Fin)
morph-tensor-l {A ◃ B} (s ◃ p) = (λ { (n , a) → n * s a }) ◃ map-π₂ p ∘ row-m₂


sum : ∀ {a}{A : Set a}{n} → (A → ℕ) → (Fin n → A) → ℕ
sum {n = zero}  s f = 0
sum {n = suc n} s f = s (f zero) + sum s (f ∘ suc)


morph-comp : ∀ {C} → C ⇒ (ℕ ◃ Fin) → ((ℕ ◃ Fin) ∙ C) ⇒ (ℕ ◃ Fin)
morph-comp {A ◃ B} (s ◃ p) = (λ { (n , γ) → sum s γ}) ◃ hlpr
  where
    hlpr : {n : ℕ}{γ : Fin n → A} →
           Fin (sum s γ) → Σ (Fin n) (B ∘ γ)
    hlpr {zero}{γ} ()
    hlpr {suc zero}{γ} f rewrite (+-identityʳ (s (γ zero))) = zero , p f
    hlpr {suc (suc n)}{γ} f with toℕ f ≥? s (γ zero)
    ... | yes pp = let
                     n' , γ' = hlpr {suc n}{γ ∘ suc} (reduce≥ f pp)
                   in suc n' , γ'
    ... | no ¬pp = zero , p (fromℕ< $ ≰⇒> ¬pp)


prod : (n : ℕ) → (Fin n → ℕ) → ℕ
prod zero γ = 1
prod (suc n) γ = γ zero * prod n (γ ∘ suc)

b≡0⇒a*b≡0 : ∀ {a b} → b ≡ 0 → a * b ≡ 0
b≡0⇒a*b≡0 {a} refl = *-zeroʳ a

-- XXX well, that's roughly what we do in morph-tensor
prod-conv : ∀ {n s} → Fin (prod n s) → ((i : Fin n) → Fin (s i))
prod-conv {suc n} {s} f i       with (prod n (s ∘ suc) ≟ 0)
prod-conv {suc n} {s} f i       | yes p =
     magic-fin (subst Fin (b≡0⇒a*b≡0 {a = s zero} p) f)
prod-conv {suc n} {s} f zero    | no ¬p =
     -- f / prod n (s ∘ suc)
     fromℕ< {n = s zero} (/-mono-x (toℕ<n f) (fromWitnessFalse ¬p))
prod-conv {suc n} {s} f (suc i) | no ¬p =
     -- prod-conv (f % prod n (s ∘ suc)) i
     prod-conv (fromℕ< (n≢0⇒m%n<n {m = toℕ f} ¬p)) i


-- XXX the same ⇒ (ℕ ◃ Fin) preserving function for ⋄
-- Can't really prove this: it seems that C ⇒ (ℕ ◃ Fin) is not strong enough.
-- Probably we need ⇔ instead...
--morph-diamond- : ∀ {C} → C ⇒ (ℕ ◃ Fin) → (C ⋄ (ℕ ◃ Fin)) ⇒ (ℕ ◃ Fin)
--morph-diamond- {A ◃ B} (s ◃ p) = (λ { (a , γ) → prod (s a) (γ ∘ p) }) ◃ hlpr
--  where
--    hlpr : {a : Σ A (λ s → B s → ℕ)} →
--           let a , γ = a in Fin (prod (s a) (γ ∘ p)) → (s : B a) → Fin (γ s)
--    hlpr {a , γ} f = {!prod-conv {n = s a} {s = γ ∘ p} f!}


morph-diamond-r : ∀ {C} → C ⊸ (ℕ ◃ Fin) → (C ⋄ (ℕ ◃ Fin)) ⇒ (ℕ ◃ Fin)
morph-diamond-r {A ◃ B} (s ◃ p) =
    (λ { (a , γ) → prod (s a) (γ ∘ (_⟨$⟩_ (Inverse.to p))) }) ◃ hlpr
  where
    hlpr : {a : Σ A (λ s → B s → ℕ)} →
           let a , γ = a in Fin (prod (s a) (γ ∘ (_⟨$⟩_ (Inverse.to p)))) → (s : B a) → Fin (γ s)
    hlpr {a , γ} f b = let
        o = Inverse.from p ⟨$⟩ b
        f′ = prod-conv f o
        q = subst (Fin ∘ γ) (LeftInverse.left-inverse-of (Inverse.right-inverse p) b) f′
      in q


-- Can do this on the left though.
morph-diamond-l : ∀ {C} → C ⇒ (ℕ ◃ Fin) → ((ℕ ◃ Fin) ⋄ C) ⇒ (ℕ ◃ Fin)
morph-diamond-l {A ◃ B} (s ◃ p) = (λ { (n , γ) → prod n (s ∘ γ) }) ◃ λ f → p ∘ prod-conv f -- hlpr
  where
    hlpr : {a : Σ ℕ (λ n → Fin n → A)} →
           let n , γ = a in Fin (prod n (s ∘ γ)) →
           (i : Fin n) → B (γ i)
    hlpr {n , γ} f = p ∘ prod-conv  f


-- (ℕ ◃ Fin) ⋄ C is an n-fold tensor product of C
-- XXX why this is non-terminating?
--n-fold : ∀ {X} → ⟦ ℕ ◃ Fin ⟧◃ X → (id : X) → (X → X → X) → X
--n-fold (zero  , f) id _⊕_ = id
--n-fold (suc n , f) id _⊕_ = f zero ⊕ curry n-fold n (f ∘ suc) id _⊕_

n-fold-curry : ∀ {a}{X : Set a} n → (Fin n → X) → X → (X → X → X) → X
n-fold-curry zero f id _⊕_ = id
n-fold-curry (suc n) f id _⊕_ = f zero ⊕ n-fold-curry n (f ∘ suc) id _⊕_

n-fold' : ∀ {X} → ⟦ ℕ ◃ Fin ⟧◃ X → (id : X) → (X → X → X) → X
n-fold' (n , f) id _⊕_ = n-fold-curry n f id _⊕_


𝟘 : Con
𝟘 = ⊥ ◃ λ ()

𝟘-map-l : 𝟘 ⇒ (ℕ ◃ Fin)
𝟘-map-l = (const 0) ◃ λ ()

-- 1 container
𝟙 : Con
𝟙 = ⊤ ◃ const ⊤

-- We can make a "view" of the 𝟙 container as an n-element
-- ℕ ◃ Fin container.
𝟙-map-l : ∀ n → 𝟙 ⇒ (ℕ ◃ Fin)
𝟙-map-l n = (const n) ◃ (const tt)

-- Well, only non-empty vectors can be mapped to 𝟙
𝟙-map-r : (ℕ ◃ (Fin ∘ suc)) ⇒ 𝟙
𝟙-map-r = (const tt) ◃ const zero

-- n-fold tensor product of a container
⨂ : ℕ → Con → Con
⨂ n C = n-fold-curry n (const C) 𝟙 _⊗_

⨂-sh : ∀ {A B n} → (Fin n → A) → Sh $ ⨂ n (A ◃ B)
⨂-sh {n = zero} f = tt
⨂-sh {n = suc n} f = f zero , ⨂-sh (f ∘ suc)

⨂-po : ∀ {A B n γ} → Po (⨂ n (A ◃ B)) (⨂-sh γ) → ((i : Fin n) → B (γ i))
⨂-po {n = zero}  f         = λ i → magic-fin i
⨂-po {n = suc n} (γ₀ , γₛ) = λ {zero → γ₀ ; (suc i) → ⨂-po γₛ i}

-- Definition of diamond via n-fold ⊗ operation (for (ℕ ◃ Fin) on the right).
-- XXX well, actually we want to show that they are isomorphic
⋄-⨂ : ∀ {C X} → (c : ⟦ (ℕ ◃ Fin) ⋄ C ⟧◃ X) → ⟦ ⨂ (proj₁ $ proj₁ c) C ⟧◃ X
⋄-⨂ {A ◃ B} ((n , γ) , δ) = (⨂-sh γ) , δ ∘ ⨂-po


-- Left identity
⋄-left-id : ∀ {C X} → ⟦ 𝟙 ⋄ C ⟧◃ X → ⟦ C ⟧◃ X
⋄-left-id {A ◃ B} ((t , γ) , q) = γ t , λ x → q λ {tt → x}


-- Just picks one element from X (γ is useless, as it has type B a → ⊤)
-- XXX not sure this should be called terminal
⋄-right-terminal : ∀ {C X} → ⟦ C ⋄ 𝟙 ⟧◃ X → Sh C × X
⋄-right-terminal {A ◃ B} ((a , γ) , q) = a , q (const tt)


-- Distributivity of ×c and ⊗
-- XXX actually, this is an isomorphism
⋄-distribʳ : ∀ {A B C X} → ⟦ (A ×c B) ⋄ C ⟧◃ X → ⟦ (A ⋄ C) ⊗ (B ⋄ C) ⟧◃ X
⋄-distribʳ {As ◃ Ap} {Bs ◃ Bp} {Cs ◃ Cp} (((as , bs) , ap+bp⇒cs) , γ) =
  ((as , (λ ap → ap+bp⇒cs (inj₁ ap))) ,
    bs , (λ bp → ap+bp⇒cs (inj₂ bp))) ,
  λ where
      (ap⇒cp , bp⇒cp) → γ λ where
                              (inj₁ ap) → ap⇒cp ap
                              (inj₂ bp) → bp⇒cp bp


--==== Iterated ⋄ applications ====--

-- apply _⋄ (ℕ ◃ Fin) n times on the right
R : ℕ → Con → Con
R zero    c = c
R (suc x) c = (R x c) ⋄ (ℕ ◃ Fin)

-- apply (ℕ ◃ Fin) ⋄_ n times on the left
L : ℕ → Con → Con
L zero    c = c
L (suc x) c = (ℕ ◃ Fin) ⋄ (L x c)

-- We can clearly define A operator (from arrays with levels)
-- using R as follows.
A : ℕ → Con
A n = R n 𝟙


-- Now, we'd like to define functions L and R that also
-- maintain the morphism into (ℕ ◃ Fin)
L' : (n : ℕ) → (c : Con) → (mc : c ⇒ (ℕ ◃ Fin)) → Σ Con λ c' → (c' ⇒ (ℕ ◃ Fin))
L' zero    c m = c , m
L' (suc n) c m = let
    c' , m' = L' n c m
    c'' = (ℕ ◃ Fin) ⋄ c'
    m'' = morph-diamond-l m'
  in c'' , m''


-- Well, these guys have a shape ℕ × ℕ, but only store a single element...
--L1 = proj₁ $ L' 2 𝟙 (const 1 ◃ const tt)
--M1 = proj₂ $ L' 2 𝟙 (const 1 ◃ const tt)

-- That's our regular multi-dimensional array
L2 = proj₁ $ L' 1 (ℕ ◃ Fin) (id ◃ id)
M2 = proj₂ $ L' 1 (ℕ ◃ Fin) (id ◃ id)

L3 = proj₁ $ L' 2 (ℕ ◃ Fin) (id ◃ id)
M3 = proj₂ $ L' 2 (ℕ ◃ Fin) (id ◃ id)

-- Which means that if I have a function that goes from ... → L2 X
-- I can translate its result into (ℕ ◃ Fin) X by applying M2
flat3 : ∀ {X} → ⟦ L3 ⟧◃ X → ⟦ ℕ ◃ Fin ⟧◃ X
flat3 = ⟪ M3 ⟫




--===== Just a few tests =====--

-- This is level-3 array with 2d irregular shape, e.g.
--
--     / . .     \
-- s = | . . . . |   , so why don't we increment elements with
--     \ .       /     index zero at the last position.
--
test : ⟦ L3 ⟧◃ ℕ → ⟦ L3 ⟧◃ ℕ
test (sh@(zero  , s) , γ) = sh , suc ∘ γ
test (sh@(suc n , s) , γ) = sh , inc
  where inc : _
        inc f with fromℕ< $ n<1+n n
        inc f | `n with (s `n) | f `n
        inc f | `n | zero , δ  | f`n = γ f
        inc f | `n | suc m , δ | f`n with fromℕ< $ n<1+n m
        inc f | `n | suc m , δ | f`n | `m with (δ `m) | (f`n `m)
        inc f | `n | suc m , δ | f`n | `m | suc δ`m | zero = γ f
        inc f | `n | suc m , δ | f`n | `m | suc δ`m | suc f`n`m = γ f + 1


test-flat : ⟦ L3 ⟧◃ ℕ → ⟦ ℕ ◃ Fin ⟧◃ ℕ
test-flat = flat3 ∘ test

open import Data.Vec
cont-tabulate : ∀ {X} → (c : ⟦ ℕ ◃ Fin ⟧◃ X) → Vec X (proj₁ c)
cont-tabulate (n , s) = tabulate s

sh3 : Sh L3
sh3 = 3 , (lookup ((1 , lookup [ 1 ]) ∷
                   (2 , lookup (2 ∷ [ 3 ])) ∷
                   (2 , lookup (2 ∷ [ 2 ])) ∷ []))

ex3 : ⟦ L3 ⟧◃ ℕ
ex3 = sh3 , const 0

-- We should see now that every n-th element is changed.
test-ex3 = cont-tabulate $ test-flat ex3
