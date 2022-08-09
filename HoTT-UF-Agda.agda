{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}
module HoTT-UF-Agda where
open import Universes public

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇ where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → (𝟙 → B)
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙' : (X : 𝓤 ̇) → X → 𝟙
!𝟙' X x = ⋆

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆

data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (A : 𝓤 ̇) → 𝟘 → A
𝟘-recursion A a = 𝟘-induction (λ _ → A) a

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ -> 𝓤 ̇
¬ X = X → 𝟘

data ℕ : 𝓤₀ ̇ where
 zero : ℕ
 succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h
 where
  h : (n : ℕ) → A n
  h 0         = a₀
  h (succ n)  = f n (h n)

{- when A is not dependently typed -}

ℕ-recursion : (X : 𝓤 ̇)
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇)
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)

module Arithmetic where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + 0 = x
  x + succ y = succ (x + y)
  x × 0 = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_

module Arithmetic' where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + y = ℕ-recursion ℕ x (λ _ z → succ z) y
  -- x + y = h y
  --  where
  --   h : ℕ → ℕ
  --   h = ℕ-iteration ℕ x succ
  
  x × y = h y
   where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_

module ℕ-order where

 _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇
 0 ≤ y = 𝟙
 succ x ≤ 0 = 𝟘
 succ x ≤ succ y = x ≤ y

 x ≥ y = y ≤ x

 infix 10 _≤_
 infix 10 _≥_

{- Exercise -}
module ℕ-order' where

 _≤_ : ℕ → ℕ → 𝓤₀ ̇
 _≤_ = ℕ-iteration (ℕ → 𝓤₀ ̇) (λ _ → 𝟙) (λ f → ℕ-recursion (𝓤₀ ̇) 𝟘 (λ n _ → f n))
  -- where
  --  h : ℕ → ℕ → 𝓤₀ ̇
  --  h x y = ℕ-recursion (𝓤₀ ̇ ) 𝟙 (λ x' _ → i (succ x') y) x
  --  where
  --   i : ℕ → ℕ → 𝓤₀ ̇
  --   i x y = ℕ-recursion 𝓤₀ ̇  𝟘 (λ y' _ → h x y') y

data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
 inl : X → X + Y
 inr : Y → X + Y

+-induction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : X + Y → 𝓦 ̇)
            → ((x : X) → A (inl x))
            → ((y : Y) → A (inr y))
            → (z : X + Y) → A z

+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ } → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-induction' : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction' A a₀ a₁ = +-induction A
                         (𝟙-induction (λ (x : 𝟙) → A (inl x)) a₀)
                         (𝟙-induction (λ (y : 𝟙) → A (inr y)) a₁)

record Σ {𝓤 𝓥} {X : 𝓤 ̇ } (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
   _,_
  field
   x : X
   y : Y x

-- pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
-- pr₁ (x , y) = x

pr₁ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → Σ Y → X
pr₁ (x , y) = x
pr₂ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

syntax -Σ X (λ x → y) = Σ x ∶ X , y

Σ-induction : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
            → ((x : X) (y : Y x) → A (x , y))
            → ((x , y) : Σ Y) → A (x , y)
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } {A : Σ Y → 𝓦 ̇ }
      → (((x , y) : Σ Y) → A (x , y))
      → ((x : X) → (y : Y x) → A (x , y))
curry f x y = f (x , y)

_×_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ∶ X , Y

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (Y : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

syntax -Π A (λ x → b) = Π x ∶ A , b

id : {X : 𝓤 ̇ } → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇ ) → X → X
𝑖𝑑 X = id

_∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : Y → 𝓦 ̇ }
    → ((y : Y) → Z y)
    → (f : X → Y)
    → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

domain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y

type-of : {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

data Id {𝓤} (X : 𝓤 ̇ ) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

_≡_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≡ y = Id _ x y

𝕁 : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
  → ((x : X) → A x x (refl x))
  → (x y : X) (p : x ≡ y) → A x y p
𝕁 X A f x x (refl x) = f x

ℍ : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
  → B x (refl x)
  → (y : X) (p : x ≡ y) → B y p
ℍ x B b x (refl x) = b

𝕁' : (X : 𝓤 ̇ ) (A : (x y : X) → (p : x ≡ y) → 𝓥 ̇ )
   → ((x : X) → A x x (refl x))
   → (x y : X) (p : x ≡ y) → A x y p
𝕁' X A f x = ℍ x (A x) (f x)

𝕁s-agreement : (X : 𝓤 ̇ ) (A : (x y : X) → x ≡ y → 𝓥 ̇ )
               (f : (x : X) → A x x (refl x)) (x y : X) (p : x ≡ y)
             → 𝕁 X A f x y p ≡ 𝕁' X A f x y p
𝕁s-agreement X A f x x (refl x) = refl (f x)

-- ℍ' : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇ )
--    → B x (refl x)
--    → (y : X) (p : x ≡ y) → B y p
-- ℍ' {X} x B b y = 𝕁 X (λ _ → B)

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport A (refl x) = id

transport𝕁 : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X}
          → x ≡ y → A x → A y
transport𝕁 {𝓤} {𝓥} {X} A {x} {y} = 𝕁 X (λ x y _ → A x → A y) (λ x → id) x y

lhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
lhs {𝓤} {X} {x} {y} p = x

rhs : {X : 𝓤 ̇ } {x y : X} → x ≡ y → X
rhs {𝓤} {X} {x} {y} p = y

_∙_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
-- (refl x) ∙ p = p
p ∙ q = transport (lhs p ≡_) q p

_≡⟨_⟩_ : {X : 𝓤 ̇ } (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

_∎ : {X : 𝓤 ̇ } (x : X) → x ≡ x
x ∎ = refl x

_⁻¹ : {X : 𝓤 ̇ } → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (_≡ lhs p) p (refl (lhs p))

_∙'_ : {X : 𝓤 ̇ } {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙' q = transport (_≡ rhs q) (p ⁻¹) q


∙agreement : {X : 𝓤 ̇ } {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → (p ∙' q) ≡ (p ∙ q)
∙agreement (refl x) (refl x) = refl (refl x)

rdnel : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
      → (p ∙ (refl y)) ≡ p
rdnel p = refl p

rdner : {X : 𝓤 ̇ } {y z : X} (q : y ≡ z)
      → ((refl y)  ∙' q) ≡ q
rdner q = refl q

rdnel' : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
       → (p ∙' (refl y)) ≡ p
rdnel' (refl x) = refl (refl x)

-- ^ depends on which side is transported.

ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f {x} {x'} p = transport (λ - → f x ≡ f -) p (refl (f x))

_~_ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } → Π A → Π A → 𝓤 ⊔ 𝓥 ̇
f ~ g = ∀ x → f x ≡ g x

¬¬ ¬¬¬ : 𝓤 ̇ → 𝓤 ̇
¬¬ A = ¬(¬ A)
¬¬¬ A = ¬(¬¬ A)

dni : (A : 𝓤 ̇ ) → A → ¬¬ A
dni A a u = u a

contrapositive : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (¬ B → ¬ A)
contrapositive f v a = v (f a)

tno : (A : 𝓤 ̇ ) → ¬¬¬ A → ¬ A
tno A = contrapositive (dni A)

_⇔_ : 𝓤 ̇  → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇
X ⇔ Y = (X → Y) × (Y → X)

lr-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (X → Y)
lr-implication = pr₁

rl-implication : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X ⇔ Y) → (Y → X)
rl-implication = pr₂

absurdity³-is-absurdity : {A : 𝓤 ̇ } → ¬¬¬ A ⇔ ¬ A
absurdity³-is-absurdity {𝓤} {A} = firstly , secondly
 where
  firstly : ¬¬¬ A → ¬ A
  firstly = tno A
  secondly : ¬ A → ¬¬¬ A
  secondly = dni (¬ A)

_≢_ : {X : 𝓤 ̇ } → X → X → 𝓤 ̇
x ≢ y = ¬(x ≡ y)

≢-sym : {X : 𝓤 ̇ } {x y : X} → x ≢ y → y ≢ x
≢-sym {𝓤} {X} {x} {y} u = λ (p : y ≡ x) → u (p ⁻¹)

Id→Fun : {X Y : 𝓤 ̇ } → X ≡ Y → X → Y
Id→Fun {𝓤} = transport id

𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = Id→Fun p ⋆

₁-is-not-₀ : ₁ ≢ ₀
₁-is-not-₀ p = 𝟙-is-not-𝟘 q
 where
  f : 𝟚 → 𝓤₀ ̇
  f ₀ = 𝟘
  f ₁ = 𝟙
  q : 𝟙 ≡ 𝟘
  q = ap f p

₁-is-not-₀[not-an-MLTT-proof] : ¬(₁ ≡ ₀)
₁-is-not-₀[not-an-MLTT-proof] ()

decidable : 𝓤 ̇ → 𝓤 ̇
decidable A = A + ¬ A

has-decidable-equality : 𝓤 ̇ → 𝓤 ̇
has-decidable-equality X = (x y : X) → decidable (x ≡ y)

𝟚-has-decidable-equality : has-decidable-equality 𝟚
𝟚-has-decidable-equality ₀ ₀ = inl (refl _)
𝟚-has-decidable-equality ₀ ₁ = inr (≢-sym ₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₀ = inr (₁-is-not-₀)
𝟚-has-decidable-equality ₁ ₁ = inl (refl _)

not-zero-is-one : (n : 𝟚) → n ≢ ₀ → n ≡ ₁
not-zero-is-one ₀ f = !𝟘 (₀ ≡ ₁) (f (refl ₀))
not-zero-is-one ₁ f = refl _

inl-inr-disjoint-images : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {x : X} {y : Y} → inl x ≢ inr y
inl-inr-disjoint-images {𝓤} {𝓥} {X} {Y} p = 𝟙-is-not-𝟘 q
 where
 f : X + Y → 𝓤₀ ̇
 f (inl x) = 𝟙
 f (inr y) = 𝟘
 q : 𝟙 ≡ 𝟘
 q = ap f p

right-fails-gives-left-holds : {P : 𝓤 ̇ } {Q : 𝓥 ̇ } → P + Q → ¬ Q → P
right-fails-gives-left-holds (inl p) u = p
right-fails-gives-left-holds (inr q) u = !𝟘 _ (u q)

positive-not-zero : (x : ℕ) → succ x ≢ 0
positive-not-zero x p = 𝟙-is-not-𝟘 (g p)
 where
  f : ℕ → 𝓤₀ ̇
  f 0        = 𝟘
  f (succ x) = 𝟙
  g : succ x ≡ 0 → 𝟙 ≡ 𝟘
  g = ap f

pred : ℕ → ℕ
pred 0        = 0
pred (succ n) = n

succ-lc : {x y : ℕ} → succ x ≡ succ y → x ≡ y
succ-lc = ap pred

ℕ-has-decidable-equality : has-decidable-equality ℕ
ℕ-has-decidable-equality 0 0               = inl (refl 0)
ℕ-has-decidable-equality 0 (succ y)        = inr (≢-sym (positive-not-zero y))
ℕ-has-decidable-equality (succ x) 0        = inr (positive-not-zero x)
ℕ-has-decidable-equality (succ x) (succ y) = f (ℕ-has-decidable-equality x y)
 where
  f : decidable (x ≡ y) → decidable (succ x ≡ succ y)
  f (inl p) = inl (ap succ p)
  f (inr k) = inr (λ (s : succ x ≡ succ y) → k (succ-lc s))

is-singleton : 𝓤 ̇  → 𝓤 ̇
is-singleton X = Σ c ∶ X , ((x : X) → c ≡ x)

is-center : (X : 𝓤 ̇ ) → X → 𝓤 ̇
is-center X c = (x : X) → c ≡ x

𝟙-is-singleton : is-singleton 𝟙
𝟙-is-singleton = ⋆ , 𝟙-induction (λ x → ⋆ ≡ x) (refl _)

center : (X : 𝓤 ̇ ) → is-singleton X → X
center X (c , ϕ) = c

centrality : (X : 𝓤 ̇ ) (i : is-singleton X) (x : X) → center X i ≡ x
centrality X (c , φ) = φ

is-subsingleton : 𝓤 ̇ → 𝓤 ̇
is-subsingleton X = (x y : X) → x ≡ y

𝟘-is-subsingleton : is-subsingleton 𝟘
𝟘-is-subsingleton x y = !𝟘 (x ≡ y) x

singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
-- singletons-are-subsingletons X (c , ϕ) = λ x y → ((ϕ x) ⁻¹) ∙ (ϕ y)
singletons-are-subsingletons X (c , φ) x y = x ≡⟨ (φ x)⁻¹ ⟩
                                             c ≡⟨ φ y     ⟩
                                             y ∎

𝟙-is-subsingleton : is-subsingleton 𝟙
𝟙-is-subsingleton = singletons-are-subsingletons 𝟙 𝟙-is-singleton

pointed-subsingletons-are-singletons : (X : 𝓤 ̇ )
                                     → X → is-subsingleton X → is-singleton X
pointed-subsingletons-are-singletons X x s = x , s x

singleton-iff-pointed-and-subsingleton : {X : 𝓤 ̇ } → is-singleton X ⇔ (X × is-subsingleton X)
singleton-iff-pointed-and-subsingleton {𝓤} {X} = a , b
 where
  a : is-singleton X → X × is-subsingleton X
  a s = (center X s , singletons-are-subsingletons X s)
  b : X × is-subsingleton X → is-singleton X
  b (x , t) = pointed-subsingletons-are-singletons X x t

is-prop is-truth-value : 𝓤 ̇  → 𝓤 ̇
is-prop = is-subsingleton
is-truth-value = is-subsingleton

is-set : 𝓤 ̇  → 𝓤 ̇
is-set X = (x y : X) → is-prop (x ≡ y)

EM EM' : ∀ 𝓤 → 𝓤 ⁺ ̇
EM 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → X + ¬ X
EM' 𝓤 = (X : 𝓤 ̇ ) → is-subsingleton X → is-singleton X + is-empty X

EM-gives-EM' : EM 𝓤 → EM' 𝓤
EM-gives-EM' em X s = γ (em X s)
 where
  γ : X + ¬ X → is-singleton X + is-empty X
  γ (inl x) = inl (pointed-subsingletons-are-singletons X x s)
  γ (inr x) = inr x

EM'-gives-EM : EM' 𝓤 → EM 𝓤
EM'-gives-EM em' X s = γ (em' X s)
 where
  γ : is-singleton X + is-empty X → X + ¬ X
  γ (inl i) = inl (center X i)
  γ (inr x) = inr x

no-unicorns : ¬(Σ X ∶ 𝓤 ̇  , is-subsingleton X × ¬(is-singleton X) × ¬(is-empty X))
no-unicorns (X , i , f , g) = c
 where
  e : is-empty X
  e x = f (pointed-subsingletons-are-singletons X x i)
  c : 𝟘
  c = g e

¬+→¬× : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ¬(X + Y) → (¬ X × ¬ Y)
¬+→¬× {𝓤} {𝓥} {X} {Y} f = (a , b)
 where
  a : ¬ X
  a x = f (inl x)
  b : ¬ Y
  b y = f (inr y)

negnegEM' : {X : 𝓤 ̇ } → is-subsingleton X → ¬¬(is-singleton X + is-empty X)
negnegEM' {𝓤} {X} i f = no-unicorns (X , i , a , b)
 where
  c : ¬(is-singleton X) × ¬(is-empty X)
  c = ¬+→¬× f
  a : ¬(is-singleton X)
  a = pr₁ c
  b : ¬(is-empty X)
  b = pr₂ c

module magmas where
 Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Magma 𝓤 = Σ X ∶ 𝓤 ̇ , is-set X × (X → X → X)
 ⟨_⟩ : Magma 𝓤 → 𝓤 ̇
 ⟨ X , i , _·_ ⟩ = X

 magma-is-set : (M : Magma 𝓤) → is-set ⟨ M ⟩
 magma-is-set (X , i , _·_) = i

 magma-operation : (M : Magma 𝓤) → ⟨ M ⟩ → ⟨ M ⟩ → ⟨ M ⟩
 magma-operation (X , i , _·_) = _·_

 syntax magma-operation M x y = x ·⟨ M ⟩ y

 is-magma-hom : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-hom M N f = (x y : ⟨ M ⟩) → f (x ·⟨ M ⟩ y) ≡ f x ·⟨ N ⟩ f y

 id-is-magma-hom : (M : Magma 𝓤) → is-magma-hom M M (𝑖𝑑 ⟨ M ⟩)
 id-is-magma-hom M = λ (x y : ⟨ M ⟩) → refl (x ·⟨ M ⟩ y)

 is-magma-iso : (M N : Magma 𝓤) → (⟨ M ⟩ → ⟨ N ⟩) → 𝓤 ̇
 is-magma-iso M N f = is-magma-hom M N f
                    × (Σ g ∶ (⟨ N ⟩ → ⟨ M ⟩), is-magma-hom N M g
                                            × (g ∘ f ~ 𝑖𝑑 ⟨ M ⟩)
                                            × (f ∘ g ~ 𝑖𝑑 ⟨ N ⟩))

 id-is-magma-iso : (M : Magma 𝓤) → is-magma-iso M M (𝑖𝑑 ⟨ M ⟩)
 id-is-magma-iso M = id-is-magma-hom M ,
                     𝑖𝑑 ⟨ M ⟩ ,
                     id-is-magma-hom M ,
                     refl ,
                     refl
 
 Id→iso : {M N : Magma 𝓤} → M ≡ N → ⟨ M ⟩ → ⟨ N ⟩
 Id→iso p = transport ⟨_⟩ p

 Id→iso-is-iso : {M N : Magma 𝓤} (p : M ≡ N) → is-magma-iso M N (Id→iso p)
 Id→iso-is-iso (refl M) = id-is-magma-iso M

 _≅ₘ_ : Magma 𝓤 → Magma 𝓤 → 𝓤 ̇
 M ≅ₘ N = Σ f ∶ (⟨ M ⟩ → ⟨ N ⟩), is-magma-iso M N f

 magma-Id→iso : {M N : Magma 𝓤} → M ≡ N → M ≅ₘ N
 magma-Id→iso p = (Id→iso p , Id→iso-is-iso p)

 ∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
 ∞-Magma 𝓤 = Σ X ∶ 𝓤 ̇ , (X → X → X)

module monoids where

 left-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
 left-neutral e _·_ = ∀ x → e · x ≡ x

 right-neutral : {X : 𝓤 ̇ } → X → (X → X → X) → 𝓤 ̇
 right-neutral e _·_ = ∀ x → x · e ≡ x

 associative : {X : 𝓤 ̇ } → (X → X → X) → 𝓤 ̇
 associative _·_ = ∀ x y z → (x · y) · z ≡ x · (y · z)

 Monoid : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Monoid 𝓤 = Σ X ∶ 𝓤  ̇ , is-set X
                      × (Σ · ∶ (X → X → X) , (Σ e ∶ X , (left-neutral e ·)
                                                      × (right-neutral e ·)
                                                      × (associative ·)))

refl-left : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → refl x ∙ p ≡ p
refl-left {𝓤} {X} {x} {x} {refl x} = refl (refl x)

refl-right : {X : 𝓤 ̇ } {x y : X} {p : x ≡ y} → p ∙ refl y ≡ p
refl-right {𝓤} {X} {x} {y} {p} = refl p

∙assoc : {X : 𝓤 ̇ } {x y z t : X} (p : x ≡ y) (q : y ≡ z) (r : z ≡ t)
       → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
∙assoc p q (refl z) = refl (p ∙ q)

⁻¹-left∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
         → p ⁻¹ ∙ p ≡ refl y
⁻¹-left∙ (refl x) = refl (refl x)


⁻¹-right∙ : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
          → p ∙ p ⁻¹ ≡ refl x
⁻¹-right∙ (refl x) = refl (refl x)

⁻¹-involutive : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
              → (p ⁻¹)⁻¹ ≡ p
⁻¹-involutive (refl x) = refl (refl x)

ap-refl : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (x : X)
        → ap f (refl x) ≡ refl (f x)
ap-refl f x = refl (refl (f x))

ap-∙ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y z : X} (p : x ≡ y) (q : y ≡ z)
     → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ f p (refl y) = refl (ap f p)

ap⁻¹ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) {x y : X} (p : x ≡ y)
     → (ap f p)⁻¹ ≡ ap f (p ⁻¹)
ap⁻¹ f (refl x) = refl (refl (f x))

ap-id : {X : 𝓤 ̇ } {x y : X} (p : x ≡ y)
      → ap id p ≡ p
ap-id (refl x) = refl (refl x)

ap-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
       (f : X → Y) (g : Y → Z) {x y : X} (p : x ≡ y)
     → ap (g ∘ f) p ≡ (ap g ∘ ap f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

transport∙ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y z : X} (p : x ≡ y) (q : y ≡ z)
           → transport A (p ∙ q) ≡ transport A q ∘ transport A p
transport∙ A p (refl y) = refl (transport A p)

Nat : {X : 𝓤 ̇ } → (X → 𝓥 ̇ ) → (X → 𝓦 ̇ ) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
Nat A B = (x : domain A) → A x → B x

Nats-are-natural : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) (τ : Nat A B)
                 → {x y : X} (p : x ≡ y)
                 → τ y ∘ transport A p ≡ transport B p ∘ τ x
Nats-are-natural A B τ (refl x) = refl (τ x)

NatΣ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ } → Nat A B → Σ A → Σ B
NatΣ τ (x , a) = (x , τ x a)

transport-ap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (A : Y → 𝓦 ̇ )
               (f : X → Y) {x x' : X} (p : x ≡ x') (a : A (f x))
             → transport (A ∘ f) p a ≡ transport A (ap f p) a
transport-ap A f (refl x) a = refl a

data Color : 𝓤₀ ̇  where
 Black White : Color

apd : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f : (x : X) → A x) {x y : X}
      (p : x ≡ y) → transport A p (f x) ≡ f y
apd f (refl x) = refl (f x)

to-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
       → (Σ p ∶ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl x , refl a) = refl (x , a)

from-Σ-≡ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {σ τ : Σ A}
         → σ ≡ τ
         → Σ p ∶ pr₁ σ ≡ pr₁ τ , transport A p (pr₂ σ) ≡ pr₂ τ
from-Σ-≡ (refl (x , a)) = (refl x , refl a)

to-Σ-≡-again : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {(x , a) (y , b) : Σ A}
             → Σ p ∶ x ≡ y , transport A p a ≡ b
             → (x , a) ≡ (y , b)
to-Σ-≡-again (refl x , refl a) = refl (x , a)

from-Σ-≡-again : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {(x , a) (y , b) : Σ A}
               → (x , a) ≡ (y , b)
               → Σ p ∶ x ≡ y , transport A p a ≡ b
from-Σ-≡-again (refl (x , a)) = (refl x , refl a)

to-Σ-≡' : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {x : X} {a a' : A x}
        → a ≡ a' → Id (Σ A) (x , a) (x , a')
to-Σ-≡' {𝓤} {𝓥} {X} {A} {x} = ap (λ - → (x , -))

transport-× : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ )
              {x y : X} (p : x ≡ y) {(a , b) : A x × B x}
            → transport (λ x → A x × B x) p (a , b)
            ≡ (transport A p a , transport B p b)
transport-× A B (refl _) = refl _

transportd : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
             {x : X} ((a , b) : Σ a ∶ A x , B x a) {y : X} (p : x ≡ y)
           → B x a → B y (transport A p a)
transportd A B (a , b) (refl _) = id

transport-Σ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) (B : (x : X) → A x → 𝓦 ̇ )
              {x : X} {y : X} (p : x ≡ y) {(a , b) : Σ a ∶ A x , B x a}
            → transport (λ - → Σ (B -)) p (a , b)
            ≡ transport A p a , transportd A B (a , b) p b
transport-Σ A B (refl x) {a , b} = refl (a , b)

_is-of-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X is-of-hlevel 0 = is-singleton X
X is-of-hlevel (succ n) = (x x' : X) → ((x ≡ x') is-of-hlevel n)

wconstant : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
wconstant f = (x x' : domain f) → f x ≡ f x'

wconstant-endomap : 𝓤 ̇  → 𝓤 ̇
wconstant-endomap X = Σ f ∶ (X → X), wconstant f

wcmap : (X : 𝓤 ̇ ) → wconstant-endomap X → (X → X)
wcmap X (f , w) = f

wcmap-constancy : (X : 𝓤 ̇ ) (c : wconstant-endomap X)
                → wconstant (wcmap X c)
wcmap-constancy X (f , w) = w

Hedberg : {X : 𝓤 ̇ } (x : X) → ((y : X) → wconstant-endomap (x ≡ y)) → (y : X) → is-subsingleton (x ≡ y)
Hedberg {𝓤} {X} x c y p q =
 p ≡⟨ a y p ⟩
 (f x (refl x))⁻¹ ∙ f y p ≡⟨ ap (λ - → (f x (refl x))⁻¹ ∙ -) (κ y p q) ⟩
 (f x (refl x))⁻¹ ∙ f y q ≡⟨ (a y q)⁻¹ ⟩
 q ∎

 where
  f : (y : X) → x ≡ y → x ≡ y
  f y = wcmap (x ≡ y) (c y)
  κ : (y : X) (p q : x ≡ y) → f y p ≡ f y q
  κ y = wcmap-constancy (x ≡ y) (c y)
  a : (y : X) (p : x ≡ y) → p ≡ (f x (refl x))⁻¹ ∙ f y p
  a x (refl x) = (⁻¹-left∙ (f x (refl x)))⁻¹

wconstant-≡-endomaps : 𝓤 ̇ → 𝓤 ̇
wconstant-≡-endomaps X = (x y : X) → wconstant-endomap (x ≡ y)

sets-have-wconstant-≡-endomaps : (X : 𝓤 ̇ ) → is-set X → wconstant-≡-endomaps X
sets-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = p

  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = s x y p q

types-with-wconstant-≡-endomaps-are-sets : (X : 𝓤 ̇ )
                                         → wconstant-≡-endomaps X → is-set X
types-with-wconstant-≡-endomaps-are-sets X c x = Hedberg x
                                                  (λ y → wcmap (x ≡ y) (c x y) ,
                                                   wcmap-constancy (x ≡ y) (c x y))

subsingletons-have-wconstant-≡-endomaps : (X : 𝓤 ̇ )
                                        → is-subsingleton X
                                        → wconstant-≡-endomaps X
subsingletons-have-wconstant-≡-endomaps X s x y = (f , κ)
 where
  f : x ≡ y → x ≡ y
  f p = s x y
  κ : (p q : x ≡ y) → f p ≡ f q
  κ p q = refl (s x y)

subsingletons-are-sets : (X : 𝓤 ̇ ) → is-subsingleton X → is-set X
subsingletons-are-sets X s = types-with-wconstant-≡-endomaps-are-sets X
                               (subsingletons-have-wconstant-≡-endomaps X s)

singletons-are-sets : (X : 𝓤 ̇ ) → is-singleton X → is-set X
singletons-are-sets X = subsingletons-are-sets X ∘ singletons-are-subsingletons X

𝟘-is-set : is-set 𝟘
𝟘-is-set = subsingletons-are-sets 𝟘 𝟘-is-subsingleton

𝟙-is-set : is-set 𝟙
𝟙-is-set = subsingletons-are-sets 𝟙 𝟙-is-subsingleton

subsingletons-are-of-hlevel-1 : (X : 𝓤 ̇ ) → is-subsingleton X → X is-of-hlevel 1
subsingletons-are-of-hlevel-1 X = g
 where
  g : ((x y : X) → x ≡ y) → (x y : X) → is-singleton (x ≡ y)
  g t x y = t x y , subsingletons-are-sets X t x y (t x y)
-- t x y がcenter。pointed subsingletonになっている。

types-of-hlevel-1-are-subsingletons : (X : 𝓤 ̇ ) → X is-of-hlevel 1 → is-subsingleton X
types-of-hlevel-1-are-subsingletons X t x y = center (x ≡ y) (t x y)

sets-are-of-hlevel-2 : (X : 𝓤 ̇ ) → is-set X → X is-of-hlevel 2
sets-are-of-hlevel-2 X t x y = subsingletons-are-of-hlevel-1 (x ≡ y) (t x y)

types-of-hlevel-2-are-sets : (X : 𝓤 ̇ ) → X is-of-hlevel 2 → is-set X
types-of-hlevel-2-are-sets X t x y = types-of-hlevel-1-are-subsingletons (x ≡ y) (t x y)

hlevel-upper : (X : 𝓤 ̇ ) (n : ℕ) → X is-of-hlevel n → X is-of-hlevel (succ n)
hlevel-upper X 0 t = subsingletons-are-of-hlevel-1 X (singletons-are-subsingletons X t)
hlevel-upper X (succ n) t x y = hlevel-upper (x ≡ y) n (t x y)

_has-minimal-hlevel_ : 𝓤 ̇ → ℕ → 𝓤 ̇
X has-minimal-hlevel 0        = X is-of-hlevel 0
X has-minimal-hlevel (succ n) = (X is-of-hlevel (succ n)) × ¬(X is-of-hlevel n)

_has-minimal-hlevel-∞ : 𝓤 ̇ → 𝓤 ̇
X has-minimal-hlevel-∞ = (n : ℕ) → ¬(X is-of-hlevel n)

𝟙-has-minimal-hlevel-0 : 𝟙 has-minimal-hlevel 0
𝟙-has-minimal-hlevel-0 = 𝟙-is-singleton

𝟘-has-minimal-hlevel-1 : 𝟘 has-minimal-hlevel 1
𝟘-has-minimal-hlevel-1 = a , b
 where
  a : 𝟘 is-of-hlevel 1
  a = subsingletons-are-of-hlevel-1 𝟘 𝟘-is-subsingleton
  b : ¬(𝟘 is-of-hlevel 0)
  b s = center 𝟘 s

pointed-types-have-wconstant-endomap : {X : 𝓤 ̇ } → X → wconstant-endomap X
pointed-types-have-wconstant-endomap x = (λ y → x) , (λ y y' → refl x)

empty-types-have-wconstant-endomap : {X : 𝓤 ̇ } → is-empty X → wconstant-endomap X
empty-types-have-wconstant-endomap e = id , (λ x x' → !𝟘 (x ≡ x') (e x))

decidable-has-wconstant-endomap : {X : 𝓤 ̇ } → decidable X → wconstant-endomap X
decidable-has-wconstant-endomap (inl x) = pointed-types-have-wconstant-endomap x
decidable-has-wconstant-endomap (inr e) = empty-types-have-wconstant-endomap e

hedberg-lemma : {X : 𝓤 ̇ } → has-decidable-equality X → wconstant-≡-endomaps X
hedberg-lemma d x y = decidable-has-wconstant-endomap (d x y)

hedberg : {X : 𝓤 ̇ } → has-decidable-equality X → is-set X
-- hedberg d x = Hedberg x (hedberg-lemma d x)
hedberg {𝓤} {X} d = types-with-wconstant-≡-endomaps-are-sets X (hedberg-lemma d)

ℕ-is-set : is-set ℕ
ℕ-is-set = hedberg ℕ-has-decidable-equality

ℕ-has-minimal-hlevel-2 : ℕ has-minimal-hlevel 2
ℕ-has-minimal-hlevel-2 = a , b
 where
  a : ℕ is-of-hlevel 2
  a = sets-are-of-hlevel-2 ℕ ℕ-is-set
  b : ¬(ℕ is-of-hlevel 1)
  b h = positive-not-zero 0 (center (1 ≡ 0) (h 1 0))

𝟚-is-set : is-set 𝟚
𝟚-is-set = hedberg 𝟚-has-decidable-equality

has-section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
has-section r = Σ s ∶ (codomain r → domain r) , r ∘ s ~ id

_◁_ : 𝓤 ̇ → 𝓥 ̇  → 𝓤 ⊔ 𝓥 ̇
X ◁ Y = Σ r ∶ (Y → X) , has-section r

retraction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → Y → X
retraction (r , s , η) = r

section : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → X ◁ Y → X → Y
section (r , s , η) = s

retract-equation : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (ρ : X ◁ Y)
                 → retraction ρ ∘ section ρ ~ 𝑖𝑑 X
retract-equation (r , s , η) = η

id-◁ : (X : 𝓤 ̇ ) → X ◁ X
id-◁ X = 𝑖𝑑 X , 𝑖𝑑 X , refl

pred-◁ : ℕ ◁ ℕ
pred-◁ = pred , pred-section , e
 where
  pred-section : ℕ → ℕ
  pred-section 0 = 0
  pred-section (succ n) = succ (succ n)
  e : pred ∘ pred-section ~ id
  e 0 = refl _
  e (succ n) = refl _

-- 偶数を1/2して、奇数は適当なところに飛ばすみたいな写像もsectionを持ち、 ℕ ◁ ℕ に入る

_◁∘_ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
(r , s , η) ◁∘ (r' , s' , η') = (r ∘ r' , s' ∘ s , η'')
 where
  η'' = λ x → r (r' (s' (s x))) ≡⟨ ap r (η' (s x)) ⟩
              r (s x)           ≡⟨ η x             ⟩
              x                 ∎

_◁⟨_⟩_ : (X : 𝓤 ̇ ) {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } → X ◁ Y → Y ◁ Z → X ◁ Z
X ◁⟨ ρ ⟩ σ = ρ ◁∘ σ

_◀ : (X : 𝓤 ̇ ) → X ◁ X
X ◀ = id-◁ X

Σ-retract : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
          → ((x : X) → A x ◁  B x) → Σ A ◁ Σ B
Σ-retract {𝓤} {𝓥} {𝓦} {X} {A} {B} ρ = NatΣ r , NatΣ s , η'
 where
  r : (x : X) → B x → A x
  r x = retraction (ρ x)
  s : (x : X) → A x → B x
  s x = section (ρ x)
  η : (x : X) (a : A x) → r x (s x a) ≡ a
  η x = retract-equation (ρ x)
  η' : (σ : Σ A) → NatΣ r (NatΣ s σ) ≡ σ
  η' (x , a) = x , r x (s x a) ≡⟨ to-Σ-≡' (η x a) ⟩
               x , a           ∎

transport-is-retraction : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                        → transport A p ∘ transport A (p ⁻¹) ~ 𝑖𝑑 (A y)
transport-is-retraction A (refl x) = refl

transport-is-section : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) {x y : X} (p : x ≡ y)
                     → transport A (p ⁻¹) ∘ transport A p ~ 𝑖𝑑 (A x)
transport-is-section A (refl x) = refl

Σ-reindexing-retract : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : X → 𝓦 ̇ } (r : Y → X)
                     → has-section r
                     → (Σ x ∶ X , A x) ◁ (Σ y ∶ Y , A (r y))
Σ-reindexing-retract {𝓤} {𝓥} {𝓦} {X} {Y} {A} r (s , η) = γ , φ , γφ
 where
  γ : Σ (A ∘ r) → Σ A
  γ (y , a) = (r y , a)
  φ : Σ A → Σ (A ∘ r)
  φ (x , a) = (s x , transport A ((η x)⁻¹) a)
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = p
   where
    p : (r (s x) , transport A ((η x)⁻¹) a) ≡ (x , a)
    p = to-Σ-≡ (η x , transport-is-retraction A (η x) a)

singleton-type : {X : 𝓤 ̇ } → X → 𝓤 ̇ 
singleton-type {𝓤} {X} x = Σ y ∶ X , y ≡ x

singleton-type-center : {X : 𝓤 ̇ } (x : X) → singleton-type x
singleton-type-center x = x , refl x

singleton-type-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type x) → singleton-type-center x ≡ σ
singleton-type-centered x (x , refl x) = refl (x , refl x)

singleton-types-are-singletons : (X : 𝓤 ̇ ) (x : X) → is-singleton (singleton-type x)
singleton-types-are-singletons X x = singleton-type-center x ,
                                     singleton-type-centered x

retract-of-singleton : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → Y ◁ X → is-singleton X → is-singleton Y
retract-of-singleton (r , s , η) (c , f) = (r c , g)
 where
  g : (y : codomain r) → (r c) ≡ y
  g y = r c ≡⟨ ap r (f (s y)) ⟩
        r (s y) ≡⟨ η y ⟩
        y ∎

singleton-type' : {X : 𝓤 ̇ } → X → 𝓤 ̇
singleton-type' {𝓤} {X} x = Σ y ∶ X , x ≡ y

singleton-type'-center : {X : 𝓤 ̇ } (x : X) → singleton-type' x
singleton-type'-center x = (x , refl x)


singleton-type'-centered : {X : 𝓤 ̇ } (x : X) (σ : singleton-type' x)
                         → singleton-type'-center x ≡ σ
singleton-type'-centered x (x , refl x) = refl (x , refl x)


singleton-types'-are-singletons : (X : 𝓤 ̇ ) (x : X)
                                → is-singleton (singleton-type' x)
singleton-types'-are-singletons X x = singleton-type'-center x ,
                                      singleton-type'-centered x

infix   0 _~_
infixr 50 _,_
infixr 30 _×_
infixr 20 _+_
infixl 70 _∘_
infix   0 Id
infix   0 _≡_
infix  10 _⇔_
infixl 30 _∙_
infixr  0 _≡⟨_⟩_
infix   1 _∎
infix  40 _⁻¹

infixr -1 -Σ
infixr -1 -Π