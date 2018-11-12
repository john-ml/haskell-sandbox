{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Proofs where

-- some sugar to make proofs nicer to read

infixl 1 !
f! a = f a

infixr 0 .
f. a = f a

infixl 3 !!
f!! a = f a

infixr 2 ...
f... a = f a

-- logic

data True = True
data False
data And a b = And a b
data Or a b = Left a | Right b
type Not a = a -> False

type (/\) = And
type (\/) = Or
type a <-> b = (a -> b) /\ (b -> a)

data Exists f where
  Ex_intro :: f a -> Exists f

excluded_middle :: forall a. a \/ Not a
excluded_middle = excluded_middle

trivial :: forall a. a -> True
trivial _ = True

absurd :: forall a. False -> a
absurd = \ case

void :: forall a. a
void = void

flip :: forall a b c. (a -> b -> c) -> (b -> a -> c)
flip f b a = f a b

and_sym :: forall a b. a /\ b -> b /\ a
and_sym (And a b) = And b a

and_elim_l :: forall a b. a /\ b -> a
and_elim_l (And a _) = a

and_id_l :: forall a b. a -> True /\ a
and_id_l = And True

and_id_r :: forall a b. a -> a /\ True
and_id_r = flip And True

and_elim_r :: forall a b. a /\ b -> b
and_elim_r (And _ b) = b

either :: forall a b c. (a -> c) -> (b -> c) -> a \/ b -> c
either f g = \ case
  Left a -> f a
  Right b -> g b

or_sym :: forall a b. a \/ b -> b \/ a
or_sym = either Right Left

or_id_l :: forall a b. False \/ a -> a
or_id_l = either absurd implies_refl

or_id_r :: forall a b. a \/ False -> a
or_id_r = either implies_refl absurd

not_and_distr' :: forall a b. Not a \/ Not b -> Not (a /\ b)
not_and_distr' = \ case
  Left not_a -> \ (And a _) -> absurd (not_a a)
  Right not_b -> \ (And _ b) -> absurd (not_b b)

not_and_distr :: forall a b. Not (a /\ b) -> Not a \/ Not b
not_and_distr =
  case excluded_middle @a of
    Left a ->
      case excluded_middle @b of
        Left b -> \ not_a_and_b -> absurd. not_a_and_b. And a b
        Right not_b -> \ _ -> Right not_b
    Right not_a -> \ _ -> Left not_a

not_or_distr' :: forall a b. Not a /\ Not b -> Not (a \/ b)
not_or_distr' = \ (And not_a not_b) -> either not_a not_b

not_or_distr :: forall a b. Not (a \/ b) -> Not a /\ Not b
not_or_distr =
  case excluded_middle @a of
    Left a -> \ not_a_or_b -> absurd. not_a_or_b. Left. a
    Right not_a ->
      case excluded_middle @b of
        Left b -> \ not_a_or_b -> absurd. not_a_or_b. Right. b
        Right not_b -> \ _ -> And not_a not_b

implies_refl :: forall a. a -> a
implies_refl a = a

implies_trans :: forall a b c. (a -> b) -> (b -> c) -> (a -> c)
implies_trans a_implies_b b_implies_c a = b_implies_c. a_implies_b. a

iff_refl :: forall a. a <-> a
iff_refl = And implies_refl implies_refl

iff_trans :: forall a b c. (a <-> b) -> (b <-> c) -> (a <-> c)
iff_trans (And a_implies_b b_implies_a) (And b_implies_c c_implies_b) =
  And (implies_trans a_implies_b b_implies_c) (implies_trans c_implies_b b_implies_a)

iff_sym :: forall a b. (a <-> b) -> (b <-> a)
iff_sym = and_sym

-- equality

infixl 1 ==
data a == b where
  Refl :: a == a

sym :: forall a b. a == b -> b == a
sym Refl = Refl

trans :: forall a b c. a == b -> b == c -> a == c
trans Refl Refl = Refl

f_eq :: forall f a b. a == b -> f a == f b
f_eq Refl = Refl

f_sub :: forall f a b. a == b -> f a -> f b
f_sub Refl f = f

f2_eq1 :: forall f a b c. a == b -> f a c == f b c
f2_eq1 Refl = Refl

f2_eq2 :: forall f a b c. a == b -> f c a == f c b
f2_eq2 Refl = Refl

f2_sub1 :: forall f a b c. a == b -> f a c -> f b c
f2_sub1 Refl f = f

f2_sub2 :: forall f a b c. a == b -> f c a -> f c b
f2_sub2 Refl f = f

-- arithmetic

data Nat = O | S Nat

data Nat' a where
  O' :: Nat' O
  S' :: Nat' a -> Nat' (S a)

infixl 6 +
type family a + b :: Nat where
  O + b = b
  S a + b = S (a + b)

(+) :: forall a b. Nat' a -> Nat' b -> Nat' (a + b)
O' + b = b
S' a + b = S' (a + b)

add_sub_l :: forall c a b. Nat' a -> Nat' b -> Nat' c -> a == b -> a + c == b + c
add_sub_l _ _ _ Refl = Refl

add_sub_r :: forall c a b. Nat' a -> Nat' b -> Nat' c -> a == b -> c + a == c + b
add_sub_r _ _ _ Refl = Refl

add_split :: forall a b c d.  Nat' a -> Nat' b -> Nat' c -> Nat' d ->
  a == b ->
  c == d ->
  a + c == b + d
add_split _ _ _ _ Refl Refl = Refl

add_id_r :: forall a. Nat' a -> a + O == a
add_id_r O' = Refl
add_id_r (S' a) = f_eq @S. add_id_r a

add_S_r :: forall a b. Nat' a -> Nat' b -> a + S b == S (a + b)
add_S_r O' _ = Refl
add_S_r (S' a) b = f_eq @S. add_S_r a b

add_comm :: forall a b. Nat' a -> Nat' b -> a + b == b + a
add_comm O' b = sym. add_id_r b
add_comm a O' = add_id_r a
add_comm (S' a) (S' b) =
  f_eq @S.
  trans (add_S_r a b).
  flip trans (sym. add_S_r b a).
  f_eq @S.
  add_comm a b

add_assoc :: forall a b c. Nat' a -> Nat' b -> Nat' c -> a + (b + c) == a + b + c
add_assoc O' _ _ = Refl
add_assoc (S' a) b c = f_eq @S. add_assoc a b c

infixl 7 *
type family a * b :: Nat where
  O * _ = O
  S a * b = b + a * b

(*) :: forall a b. Nat' a -> Nat' b -> Nat' (a * b)
O' * _ = O'
S' a * b = b + a * b

mul_O_r :: forall a. Nat' a -> a * O == O
mul_O_r O' = Refl
mul_O_r (S' a) = mul_O_r a

mul_id_r :: forall a. Nat' a -> a * S O == a
mul_id_r O' = Refl
mul_id_r (S' a) = f_eq @S. mul_id_r a

mul_id_l :: forall a. Nat' a -> S O * a == a
mul_id_l O' = Refl
mul_id_l (S' a) = f_eq @S. add_id_r a

mul_comm :: forall a b. Nat' a -> Nat' b -> a * b == b * a
mul_comm O' b = sym. mul_O_r b
mul_comm a O' = mul_O_r a
mul_comm (S' a) (S' b) =
  let ih_a_Sb = mul_comm a (S' b) in
  let ih_Sa_b = mul_comm (S' a) b in
  trans (add_sub_r (a * S' b) (S' b * a) (S' b) ih_a_Sb).
  flip trans (add_sub_r (S' a * b) (b * S' a) (S' a) ih_Sa_b).
  f_eq @S.
  trans (add_assoc b a (b * a)).
  flip trans (sym. add_assoc a b (a * b)).
  add_split (b + a) (a + b) (b * a) (a * b)!
    add_comm b a.
    mul_comm b a

mul_add_distr_l :: forall a b c. Nat' a -> Nat' b -> Nat' c -> a * (b + c) == a * b + a * c
mul_add_distr_l O' _ _ = Refl
mul_add_distr_l (S' a) b c =
  flip trans (add_assoc b (a * b) (S' a * c)).
  flip trans!
    add_sub_r (c + (a * b + a * c)) (a * b + S' a * c) b...
    flip trans (sym. add_assoc (a * b) c (a * c))...
    trans (add_assoc c (a * b) (a * c))...
    add_sub_l (c + a * b) (a * b + c) (a * c)...
    add_comm c (a * b).
    flip trans (sym. add_assoc b c (a * b + a * c))...
    add_sub_r (a * (b + c)) (a * b + a * c) (b + c)...
    mul_add_distr_l a b c

mul_add_distr_r :: forall a b c. Nat' a -> Nat' b -> Nat' c -> (a + b) * c == a * c + b * c
mul_add_distr_r a b c =
  trans (mul_comm (a + b) c).
  trans (mul_add_distr_l c a b).
  add_split (c * a) (a * c) (c * b) (b * c)!
    mul_comm c a.
    mul_comm c b

mul_assoc :: forall a b c. Nat' a -> Nat' b -> Nat' c -> a * b * c == a * (b * c)
mul_assoc O' _ _ = Refl
mul_assoc (S' a) b c =
  trans (mul_add_distr_r b (a * b) c).
  add_sub_r (a * b * c) (a * (b * c)) (b * c).
  mul_assoc a b c

-- parity

data Even a where
  EvenO :: Even O
  EvenSS :: forall a. Even a -> Even (S (S a))

data Odd a where
  OddSO :: Odd (S O)
  OddSS :: forall a. Odd a -> Odd (S (S a))

exists_even :: Exists Even
exists_even = Ex_intro EvenO

exists_odd :: Exists Odd
exists_odd = Ex_intro OddSO

even_S_odd :: forall a. Nat' a -> Even a -> Odd (S a)
even_S_odd _ EvenO = OddSO
even_S_odd (S' (S' a)) (EvenSS even_a) = OddSS. even_S_odd a even_a

odd_S_even :: forall a. Nat' a -> Odd a -> Even (S a)
odd_S_even _ OddSO = EvenSS EvenO
odd_S_even (S' (S' a)) (OddSS odd_a) = EvenSS. odd_S_even a odd_a

double_even :: forall a. Nat' a -> Even (a + a)
double_even O' = EvenO
double_even (S' a) =
  flip (f_sub @Even) (EvenSS. double_even a).
  f_eq @S. sym. add_S_r a a

even_add_even_even :: forall a b. Nat' a -> Nat' b -> Even a -> Even b -> Even (a + b)
even_add_even_even _ _ EvenO even_b = even_b
even_add_even_even (S' (S' a)) b (EvenSS even_a) even_b =
  EvenSS. even_add_even_even a b even_a even_b

odd_add_odd_even :: forall a b. Nat' a -> Nat' b -> Odd a -> Odd b -> Even (a + b)
odd_add_odd_even _ b OddSO odd_b = odd_S_even b odd_b
odd_add_odd_even (S' (S' a)) b (OddSS odd_a) odd_b =
  EvenSS. odd_add_odd_even a b odd_a odd_b

even_mul_l :: forall a b. Nat' a -> Nat' b -> Even a -> Even (a * b)
even_mul_l _ _ EvenO = EvenO
even_mul_l (S' (S' a)) b (EvenSS even_a) =
  f_sub @Even (sym. add_assoc b b (a * b)).
  even_add_even_even (b + b) (a * b) (double_even b).
  even_mul_l a b even_a

even_mul_r :: forall a b. Nat' a -> Nat' b -> Even b -> Even (a * b)
even_mul_r a b even_b = f_sub @Even (mul_comm b a). even_mul_l b a even_b
