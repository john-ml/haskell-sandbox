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

f2_eq1 :: forall f a b c. a == b -> f a c == f b c
f2_eq1 Refl = Refl

f2_eq2 :: forall f a b c. a == b -> f a c == f b c
f2_eq2 Refl = Refl

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

add_split :: forall a b c d.
  Nat' a -> Nat' b -> Nat' c -> Nat' d ->
  a == b -> c == d ->
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
