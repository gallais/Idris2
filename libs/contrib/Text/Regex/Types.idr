module Text.Regex.Types

import Decidable.Equality

%default total

namespace Regex

  public export
  data Regex : Type -> Type where
    Void : Regex a
    Unit : Regex a
    Dot  : Regex a
    Symb : a -> Regex a
    Sum  : Regex a -> Regex a -> Regex a
    Seq  : Regex a -> Regex a -> Regex a
    Star : Regex a -> Regex a

namespace IsVoid

  public export
  data IsVoid : Regex a -> Type where
    Void  : IsVoid Void
    Other : IsVoid e

  public export
  isVoid : (e : Regex a) -> IsVoid e
  isVoid Void = Void
  isVoid _ = Other

  public export
  ifIsVoid : IsVoid e -> Lazy b -> Lazy b -> b
  ifIsVoid Void l r = l
  ifIsVoid Other l r = r

  public export
  ifVoid : Regex a -> Lazy b -> Lazy b -> b
  ifVoid e l r = ifIsVoid (isVoid e) l r

namespace IsUnit

  public export
  data IsUnit : Regex a -> Type where
    Unit  : IsUnit Unit
    Other : IsUnit e

  public export
  isUnit : (e : Regex a) -> IsUnit e
  isUnit Unit = Unit
  isUnit _ = Other

  public export
  ifIsUnit : IsUnit e -> Lazy b -> Lazy b -> b
  ifIsUnit Unit l r = l
  ifIsUnit Other l r = r

  public export
  ifUnit : Regex a -> Lazy b -> Lazy b -> b
  ifUnit e l r = ifIsUnit (isUnit e) l r

namespace HasEmpty

  public export
  data HasEmpty : Regex a -> Type where
    Unit : HasEmpty Unit
    SumL : HasEmpty l -> (r : Regex a) -> HasEmpty (Sum l r)
    SumR : (l : Regex a) -> HasEmpty r -> HasEmpty (Sum l r)
    Seq : HasEmpty p -> HasEmpty q -> HasEmpty (Seq p q)
    Star : (p : Regex a) -> HasEmpty (Star p)

  export Uninhabited (HasEmpty Void) where uninhabited x impossible
  export Uninhabited (HasEmpty Dot) where uninhabited x impossible
  export Uninhabited (HasEmpty (Symb c)) where uninhabited x impossible

  public export
  hasEmptySum : HasEmpty (Sum l r) -> Either (HasEmpty l) (HasEmpty r)
  hasEmptySum (SumL l r) = Left l
  hasEmptySum (SumR l r) = Right r

  public export
  hasEmptySeq : HasEmpty (Seq p q) -> (HasEmpty p, HasEmpty q)
  hasEmptySeq (Seq p q) = (p, q)

  public export
  hasEmpty : (e : Regex a) -> Dec (HasEmpty e)
  hasEmpty Void = No absurd
  hasEmpty Unit = Yes Unit
  hasEmpty Dot  = No absurd
  hasEmpty (Symb c) = No absurd
  hasEmpty (Sum l r) = case hasEmpty l of
    (Yes l) => Yes (SumL l r)
    (No nl) => case hasEmpty r of
      (Yes r) => Yes (SumR l r)
      (No nr) => No (either nl nr . hasEmptySum)
  hasEmpty (Seq p q) = case hasEmpty p of
    (No np) => No (np . fst . hasEmptySeq)
    (Yes p) => case hasEmpty q of
      (No nq) => No (nq . snd . hasEmptySeq)
      (Yes q) => Yes (Seq p q)
  hasEmpty (Star p) = Yes (Star p)

namespace Regex

  public export
  sum : Regex a -> Regex a -> Regex a
  sum a b = ifVoid a b
          $ ifVoid b a
          $ Sum a b

  public export
  seq : Regex a -> Regex a -> Regex a
  seq a b = ifVoid a Void $ ifUnit a b
          $ ifVoid b Void $ ifUnit b a
          $ Seq a b

  public export
  star : Regex a -> Regex a
  star a = ifVoid a Unit
         $ ifUnit a Unit
         $ Star a

namespace Accepts

  public export
  data Split : (xs, ys, zs : List a) -> Type where
    Nil  : Split xs [] xs
    (::) : (x : a) -> Split xs ys zs -> Split (x :: xs) (x :: ys) zs

  public export
  split : (xs, ys : List a) -> Split (xs ++ ys) xs ys
  split [] ys = []
  split (x :: xs) ys = x :: split xs ys

  public export
  splitNil : (xs : List a) -> Split xs xs []
  splitNil [] = []
  splitNil (x :: xs) = x :: splitNil xs

  export
  splitLeftNilInversion : Split xs [] ys -> xs === ys
  splitLeftNilInversion [] = Refl

  export
  splitRightNilInversion : Split xs ys [] -> xs === ys
  splitRightNilInversion [] = Refl
  splitRightNilInversion (x :: xs) = cong (x ::) (splitRightNilInversion xs)

  export
  unsplit : Split xs ys zs -> xs === (ys ++ zs)
  unsplit [] = Refl
  unsplit (x :: xs) = cong (x ::) (unsplit xs)

  public export
  data Accepts : Regex a -> List a -> Type where
    Unit : Accepts Unit []
    Dot  : Accepts Dot [c]
    Symb : (c : a) -> Accepts (Symb c) [c]
    SumL : Accepts l cs -> (r : Regex a) -> Accepts (Sum l r) cs
    SumR : (l : Regex a) -> Accepts r cs -> Accepts (Sum l r) cs
    Seq  : (0 _ : Split cs cs1 cs2) -> Accepts p cs1 -> Accepts q cs2 -> Accepts (Seq p q) cs
    Star : Accepts (Sum Unit (Star e)) cs -> Accepts (Star e) cs

  export Uninhabited (Accepts Void cs) where uninhabited x impossible
  export Uninhabited (Accepts Unit (x::xs)) where uninhabited x impossible
  export Uninhabited (Accepts Dot []) where uninhabited x impossible
  export Uninhabited (Accepts Dot (x::y::xs)) where uninhabited x impossible
  export Uninhabited (Accepts (Symb c) []) where uninhabited x impossible
  export Uninhabited (c === x) => Uninhabited (Accepts (Symb c) [x])
    where uninhabited (Symb c) = uninhabited (the (c === c) Refl)
  export Uninhabited (Accepts (Symb c) (x::y::xs)) where uninhabited x impossible
  export Uninhabited (Accepts (Seq Void b) cs) where uninhabited (Seq _ prf _) = uninhabited prf
  export Uninhabited (Accepts (Seq a Void) cs) where uninhabited (Seq _ _ prf) = uninhabited prf

  export
  starVoidInversion : Accepts (Star Void) cs -> cs === []
  starVoidInversion (Star (SumL Unit _)) = Refl
  starVoidInversion (Star (SumR _ prf)) = starVoidInversion prf

  export
  starUnitInversion : Accepts (Star Unit) cs -> cs === []
  starUnitInversion (Star (SumL Unit _)) = Refl
  starUnitInversion (Star (SumR _ prf)) = starUnitInversion prf

  export
  sumSound : (l, r : Regex a) -> Accepts (Sum l r) cs -> Accepts (sum l r) cs
  sumSound l r prf with (isVoid l)
    sumSound _ r (SumR _ prf) | Void = prf
    sumSound l r prf | Other with (isVoid r)
      sumSound l _ (SumL prf _) | Other | Void = prf
      sumSound l r prf | Other | Other = prf

  export
  sumComplete : (l, r : Regex a) -> Accepts (sum l r) cs -> Accepts (Sum l r) cs
  sumComplete l r prf with (isVoid l)
    sumComplete _ r prf | Void = SumR _ prf
    sumComplete l r prf | Other with (isVoid r)
      sumComplete l _ prf | Other | Void = SumL prf _
      sumComplete l r prf | Other | Other = prf

  export
  seqSound : (p, q : Regex a) -> Accepts (Seq p q) cs -> Accepts (seq p q) cs
  seqSound p q prf with (isVoid p)
    seqSound Void q prf | Void = absurd prf
    seqSound p q prf | Other with (isUnit p)
      seqSound Unit q (Seq spl Unit prf) | Other | Unit =
        rewrite splitLeftNilInversion spl in prf
      seqSound p q prf | Other | Other with (isVoid q)
        seqSound p Void prf | Other | Other | Void = absurd prf
        seqSound p q prf | Other | Other | Other with (isUnit q)
        seqSound p Unit (Seq spl prf Unit) | Other | Other | Other | Unit =
          rewrite splitRightNilInversion spl in prf
        seqSound p q prf | Other | Other | Other | Other = prf

  export
  seqComplete : (p, q : Regex a) -> Accepts (seq p q) cs -> Accepts (Seq p q) cs
  seqComplete p q prf with (isVoid p)
    seqComplete Void q prf | Void = absurd prf
    seqComplete p q prf | Other with (isUnit p)
      seqComplete Unit q prf | Other | Unit = Seq [] Unit prf
      seqComplete p q prf | Other | Other with (isVoid q)
        seqComplete p Void prf | Other | Other | Void = absurd prf
        seqComplete p q prf | Other | Other | Other with (isUnit q)
        seqComplete p Unit prf | Other | Other | Other | Unit = Seq (splitNil _) prf Unit
        seqComplete p q prf | Other | Other | Other | Other = prf

  export
  starSound : (e : Regex a) -> Accepts (Star e) cs -> Accepts (star e) cs
  starSound e prf with (isVoid e)
    starSound Void prf | Void = rewrite starVoidInversion prf in Unit
    starSound e prf | Other with (isUnit e)
      starSound Unit prf | Other | Unit = rewrite starUnitInversion prf in Unit
      starSound e prf | Other | Other = prf

  export
  starComplete : (e : Regex a) -> Accepts (star e) cs -> Accepts (Star e) cs
  starComplete e prf with (isVoid e)
    starComplete Void prf | Void = Star (SumL prf _)
    starComplete e prf | Other with (isUnit e)
      starComplete Unit prf | Other | Unit = Star (SumL prf _)
      starComplete e prf | Other | Other = prf

public export
eat : DecEq a => a -> Regex a -> Regex a
eat c Dot = Unit
eat c (Symb v) = case decEq c v of
  Yes _ => Unit
  No _ => Void
eat c (Sum l r) = sum (eat c l) (eat c r)
eat c (Seq p q) = case hasEmpty p of
  Yes _ => sum (seq (eat c p) q) (eat c q)
  No _ => seq (eat c p) q
eat c (Star e) = seq (eat c e) (star e)
eat _ _ = Void

export
eatSound : DecEq a => (c : a) -> (e : Regex a) -> Accepts e (c :: cs) -> Accepts (eat c e) cs
eatSound c Unit prf = absurd prf
eatSound c Void prf = absurd prf
eatSound c Dot Dot = Unit
eatSound c (Symb c) (Symb c) = rewrite decEqSelfIsYes {x = c} in Unit
eatSound c (Sum l r) prf = sumSound (eat c l) (eat c r) $ case prf of
  SumL prf r => SumL (eatSound c l prf) (eat c r)
  SumR l prf => SumR (eat c l) (eatSound c r prf)
eatSound c (Seq p q) prf with (hasEmpty p)
  eatSound c (Seq p q) prf | Yes ep = sumSound (seq (eat c p) q) (eat c q) $ ?prf
  eatSound c (Seq p q) prf | No nep = seqSound (eat c p) q $ ?af
eatSound c (Star e) prf = ?a6

export
eatComplete : DecEq a => (c : a) -> (e : Regex a) -> Accepts (eat c e) cs -> Accepts e (c :: cs)
eatComplete c Unit prf = absurd prf
eatComplete c Void prf = absurd prf
eatComplete c Dot Unit = Dot
eatComplete c (Symb v) prf = ?c
eatComplete c (Sum l r) prf = case sumComplete (eat c l) (eat c r) prf of
  SumL prf _ => SumL (eatComplete c l prf) _
  SumR _ prf => SumR _ (eatComplete c r prf)
eatComplete c (Seq p q) prf = ?e
eatComplete c (Star e) prf = ?f
