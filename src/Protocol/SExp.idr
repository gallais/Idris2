module Protocol.SExp

import Data.List
import Data.List1

import Data.String

%default total

--------------------------------------------------------
-- should be in base somewhere!

export
castNatIntegerNatCorrect : (n : Nat) -> cast (cast {to = Integer} n) === n
castNatIntegerNatCorrect n = believe_me (Refl {x = n})

export
castIntIntegerIntCorrect : (i : Int) -> cast (cast {to = Integer} i) === i
castIntIntegerIntCorrect i = believe_me (Refl {x = i})
--------------------------------------------------------

public export
data SExp = SExpList (List SExp)
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String

escape : String -> String
escape = pack . concatMap escapeChar . unpack
  where
    escapeChar : Char -> List Char
    escapeChar '\\' = ['\\', '\\']
    escapeChar '"'  = ['\\', '\"']
    escapeChar c    = [c]

export
Show SExp where
  show (SExpList xs) = assert_total $ "(" ++ joinBy " " (map show xs) ++ ")"
  show (StringAtom str) = "\"" ++ escape str ++ "\""
  show (BoolAtom b) = ":" ++ show b
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s

public export
interface SExpable a where
  toSExp : a -> SExp
  fromSExp : SExp -> Maybe a
  correctSExp : (x : a) -> fromSExp (toSExp x) === Just x

export
SExpable SExp where
  toSExp = id
  fromSExp = Just
  correctSExp x = Refl

export
SExpable Bool where
  toSExp = BoolAtom

  fromSExp (BoolAtom b) = Just b
  fromSExp _ = Nothing

  correctSExp b = Refl

export
SExpable String where
  toSExp = StringAtom

  fromSExp (StringAtom s) = Just s
  fromSExp _ = Nothing

  correctSExp s = Refl

export
SExpable Integer where
  toSExp = IntegerAtom

  fromSExp (IntegerAtom a) = Just a
  fromSExp _ = Nothing

  correctSExp i = Refl

export
SExpable Int where
  toSExp x = IntegerAtom (cast x)

  fromSExp a = do Just $ cast {from = Integer} $ !(fromSExp a)

  correctSExp i = cong Just (castIntIntegerIntCorrect i)

export
SExpable Nat where
  toSExp = IntegerAtom . cast

  fromSExp a = do Just $ cast {from = Integer} $ !(fromSExp a)

  correctSExp n = cong Just (castNatIntegerNatCorrect n)

{-
export
(SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (x, y)
      = case toSExp y of
             SExpList xs => SExpList (toSExp x :: xs)
             y' => SExpList [toSExp x, y']

  fromSExp (SExpList xs) = case xs of
    [x,y] => do pure $ (!(fromSExp x), !(fromSExp y))
    (x :: xs) => do pure $ (!(fromSExp x), !(fromSExp $ SExpList xs))
    _ => Nothing
  fromSExp _ = Nothing

  correctSExp (x, y) = ?a
-}

export
SExpable a => SExpable (List a) where
  toSExp xs
      = SExpList (map toSExp xs)

  fromSExp (SExpList sexps) = traverse fromSExp sexps
  fromSExp _ = Nothing

  correctSExp [] = Refl
  correctSExp (x :: xs)
    = rewrite correctSExp x in
      rewrite correctSExp xs in
      Refl

export
SExpable a => SExpable (List1 a) where
  toSExp xs = toSExp (toList xs)

  fromSExp (SExpList (sexp :: sexps)) = traverse fromSExp (sexp ::: sexps)
  fromSExp _ = Nothing

  correctSExp (x ::: xs)
    = rewrite correctSExp x in
      rewrite correctSExp (toList xs) in
      Refl

{-
export
SExpable a => SExpable (Maybe a) where
  toSExp Nothing = SExpList []
  toSExp (Just x) = toSExp x

  fromSExp (SExpList []) = Just Nothing
  fromSExp x = Just <$> (assert_total $ fromSExp x)

  correctSExp = ?zh
-}
