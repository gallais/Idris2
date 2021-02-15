module Libraries.Data.String.Safe

import Data.String

%default total

||| Do NOT publicly export so that users cannot manufacture arbitrary positions
export
record ValidPosition (str : String) where
  constructor MkValidPosition
  currentIndex    : Int
  parameterLength : Int
-- TODO: add invariants?
--  0 isLength : length str === parameterLength
--  0 isIndex  : (0 `LTE` currentIndex, 0 `LT` parameterLength)

||| A position is either a ValidPosition or the end of the string
public export
Position : String -> Type
Position str = Maybe (ValidPosition str)

export
mkPosition : (str : String) -> Int -> Position str
mkPosition str idx
  = do let len : Int = cast (length str)
       guard (0 <= idx && idx < len)
       pure (MkValidPosition idx len)

export
mvPosition : ValidPosition str -> Int -> Position str
mvPosition (MkValidPosition pos len) idx
  = do guard (0 <= idx && idx < len)
       pure (MkValidPosition idx len)

export
zero : (str : String) -> Position str
zero str = mkPosition str 0

export
suc : ValidPosition str -> Position str
suc (MkValidPosition pos len)
  = do let idx = pos + 1
       guard (idx < len)
       pure (MkValidPosition idx len)

export
index : {str : _} -> ValidPosition str -> Char
index pos = assert_total (strIndex str pos.currentIndex)

export
uncons : {str : _} -> ValidPosition str -> (Char, Position str)
uncons pos = (index pos, suc pos)

export
span : {str : _} -> (Char -> Bool) -> Position str -> Position str
span p pos = do (c, str) <- map uncons pos
                if p c then assert_total (span p str) else pos

export
count : {str : _} -> (Char -> Bool) -> Position str -> Nat
count p Nothing = 0
count p (Just pos) =
  if p (index pos)
    then S (assert_total (count p (suc pos)))
    else assert_total (count p (suc pos))

||| Distance between a starting position and an end one
export
distance : (start : Position str) ->
           (end : Position str) -> Int
distance Nothing _ = 0
distance (Just pos) pos' =
  let start = pos.currentIndex
      end = maybe pos.parameterLength currentIndex pos'
  in end - start

||| A subString of length `distance start end`
export
subString : {str : _} ->
            (start : Position str) ->
            (end : Position str) -> String
subString Nothing pos' = ""
subString (Just pos) pos' =
  let start = pos.currentIndex
      end = maybe pos.parameterLength currentIndex pos'
  in assert_total (strSubstr start (end - start) str)
