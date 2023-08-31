module Protocol.IDE.FileContext

import Protocol.SExp

import public Libraries.Text.Bounded

import Control.Function
import Data.Maybe
import Decidable.Decidable
import Decidable.Equality

%default total

public export
record FileContext where
  constructor MkFileContext
  file : String
  range : Bounds

toSExpBounds : String -> (Int, Int) -> SExp
toSExpBounds s (line, col)
  = SExpList [ SymbolAtom s
             , toSExp line
             , toSExp col
             ]

fromSExpBounds : String -> SExp -> Maybe (Int, Int)
fromSExpBounds s (SExpList [ SymbolAtom s', line, col ])
  = if isYes (decEq s s') then [| (fromSExp line, fromSExp col) |] else Nothing
fromSExpBounds _ _ = Nothing

correctSExpBounds : (s : String) -> (bds : (Int, Int)) ->
                    fromSExpBounds s (toSExpBounds s bds) === Just bds
correctSExpBounds s (line, col) with (decEq s s)
  _ | No neq = absurd (neq Refl)
  _ | Yes Refl
    = cong Just
    $ cong2 (,) (injective (correctSExp line))
                (injective (correctSExp col))

export
SExpable FileContext where
  toSExp (MkFileContext file bounds) =
    SExpList [ SExpList [ SymbolAtom "filename", toSExp file ]
             , toSExpBounds "start" (startBounds bounds)
             , toSExpBounds "end" (endBounds bounds)
             ]

  fromSExp (SExpList
           [ SExpList [ SymbolAtom "filename", filenameSExp ]
           , startBounds
           , endBounds
           ]) = pure $ MkFileContext
                       { file = !(fromSExp filenameSExp)
                       , range = mkBounds !(fromSExpBounds "start" startBounds)
                                          !(fromSExpBounds "end" endBounds)
                       }
  fromSExp _ = Nothing

  correctSExp (MkFileContext file bds)
     = rewrite correctSExpBounds "start" (startBounds bds) in
       rewrite correctSExpBounds "end" (endBounds bds) in
       rewrite mkBoundsCorrect bds in
       Refl
