module Protocol.IDE.Holes

import Protocol.SExp

%default total

public export
record HolePremise where
  constructor MkHolePremise
  name : String -- Future: send more structured representation of:
                -- im/explicity (+ default value?) + quantity
  type : String -- Future: String + highlighting info

export
SExpable HolePremise where
  toSExp premise =
    SExpList [ StringAtom premise.name
             , StringAtom premise.type
             , SExpList [] -- TODO: metadata
             ]

  fromSExp (SExpList [ StringAtom name
             , StringAtom type
             , SExpList [] -- TODO: metadata
             ]) = do pure $ MkHolePremise
                      {name, type}
  fromSExp _ = Nothing

  correctSExp (MkHolePremise nm ty) = Refl

public export
record HoleData where
  constructor MkHoleData
  name : String
  type : String -- Future : String + highlighting info
  context : List HolePremise

export
SExpable HoleData where
  toSExp hole = SExpList
    [ StringAtom hole.name -- TODO: did I break the protocol? It used to be: (show  hole.name)
    , toSExp hole.context
    , SExpList [ toSExp hole.type   -- Conclusion
               , SExpList[]]        -- TODO: Highlighting information
    ]

  fromSExp (SExpList
    [ StringAtom name
    , context
    , SExpList [ conclusion
               , SExpList[]]        -- TODO: Highlighting information
    ]) = do pure $ MkHoleData {name, type = !(fromSExp conclusion), context = !(fromSExp context)}
  fromSExp _ = Nothing

  correctSExp (MkHoleData nm ty ctx)
    = rewrite correctSExp ctx in Refl
