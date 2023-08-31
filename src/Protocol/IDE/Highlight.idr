module Protocol.IDE.Highlight

import Protocol.SExp

import Protocol.IDE.FileContext
import Protocol.IDE.Decoration

%default total

public export
record Highlight where
  constructor MkHighlight
  location : FileContext
  name : String
  isImplicit : Bool
  key : String
  decor : Decoration
  docOverview : String
  typ : String
  ns : String

public export
record LwHighlight where
  constructor MkLwHighlight
  location : FileContext
  decor : Decoration

export
SExpable Highlight where
  toSExp (MkHighlight fc nam impl k dec doc t ns)
    = SExpList [ toSExp fc
               , SExpList [ SExpList [ SymbolAtom "name", toSExp nam ]
                          , SExpList [ SymbolAtom "namespace", toSExp ns ]
                          , toSExp dec
                          , SExpList [ SymbolAtom "implicit", toSExp impl ]
                          , SExpList [ SymbolAtom "key", toSExp k ]
                          , SExpList [ SymbolAtom "doc-overview", toSExp doc ]
                          , SExpList [ SymbolAtom "type", toSExp t ]
                          ]
               ]

  fromSExp (SExpList [ fc
               , SExpList [ SExpList [ SymbolAtom "name", nam ]
                          , SExpList [ SymbolAtom "namespace", ns ]
                          , dec
                          , SExpList [ SymbolAtom "implicit", impl ]
                          , SExpList [ SymbolAtom "key", key ]
                          , SExpList [ SymbolAtom "doc-overview", doc ]
                          , SExpList [ SymbolAtom "type", typ ]
                          ]
               ]) = do
                 pure $ MkHighlight
                   { location = !(fromSExp fc)
                   , name = !(fromSExp nam)
                   , ns = !(fromSExp ns)
                   , isImplicit = !(fromSExp impl)
                   , decor = !(fromSExp dec)
                   , docOverview = !(fromSExp doc)
                   , key = !(fromSExp key)
                   , typ = !(fromSExp typ)
                   }
  fromSExp _ = Nothing

  correctSExp (MkHighlight location name isImplicit key decor docOverview typ ns)
    = ?a_0

{-

export
SExpable LwHighlight where
  toSExp lwhl = SExpList
                 [ toSExp lwhl.location
                 , SExpList [ toSExp lwhl.decor]
                 ]

export
FromSExpable LwHighlight where
  fromSExp (SExpList
            [ location
            , SExpList [ decor ]
            ]) = do pure $ MkLwHighlight
                      { location = !(fromSExp location)
                      , decor    = !(fromSExp decor)}
  fromSExp _ = Nothing

public export
data SourceHighlight =
    Full Highlight
  | Lw LwHighlight

export
SExpable SourceHighlight where
  toSExp (Full hl) = toSExp hl
  toSExp (Lw   hl) = toSExp hl

export
FromSExpable SourceHighlight where
  fromSExp shl = do
    let Nothing = fromSExp shl
      | Just hl => Just (Full hl)
    hl <- fromSExp shl
    pure $ Lw hl
