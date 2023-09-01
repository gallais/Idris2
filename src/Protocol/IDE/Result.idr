module Protocol.IDE.Result

import Protocol.SExp

import Protocol.IDE.Holes
import Protocol.IDE.FileContext

import Data.List
import Data.List1
import Data.Maybe
import Data.So

%default total

public export
data OptionType = BOOL | STRING | ATOM

public export
(.sem) : OptionType -> Type
BOOL   .sem = Bool
STRING .sem = String
ATOM   .sem = String

%unbound_implicits off
public export
record REPLOption where
  constructor MkOption
  name : String
  type : OptionType
  val  : type.sem
%unbound_implicits on

-- Did I just break the protocol? This used to collapse STRING and ATOM!
toSExpOption : (type : OptionType) -> type.sem -> SExp
toSExpOption BOOL = BoolAtom
toSExpOption STRING = StringAtom
toSExpOption ATOM = SymbolAtom

fromSExpOption : SExp -> Maybe (type : OptionType ** type.sem)
fromSExpOption (BoolAtom b) = Just (BOOL ** b)
fromSExpOption (StringAtom str) = Just (STRING ** str)
fromSExpOption (SymbolAtom at) = Just (ATOM ** at)
fromSExpOption _ = Nothing

correctSExpOption : (type: OptionType) -> (val : type.sem) ->
  fromSExpOption (toSExpOption type val) === Just (type ** val)
correctSExpOption BOOL val = Refl
correctSExpOption STRING val = Refl
correctSExpOption ATOM val = Refl

export
SExpable REPLOption where
  toSExp (MkOption name type val) = SExpList
    [ SymbolAtom name
    , toSExpOption type val
    ]

  fromSExp (SExpList
    [ SymbolAtom name
    , val
    ]) = pure $ MkOption { name, val = snd !(fromSExpOption val), _ }
  fromSExp _ = Nothing

  correctSExp (MkOption name type val)
    = rewrite correctSExpOption type val in Refl

public export
record MetaVarLemma where
  constructor MkMetaVarLemma
  application, lemma : String

export
SExpable MetaVarLemma where
  toSExp mvl = SExpList [ SymbolAtom "metavariable-lemma"
             , SExpList [ SymbolAtom "replace-metavariable", StringAtom mvl.application ]
             , SExpList [ SymbolAtom "definition-type", StringAtom mvl.lemma ]
             ]

  fromSExp (SExpList [ SymbolAtom "metavariable-lemma"
            , SExpList [ SymbolAtom "replace-metavariable", StringAtom application ]
            , SExpList [ SymbolAtom "definition-type", StringAtom lemma ]
            ]) = Just $ MkMetaVarLemma {application, lemma}
  fromSExp _ = Nothing

  correctSExp (MkMetaVarLemma app lem) = Refl

public export
data TagType : Type where
  NoTag : TagType
  ATag  : (str : String) -> {auto 0 nonEmpty : So (not (str == ""))} -> TagType

public export
record IdrisVersion where
  constructor MkIdrisVersion
  major, minor, patch : Nat
  tag : TagType

export
SExpable TagType where
  toSExp NoTag = StringAtom ""
  toSExp (ATag str) = StringAtom str

  fromSExp (StringAtom str) = case choose (str == "") of
    Left _ => pure NoTag
    Right prf => pure (ATag str)
  fromSExp _ = Nothing

  correctSExp NoTag with (choose True)
    _ | Left _ = Refl
    _ | Right prf = absurd prf
  correctSExp (ATag str @{prf}) with (str == "")
    _ | True = void $ absurd prf
    correctSExp (ATag str @{Oh}) | False with (choose False)
      _ | Left prf' = absurd prf'
      _ | Right Oh = Refl

export
SExpable IdrisVersion where
  toSExp (MkIdrisVersion major minor patch tag) = SExpList
    [ SExpList (map toSExp [major, minor, patch])
    , SExpList [toSExp tag]
    ]

  fromSExp (SExpList [ SExpList [majorSExp, minorSExp, patchSExp]
                     , SExpList [tagSExp]
                     ])
    = do pure $ MkIdrisVersion
              { major = !(fromSExp majorSExp)
              , minor = !(fromSExp minorSExp)
              , patch = !(fromSExp patchSExp)
              , tag = !(fromSExp tagSExp)
              }
  fromSExp _ = Nothing

  correctSExp (MkIdrisVersion major minor patch tag)
    = rewrite correctSExp tag in
      rewrite castNatIntegerNatCorrect major in
      rewrite castNatIntegerNatCorrect minor in
      rewrite castNatIntegerNatCorrect patch in
      Refl

public export
data Result =
    AString String
  | AUnit
  | AVersion IdrisVersion
  | AMetaVarLemma MetaVarLemma
  | ANameLocList (List (String, FileContext))
  | AHoleList (List HoleData)
  | ACompletionList (List String) String
  | ANameList (List String)
  | AnOptionList (List REPLOption)
  | AnIntroList (List1 String)

toSExpNameLoc : (String, FileContext) -> SExp
toSExpNameLoc (str, fc) = SExpList [toSExp str, toSExp fc]

fromSExpNameLoc : SExp -> Maybe (String, FileContext)
fromSExpNameLoc (SExpList [str, fc]) = [| (fromSExp str, fromSExp fc) |]
fromSExpNameLoc _ = Nothing

correctSExpNameLoc : (nfc : (String, FileContext)) ->
  fromSExpNameLoc (toSExpNameLoc nfc) === Just nfc
correctSExpNameLoc (str, fc) = rewrite correctSExp fc in Refl

toSExpNameLocList : List (String, FileContext) -> SExp
toSExpNameLocList fcs = SExpList $ map toSExpNameLoc fcs

fromSExpNameLocList : SExp -> Maybe (List (String, FileContext))
fromSExpNameLocList (SExpList fcs) = traverse fromSExpNameLoc fcs
fromSExpNameLocList _ = Nothing


correctSExpNameLocList : (fcs : List (String, FileContext)) ->
    traverse Result.fromSExpNameLoc (map Result.toSExpNameLoc fcs) = Just fcs
correctSExpNameLocList [] = Refl
correctSExpNameLocList (nfc :: fcs)
    = rewrite correctSExpNameLoc nfc in
      rewrite correctSExpNameLocList fcs in
      Refl


toSExpCompletionList : List String -> String -> SExp
toSExpCompletionList names str = SExpList [toSExp names, toSExp str]

fromSExpCompletionList : SExp -> Maybe (List String, String)
fromSExpCompletionList (SExpList [names, str]) = [| (fromSExp names, fromSExp str) |]
fromSExpCompletionList _ = Nothing

export
SExpable Result where
  toSExp (AString s) = toSExp s
  toSExp (AUnit    ) = SExpList []
  toSExp (AVersion version) = toSExp version
  toSExp (AMetaVarLemma mvl) = toSExp mvl
  toSExp (ANameLocList fcs) = toSExpNameLocList fcs
  toSExp (AHoleList holes) = toSExp holes
  toSExp (ANameList names) = toSExp names
  toSExp (ACompletionList names str) = toSExpCompletionList names str
  toSExp (AnOptionList opts) = toSExp opts
  toSExp (AnIntroList iss) = toSExp iss

  fromSExp (SExpList []) = Just AUnit -- resolve ambiguity somewhat arbitrarily...
  fromSExp sexp = do
  let Nothing = fromSExp sexp
    | Just str => pure $ AString str
  let Nothing = fromSExp sexp
    | Just version => pure $ AVersion version
  let Nothing = fromSExp sexp
    | Just mvl => pure $ AMetaVarLemma mvl
  let Nothing = fromSExpNameLocList sexp
    | Just nll => pure $ ANameLocList nll
  let Nothing = fromSExp sexp
    | Just hl => pure $ AHoleList hl
  let Nothing = fromSExp sexp
    | Just nl => pure $ ANameList nl
  let Nothing = fromSExpCompletionList sexp
    | Just nlr => pure $ uncurry ACompletionList nlr
  let Nothing = fromSExp sexp
    | Just optl => pure $ AnOptionList optl
  let Nothing = fromSExp sexp
    | Just optl => pure $ AnIntroList optl
  Nothing

  correctSExp (AString str) = Refl
  correctSExp AUnit = Refl
  correctSExp (AVersion version) with (correctSExp version) | (toSExp version)
    _ | prf | (SExpList (x :: xs)) = rewrite prf in Refl
  correctSExp (AMetaVarLemma (MkMetaVarLemma application lemma)) = Refl
  correctSExp (ANameLocList fcs) with (correctSExpNameLocList fcs) | (map toSExpNameLoc fcs)
    _ | prf | xs = ?A
  correctSExp (AHoleList xs) = ?ak_5
  correctSExp (ACompletionList strs str) = ?ak_6
  correctSExp (ANameList strs) = ?ak_7
  correctSExp (AnOptionList xs) = ?ak_8
  correctSExp (AnIntroList xs) = ?ak_9
