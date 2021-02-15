module Libraries.Text.Lexer.Tokenizer

import public Libraries.Control.Delayed
import public Libraries.Text.Bounded
import Libraries.Data.Bool.Extra
import Libraries.Data.String.Extra
import Libraries.Text.Lexer.Core
import Libraries.Text.Lexer
import Libraries.Text.PrettyPrint.Prettyprinter
import Libraries.Text.PrettyPrint.Prettyprinter.Util
import Data.List
import Data.Either
import Data.Nat
import Data.Strings

%default total

||| Description of a language's tokenization rule.
export
data Tokenizer : (tokenType : Type) -> Type where
     Match : Lexer -> (String -> tokenType) -> Tokenizer tokenType
     Compose : (begin : Lexer) ->
               (mapBegin : String -> tokenType) ->
               (tagger : String -> tag) ->
               (middle : Inf (tag -> Tokenizer tokenType)) ->
               (end : tag -> Lexer) ->
               (mapEnd : String -> tokenType) ->
               Tokenizer tokenType
     Alt : Tokenizer tokenType -> Lazy (Tokenizer tokenType) -> Tokenizer tokenType

||| Alternative tokenizer rules.
export
(<|>) : Tokenizer t -> Lazy (Tokenizer t) -> Tokenizer t
(<|>) = Alt

||| Match on a recogniser and cast the string to a token.
export
match : Lexer -> (String -> a) -> Tokenizer a
match = Match

||| Compose other tokenizer. Language composition should be quoted between
||| a begin lexer and a end lexer. The begin token can be used to generate
||| the composition tokenizer and the end lexer.
export
compose : (begin : Lexer) ->
          (mapBegin : String -> a) ->
          (tagger : String -> tag) ->
          (middle : Inf (tag -> Tokenizer a)) ->
          (end : tag -> Lexer) ->
          (mapEnd : String -> a) ->
          Tokenizer a
compose = Compose

||| Stop reason why tokenizer can't make more progress.
||| @ ComposeNotClosing carries the span of composition begin token in the
|||                     form of `(startLine, startCol), (endLine, endCol)`.
public export
data StopReason = EndInput | NoRuleApply | ComposeNotClosing (Int, Int) (Int, Int)

export
Show StopReason where
  show EndInput = "EndInput"
  show NoRuleApply = "NoRuleApply"
  show (ComposeNotClosing start end) = "ComposeNotClosing " ++ show start ++ " " ++ show end

export
Pretty StopReason where
  pretty EndInput = pretty "EndInput"
  pretty NoRuleApply = pretty "NoRuleApply"
  pretty (ComposeNotClosing start end) = "ComposeNotClosing" <++> pretty start <++> pretty end

tokenise : {str : String} ->
           Lexer ->
           Tokenizer a ->
           (line, col : Int) -> List (WithBounds a) ->
           Position str ->
           (List (WithBounds a), (StopReason, Int, Int, Position str))
tokenise reject tokenizer line col acc Nothing =
  (reverse acc, EndInput, (line, col, Nothing))
tokenise reject tokenizer line col acc str
    = case scan reject str of
           Just _ => (reverse acc, (EndInput, line, col, str))
           Nothing => case getFirstMatch tokenizer str of
                           Right (toks, line', col', rest) =>
                               -- assert total because getFirstMatch must consume something
                               assert_total (tokenise reject tokenizer line' col' (toks ++ acc) rest)
                           Left reason => (reverse acc, reason, (line, col, str))
  where
    countNLs : {str : String} -> Position str -> Nat
    countNLs = count (== '\n')

    getCols : {str : String} -> Position str -> Int -> Int
    getCols pos c
         = case span (/= '\n') pos of
             end@Nothing => c + distance pos end
             end         => distance pos end

    -- get the next lexeme using the `Lexer` in argument, its position and the input
    -- Returns the new position, the lexeme parsed and the rest of the input
    -- If parsing the lexer fails, this returns `Nothing`
    getNext : {str : String} ->
              (lexer : Lexer) ->  (line, col : Int) ->
              (input : Position str) -> Maybe (String, Int, Int, Position str)
    getNext lexer line col str =
      let Just rest = scan lexer str
            | _ => Nothing
          token = subString str rest
          line' = line + cast (countNLs (zero token))
          col' = getCols (zero token) col
      in pure (token, line', col', rest)

    getFirstMatch :
      {str : String} -> Tokenizer a -> Position str ->
      Either StopReason (List (WithBounds a), Int, Int, Position str)
    getFirstMatch (Match lex fn) str
        = let Just (tok, line', col', rest) = getNext lex line col str
                | _ => Left NoRuleApply
              tok' = MkBounded (fn tok) False line col line' col'
           in Right ([tok'], line', col', rest)
    getFirstMatch (Compose begin mapBegin tagger middleFn endFn mapEnd) str
        = let Just (beginTok', line', col' , rest) = getNext begin line col str
                | Nothing => Left NoRuleApply
              tag = tagger beginTok'
              middle = middleFn tag
              end = endFn tag
              beginTok'' = MkBounded (mapBegin beginTok') False line col line' col'
              (midToks, (reason, line'', col'', rest'')) =
                    tokenise end middle line' col' [] rest
           in case reason of
                   (ComposeNotClosing _ _) => Left reason
                   _ => let Just (endTok', lineEnd, colEnd, restEnd) =
                                getNext end line'' col'' rest''
                              | _ => Left $ ComposeNotClosing (line, col) (line', col')
                            endTok'' = MkBounded (mapEnd endTok') False line'' col'' lineEnd colEnd
                         in Right ([endTok''] ++ reverse midToks ++ [beginTok''], lineEnd, colEnd, restEnd)
    getFirstMatch (Alt t1 t2) str
        = case getFirstMatch t1 str of
               Right result => Right result
               Left reason@(ComposeNotClosing _ _) => Left reason
               Left _ => getFirstMatch t2 str

export
lexTo : Lexer ->
        Tokenizer a ->
        String ->
        (List (WithBounds a), (StopReason, Int, Int, String))
lexTo reject tokenizer str
    = let start = zero str
          (ts, reason, (l, c, str')) =
              tokenise reject tokenizer 0 0 [] start in
          (ts, reason, (l, c, subString str' Nothing))

||| Given a tokenizer and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in
||| the string where there are no recognised tokens.
export
lex : Tokenizer a -> String ->
      (List (WithBounds a), (StopReason, Int, Int, String))
lex tokenizer str = lexTo (pred $ const False) tokenizer str
