{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE FlexibleContexts #-}

module PrintCFG (toDot, toDotRev) where

import AbsLatte (Ident (..))
import CFGDefs
import Common
import Data.Map qualified as M
import Data.Text (pack, replace, unpack)

printableToDot :: (Printable [a]) => [a] -> String
printableToDot s =
  unpack $
    foldr
      ( \(from, to) acc ->
          replace (pack from) (pack to) acc
      )
      (pack (printCode s))
      replacePatterns
  where
    -- NOTE: pattern ordering is important here, e.g. "}\n" -> "}" assumes
    -- "}" -> "\\}" has been applied
    replacePatterns =
      [ (" ", "\\ "),
        ("\"", "\\\""),
        (".", "\\."),
        ("%", "\\%"),
        (">", "\\>"),
        ("<", "\\<"),
        ("{", "\\{"),
        ("}", "\\}"),
        ("\n", "\\l\n|"),
        ("}\n", "}")
      ]

bbToDot :: (Printable [a]) => BB' [a] -> String
bbToDot bb =
  bbLabStr
    ++ " [shape=record,style=filled,fillcolor=lightgrey,label=\"{"
    ++ bbLabStr
    ++ "\n|"
    ++ printableToDot (stmts bb)
    ++ "\\l\n}\"];\n\n"
    ++ foldr (\(s, w) acc -> bbLabStr ++ " -> " ++ show s ++ "[label=" ++ show w ++ "];\n" ++ acc) [] (succs bb)
    ++ foldr (\p acc -> show p ++ " -> " ++ bbLabStr ++ ";\n" ++ acc) [] (filter isFnEntry $ preds bb)
  where
    bbLabStr = show (label bb)
    isFnEntry :: Node -> Bool
    isFnEntry (FnEntry _) = True
    isFnEntry _ = False

toDotCFG :: (Printable [a]) => Ident -> CFG' [a] -> (BB' [a] -> BB' [a]) -> String
toDotCFG (Ident fnname) cfg f =
  "subgraph \"cluster_"
    ++ fnname
    ++ "\" {\n style=\"dashed\";\n color=\"black\";\n label=\""
    ++ fnname
    ++ "()\";\n"
    ++ foldr (\(_, bb) acc -> bbToDot (f bb) ++ "\n" ++ acc) [] (M.toList cfg)
    ++ "}"

toDotRev :: (Printable [a]) => CFGs' [a] -> String
toDotRev (cfgs_, _) =
  "digraph \"cfgs\" {\noverlap=false;\n"
    ++ foldr (\(idt, cfg) acc -> toDotCFG idt cfg reverseCode ++ "\n" ++ acc) [] (M.toList cfgs_)
    ++ "}"

toDot :: (Printable [a]) => CFGs' [a] -> String
toDot (cfgs_, _) =
  "digraph \"cfgs\" {\noverlap=false;\n"
    ++ foldr (\(idt, cfg) acc -> toDotCFG idt cfg id ++ "\n" ++ acc) [] (M.toList cfgs_)
    ++ "}"
