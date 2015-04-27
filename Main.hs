{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where


import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM


interpret :: Program -> String
interpret e = "TODO"


run :: String -> (String, Integer)
run s = case pProgram (myLexer s) of
    Bad err -> ("Parsing error: " ++ err, -1)
    Ok e -> (interpret e, 0)	-- TODO


main = do
  code <- getContents
  let (out, ret) = run code
  putStrLn $ out