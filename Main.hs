{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where

import Control.Monad.State
import Data.Map

import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM

data DataType = TVoid | TChar Char | TInt Int | TDouble Double | TBool Bool | TString String | Pointer DataType

data ParseResult = ParseOk | Error String
type Loc = Int
type Env = Map Ident Loc
type MemState = Map Loc DataType
-- type PEnv = Map Ident TODO
type GlobalState = State (Env, MemState) ParseResult


-- Returns a new location
newloc :: MemState -> Loc
newloc memState = (maximum (keys memState)) + 1


allocateDirect :: DirectDeclarator -> GlobalState
allocateDirect (Name ident) = do
	(env, state) <- get
	-- FIXME conflicts?
	let loc = newloc(state)
	-- TODO types
	put (insert ident loc env, insert loc (TInt 0) state)
	return ParseOk
allocateDirect _ = undefined


allocateDeclarator :: InitDeclarator -> GlobalState
allocateDeclarator (PureDecl declarator) = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator
		_ -> undefined
allocateDeclarator _ = undefined


interpretDecl :: Decl -> GlobalState
interpretDecl (Declarators specifiers initDeclarators) = allocateDeclarator (head initDeclarators)


interpretStmt :: Stmt -> GlobalState
interpretStmt (DeclS decl) = interpretDecl decl
interpretStmt _ = undefined


run :: String -> (String, Int)
run s = case pStmt (myLexer s) of
    Bad err -> ("Parsing error: " ++ err, -1)
    -- TODO (fix below)
    Ok p -> case fst (runState (interpretStmt p) (empty, empty)) of
    	ParseOk -> ("Run successful", 0)
    	Error str -> ("Runtime error: " ++ str, 1)


main = do
  code <- getContents
  let (out, ret) = run code
  print $ (out, ret)