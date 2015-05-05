{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where

import Control.Monad.Trans.State
import Data.Map

import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM

data DataType = TVoid | TChar Char | TInt Int | TDouble Double | TBool Bool | TString String | TPointer DataType | 
		TConst DataType

data ParseResult = ParseOk | Error String
type Loc = Int
type Env = Map Ident Loc
type MemState = Map Loc DataType
-- type PEnv = Map Ident TODO
type GlobalState = State (Env, MemState) ParseResult


-- Returns a new location
newloc :: MemState -> Loc
newloc memState = (maximum (keys memState)) + 1


-- Returns an initialized object of DataType based on the declaration specifiers.
createDefaultValue :: [DeclarationSpecifier] -> DataType
createDefaultValue (h:t) = case h of
	(SpecProp (Const)) -> (TConst (createDefaultValue t)) 
	_ -> undefined
createDefaultValue [(Type (TypeVoid))] = TVoid
createDefaultValue [(Type (TypeChar))] = (TChar '\0')
createDefaultValue [(Type (TypeInt))] = (TInt 0)
createDefaultValue [(Type (TypeDouble))] = (TDouble 0.0)
createDefaultValue [(Type (TypeBool))] = (TBool False)
createDefaultValue [(Type (TypeString))] = (TString "")


allocateDirect :: DirectDeclarator -> [DeclarationSpecifier] -> GlobalState
allocateDirect (Name ident) specifiers = do
	(env, state) <- get
	-- FIXME conflicts?
	let loc = newloc(state)
	put (insert ident loc env, insert loc (createDefaultValue specifiers) state)
	return ParseOk
allocateDirect _ _ = undefined


allocateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> GlobalState
allocateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator specifiers
		_ -> undefined
allocateDeclarator _ _ = undefined


interpretStmt :: Stmt -> GlobalState
-- TODO do some sort of a fold on state here.
interpretStmt (DeclS (Declarators specifiers initDeclarators)) = allocateDeclarator (head initDeclarators) specifiers
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