{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where

import Control.Monad.Trans.State
import Data.Map
import Data.Maybe

import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM

import TypeChecking


data DataType = TVoid | TChar Char | TInt Integer | TDouble Double | TBool Bool | TString String | TPointer DataType | 
		TConst DataType
	deriving (Show)

data ParseResult = ParseOk | Error String
	deriving (Eq)
type Loc = Int
type Env = Map Ident Loc
type MemState = Map Loc DataType
-- type PEnv = Map Ident TODO
type GlobalState = State (Env, MemState) ParseResult
type ExpState = State (Env, MemState) Exp


-- Returns a new location
newloc :: MemState -> Loc
newloc memState = (safeMaximum (keys memState)) + 1
	where
		safeMaximum :: [Loc] -> Loc 
		safeMaximum l = if (Prelude.null l) then 0 else maximum l


getLoc :: Ident -> Env -> Maybe Loc 
getLoc = Data.Map.lookup


-- Returns an initialized object of DataType based on the declaration specifiers.
createDefaultValue :: [DeclarationSpecifier] -> DataType
createDefaultValue (h:t) = if (not (Prelude.null t)) then
	case h of
		(SpecProp (Const)) -> (TConst (createDefaultValue t)) 
	 	_ -> undefined
	else case h of
		Type (TypeVoid) -> TVoid
		Type (TypeChar) -> (TChar '\0')
		Type (TypeInt) -> (TInt 0)
		Type (TypeDouble) -> (TDouble 0.0)
		Type (TypeBool) -> (TBool False)
		Type (TypeString) -> (TString "")


allocateDirect :: DirectDeclarator -> [DeclarationSpecifier] -> GlobalState
allocateDirect (Name ident) specifiers = do
	(env, state) <- get
	-- FIXME conflicts?
	let loc = newloc state
	put (insert ident loc env, insert loc (createDefaultValue specifiers) state)
	return ParseOk
allocateDirect _ _ = return (Error "Allocation not supported")


allocateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> GlobalState
allocateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator specifiers
		_ -> return (Error "Not a NoPointer")
allocateDeclarator _ _ = return (Error "Wut?")


interpretExp :: Exp -> ExpState
interpretExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- interpretExp exp1
	res2 <- interpretExp exp2
	case res1 of
		ExpVar ident -> do
				(mem, state) <- get
				let val = case res2 of 
					-- TODO pointers
					ExpConstant (ExpInt v) -> TInt v
					_ -> undefined
				let loc = getLoc ident mem
				if (isNothing loc) then
					undefined
				else 
					put (mem, update (\_ -> Just val) (fromJust loc) state)
				return res2
		_ -> undefined -- Not an lvalue
	-- TODO handle all sorts of different assignment operators
interpretExp (ExpVar ident) = return (ExpVar ident)
interpretExp (ExpConstant constant) = return (ExpConstant constant)
interpretExp _ = undefined


interpretStmt :: Stmt -> GlobalState
-- TODO do some sort of a fold on state here.
interpretStmt (DeclS (Declarators specifiers initDeclarators)) = allocateDeclarator (head initDeclarators) specifiers
interpretStmt (ExprS (ExtraSemicolon)) = return ParseOk
interpretStmt (ExprS (HangingExp exp)) = do
	mem <- get
	put (snd (runState (interpretExp exp) mem))
	return ParseOk
interpretStmt (CompS (StmtComp statements)) = do
	results <- mapM (interpretStmt) statements
	if (all (== ParseOk) results) then
		return ParseOk
	else
		return (Error "Some error")
interpretStmt _ = return (Error "undefined statement")


-- TODO change run to work on programs - need standard entry point and functions.
-- Then plug typecheck here.
run :: String -> (String, (Env, MemState))
run s = case pStmt (myLexer s) of
    Bad err -> ("Parsing error: " ++ err, (empty, empty))
    -- TODO (fix below)
    Ok p -> case (runState (interpretStmt p) (empty, empty)) of
    	(ParseOk, mem) -> ("Run successful", mem)
    	(Error str, mem) -> ("Runtime error: " ++ str, mem)


main = do
  code <- getContents
  let (out, ret) = run code
  print $ (out, ret)