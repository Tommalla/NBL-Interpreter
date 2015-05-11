{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where

import Control.Monad.Except
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


data DataType = 
	  TVoid 
	| TChar Char 
	| TInt Integer 
	| TDouble Double 
	| TBool Bool 
	| TString String 
	| TPointer DataType 
	| TConst DataType
	deriving (Show)

data ParseResult = ParseOk | Error String
	deriving (Eq)
type Loc = Int
type Env = Map Ident Loc
type Store = Map Loc DataType
type PEnv = Map Ident ([Ident], CompoundStatement, Env)	-- The list is the list of argument names.
type StateType = (Env, PEnv, Store)
type GlobalState = ExceptT String (State StateType) ParseResult
type ExpState = ExceptT String (State StateType) Exp


-- Returns a new location
newloc :: Store -> Loc
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
	(env, penv, state) <- lift $ get
	-- FIXME conflicts?
	let loc = newloc state
	lift $ put (insert ident loc env, penv, insert loc (createDefaultValue specifiers) state)
	return ParseOk
allocateDirect _ _ = throwError "This type of allocation is not supported yet."


allocateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> GlobalState
allocateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator specifiers
		_ -> throwError "Not a NoPointer"
allocateDeclarator _ _ = throwError "Allocate declarator not defined for this type of declaration."


executeExp :: Exp -> ExpState
executeExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- executeExp exp1
	res2 <- executeExp exp2
	case res1 of
		ExpVar ident -> do
				(env, penv, state) <- lift $ get
				let val = case res2 of 
					-- TODO pointers
					ExpConstant (ExpInt v) -> TInt v
					_ -> undefined
				let loc = getLoc ident env
				if (isNothing loc) then
					let (Ident identStr) = ident in
							throwError ("Exp: " ++ identStr ++ " was not declared!")
				else 
					lift $ put (env, penv, update (\_ -> Just val) (fromJust loc) state)
				return res2
		_ -> throwError "Trying to assign to something that isn't an lvalue!"
	-- TODO handle all sorts of different assignment operators
executeExp (ExpVar ident) = return (ExpVar ident)
executeExp (ExpConstant constant) = return (ExpConstant constant)
executeExp _ = throwError "This type of exception is not supported yet."


executeStmt :: Stmt -> GlobalState
executeStmt (DeclS (Declarators specifiers initDeclarators)) = allocateDeclarator (head initDeclarators) specifiers
executeStmt (ExprS (ExtraSemicolon)) = return ParseOk
executeStmt (ExprS (HangingExp exp)) = do
	mem <- lift $ get
	lift $ put (snd (runState (runExceptT (executeExp exp)) mem))
	return ParseOk
executeStmt (CompS (StmtComp statements)) = do
	mapM_ (executeStmt) statements
	return ParseOk
executeStmt _ = throwError "This type of statement is not supported yet."


executeFunctionDeclaration :: Declarator -> CompoundStatement -> GlobalState
executeFunctionDeclaration (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) compoundStatement = 
	throwError "Functions with parameters are not supported yet."
executeFunctionDeclaration (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement = do
	(env, penv, store) <- lift $ get
	lift $ put (env, insert ident ([], compoundStatement, env) penv, store)
	return ParseOk
executeFunctionDeclaration declarator _ = throwError "Malformed function declaration. "


executeExternalDeclaration :: ExternalDeclaration -> GlobalState
executeExternalDeclaration (Func declarationSpecifiers declarator compoundStatement) =
	executeFunctionDeclaration declarator compoundStatement
executeExternalDeclaration (Global (Declarators specifiers initDeclarators)) = do
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	return ParseOk 


executeProg :: Prog -> GlobalState
executeProg (Program externalDeclarations) = do
	mapM_ (executeExternalDeclaration) externalDeclarations
	return ParseOk


run :: String -> (String, StateType)
run s = case pProg (myLexer s) of
    Bad err -> ("Parsing error: " ++ err, (empty, empty, empty))
    Ok p -> 
    	if not (types p) then
    		("Typechecking failed", (empty, empty, empty))
    	else
    		case (runState (runExceptT (executeProg p)) (empty, empty, empty)) of
    			((Right _), (e, penv, store)) -> 
    				let mainFunc = Data.Map.lookup (Ident "main") penv in
    					if (isNothing mainFunc) then ("No main declared.", (e, penv, store)) else
							let (params, compoundStatement, env) = fromJust mainFunc in
								case (runState (runExceptT (executeStmt (CompS compoundStatement))) (env, penv, store)) of
									((Right _), mem) -> ("Run successful", mem)
									((Left str), mem) -> ("Runtime error: " ++ str, mem)
    			((Left str), mem) -> ("Runtime error: " ++ str, mem)


main = do
  code <- getContents
  let (out, ret) = run code
  print $ (out, ret)