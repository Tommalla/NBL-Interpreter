{- Tomasz Zakrzewski, tz336079
 - New Better Language Type Checking
 -}
module TypeChecking (types) where

import Control.Monad.Except
import Control.Monad.State
import Data.Map
import Data.Maybe

import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM


data DataType = Raw TypeSpecifier | TConst DataType | TPointer DataType
data TypeCheckResult = Ok | Failed
		deriving (Eq)
type Env = Map Ident DataType
type PEnv = Map Ident (DataType, [DataType]) -- The tuple is the return type and then params types.
type TypeEval = ExceptT String (State (Env, PEnv)) TypeCheckResult
type ExpTypeEval = ExceptT String (State (Env, PEnv)) Exp


-- TODO need to incorporate pointers into this.
getType :: [DeclarationSpecifier] -> Maybe DataType
getType (h:t) = if (not (Prelude.null t)) then
	case h of
		SpecProp (Const) -> do
			innerType <- getType t
			return (TConst innerType)
	 	_ -> Nothing
	else case h of
		SpecProp (Const) -> Nothing
		Type anything -> Just (Raw anything)


extractType :: Ident -> Env -> Maybe DataType
extractType = Data.Map.lookup


validateDirect :: DirectDeclarator -> [DeclarationSpecifier] -> TypeEval
validateDirect (Name ident) specifiers = do
	(env, penv) <- lift $ get
	let declType = getType specifiers
	if (isNothing declType) then
		throwError "Incorrect type!"
	else do
		lift $ put ((insert ident (fromJust declType) env), penv)
		return TypeChecking.Ok
validateDirect _ _ = throwError "This type of allocation is not supported yet."


validateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> TypeEval
validateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> validateDirect directDeclarator specifiers
		_ -> throwError "Not a NoPointer"
validateDeclarator _ _ = throwError "validateDeclarator not defined for this type of declaration."


validateExp :: Exp -> ExpTypeEval
validateExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	case res1 of
		ExpVar ident -> do
				(env, penv) <- lift $ get
				let lType = extractType ident env
				if (isNothing lType) then
					throwError "lvalue does not type."
				else do
					case res2 of 
						-- TODO pointers
						ExpConstant (ExpInt _) -> case fromJust lType of
							(Raw TypeInt) -> do
								lift $ put (insert ident (fromJust lType) env, penv)
								return res2
							_ -> throwError "Types don't match..."
						_ -> throwError "rvalue is not a constant - not supported"
		_ -> throwError "Trying to assign to something that isn't an lvalue!"
	-- TODO handle all sorts of different assignment operators
validateExp (ExpVar ident) = return (ExpVar ident)
validateExp (ExpConstant constant) = return (ExpConstant constant)
validateExp _ = throwError "This type of exception is not supported yet."


validateStmt :: Stmt -> TypeEval
validateStmt (DeclS (Declarators specifiers initDeclarators)) = do
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	return TypeChecking.Ok
validateStmt (ExprS (ExtraSemicolon)) = return TypeChecking.Ok
validateStmt (ExprS (HangingExp exp)) = do
	validateExp exp
	return TypeChecking.Ok
validateStmt (CompS (StmtComp statements)) = do
	mapM_ (validateStmt) statements
	return TypeChecking.Ok
validateStmt _ = throwError "This type of statement is not supported yet."


-- TODO this function needs to validate the types inside the instructions in CompoundStatement.
validateFunctionDeclaration :: [DeclarationSpecifier] -> Declarator -> CompoundStatement -> TypeEval
validateFunctionDeclaration declarationSpecifiers (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) 
		compoundStatement = throwError "Functions with parameters are not supported yet."
validateFunctionDeclaration declarationSpecifiers (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement = do
	(env, penv) <- lift $ get
	let returnType = getType declarationSpecifiers
	if (isNothing returnType) then
		throwError "Incorrect function return type!"
	else do
		let penv = insert ident (fromJust returnType, []) penv
		lift $ put (env, penv)	-- Have to put function in penv.
		validateStmt (CompS compoundStatement)
		lift $ put (env, penv)	-- Restore the previous state.
		return TypeChecking.Ok
validateFunctionDeclaration _ _ _ = throwError "Malformed function declaration. "


validateExternalDeclaration :: ExternalDeclaration -> TypeEval
validateExternalDeclaration (Global (Declarators declarationSpecifiers initDeclarators)) = return TypeChecking.Ok
validateExternalDeclaration (Func declarationSpecifiers declarator compoundStatement) = 
	validateFunctionDeclaration declarationSpecifiers declarator compoundStatement
validateExternalDeclaration _ = throwError "This type of external declaration is not supported yet."


validateProg :: Prog -> TypeEval
validateProg (Program externalDeclarations) = do
	mapM_ (validateExternalDeclaration) externalDeclarations
	return TypeChecking.Ok


types :: Prog -> Either String ()
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty)) of
	(Right _) -> Right ()
	(Left msg) -> Left msg 	-- TODO We should be returning an error from here. The type of 'types' needs to change.
