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
		lift $ put (env, insert ident (fromJust returnType, []) penv)
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


types :: Prog -> Bool
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty)) of
	(Right _) -> True
	(Left _) -> False	-- TODO We should be returning an error from here. The type of 'types' needs to change.
