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


validateExternalDeclaration :: ExternalDeclaration -> TypeEval
validateExternalDeclaration (Global (Declarators declarationSpecifiers initDeclarators)) = do
	return TypeChecking.Ok
validateExternalDeclaration _ = do
	return TypeChecking.Ok


validateProg :: Prog -> TypeEval
validateProg (Program externalDeclarations) = do
	results <- mapM (validateExternalDeclaration) externalDeclarations
	return TypeChecking.Ok


types :: Prog -> Bool
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty)) of
	(Right _) -> True
	(Left _) -> False	-- TODO We should be returning an error from here.

