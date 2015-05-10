{- Tomasz Zakrzewski, tz336079
 - New Better Language Type Checking
 -}
module TypeChecking (types) where

import Control.Monad.State
import Data.Map

import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM


data DataType = Raw TypeSpecifier | Const DataType | Pointer DataType
data TypeCheckResult = Ok | Failed
		deriving (Eq)
type Env = Map Ident DataType
type PEnv = Map Ident (DataType, [DataType]) -- The tuple is the return type and then params types.
type TypeEval = State (Env, PEnv) TypeCheckResult


squashResults :: [TypeCheckResult] -> TypeCheckResult
squashResults results = if (all (== TypeChecking.Ok) results) then TypeChecking.Ok else TypeChecking.Failed


validateExternalDeclaration :: ExternalDeclaration -> TypeEval
validateExternalDeclaration (Global (Declarators declarationSpecifiers initDeclarators)) = undefined


validateProg :: Prog -> TypeEval
validateProg (Program externalDeclarations) = do
	results <- mapM (validateExternalDeclaration) externalDeclarations
	return (squashResults results)


types :: Prog -> Bool
types prog = case fst (runState (validateProg prog) (empty, empty)) of
	TypeChecking.Ok -> True
	TypeChecking.Failed -> False


