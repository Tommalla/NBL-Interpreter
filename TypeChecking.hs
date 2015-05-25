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
		deriving (Eq)
data TypeCheckResult = Ok | Failed
		deriving (Eq)
type Env = Map Ident DataType
type PEnv = Map Ident (DataType, [DataType]) -- The tuple is the return type and then params types.
type Eval a = ExceptT String (State (Env, PEnv)) a


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


getVarOrConstType :: Exp -> Eval (Maybe DataType)
getVarOrConstType (ExpConstant constant) = return (case constant of
	ExpChar _ -> Just (Raw TypeChar)
 	ExpDouble _ -> Just (Raw TypeDouble)
 	ExpInt _ -> Just (Raw TypeInt)
 	ExpBool  _ -> Just (Raw TypeBool))
getVarOrConstType (ExpVar ident) = do
	(env, _) <- lift $ get
	return (extractType ident env)
getVarOrConstType _ = return Nothing


toConstant :: DataType -> Maybe Exp
toConstant (Raw TypeChar) = Just (ExpConstant (ExpChar '0'))
toConstant (Raw TypeDouble) = Just (ExpConstant (ExpDouble 0))
toConstant (Raw TypeInt) = Just (ExpConstant (ExpInt 0))
toConstant (Raw TypeBool) = Just (ExpConstant (ExpBool ValTrue))
toConstant _ = Nothing


getCommonType :: Maybe DataType -> Maybe DataType -> Eval (Maybe DataType)
getCommonType (Just t1) (Just t2) = do
	if t1 == t2 then 
		return (Just t1)
	else 
		return Nothing
-- TODO: If we get any casting, it goes here.
getCommonType _ _ = return Nothing


validateDirect :: DirectDeclarator -> [DeclarationSpecifier] -> Eval TypeCheckResult
validateDirect (Name ident) specifiers = do
	(env, penv) <- lift $ get
	let declType = getType specifiers
	if (isNothing declType) then
		throwError "Incorrect type!"
	else do
		lift $ put ((insert ident (fromJust declType) env), penv)
		return TypeChecking.Ok
validateDirect _ _ = throwError "This type of allocation is not supported yet."


validateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> Eval TypeCheckResult
validateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> validateDirect directDeclarator specifiers
		_ -> throwError "Not a NoPointer"
validateDeclarator _ _ = throwError "validateDeclarator not defined for this type of declaration."


validateBinaryOp :: Exp -> Exp -> Eval Exp
validateBinaryOp exp1 exp2 = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	t1 <- getVarOrConstType res1
	t2 <- getVarOrConstType res2
	tRes <- getCommonType t1 t2
	case tRes of
		Just res -> do
			let finalRes = toConstant res
			if (not (isNothing finalRes)) then
				return (fromJust finalRes)	-- An arithmetic operation always returns rvalue.
			else
				throwError "The result is inconvertible to a constant."
		Nothing -> throwError "Expressions on different types are not supported."


typesMatch :: Exp -> DataType -> Bool
typesMatch expr lType = case expr of 
	-- TODO pointers
	ExpConstant (ExpInt _) -> case lType of
		Raw TypeInt -> True
		_ -> False
	ExpConstant (ExpBool _) -> case lType of
		Raw TypeBool -> True
		_ -> False
	_ -> False


validateExp :: Exp -> Eval Exp
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
					if (typesMatch res2 (fromJust lType)) then do
						lift $ put (insert ident (fromJust lType) env, penv)
						return res2
					else
						throwError "Assignment types don't match."
		_ -> throwError "Trying to assign to something that isn't an lvalue!"
	-- TODO handle all sorts of different assignment operators
validateExp (ExpVar ident) = return (ExpVar ident)
validateExp (ExpConstant constant) = return (ExpConstant constant)
validateExp (ExpPlus exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpMinus exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpTimes exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpDiv exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpMod exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpOr exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpAnd exp1 exp2) = validateBinaryOp exp1 exp2
validateExp (ExpOr exp1 exp2) = validateBinaryOp exp1 exp2
validateExp _ = throwError "This type of exception is not supported yet."


validateStmt :: Stmt -> Eval TypeCheckResult
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
validateFunctionDeclaration :: [DeclarationSpecifier] -> Declarator -> CompoundStatement -> Eval TypeCheckResult
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


validateExternalDeclaration :: ExternalDeclaration -> Eval TypeCheckResult
validateExternalDeclaration (Global (Declarators declarationSpecifiers initDeclarators)) = return TypeChecking.Ok
validateExternalDeclaration (Func declarationSpecifiers declarator compoundStatement) = 
	validateFunctionDeclaration declarationSpecifiers declarator compoundStatement
validateExternalDeclaration _ = throwError "This type of external declaration is not supported yet."


validateProg :: Prog -> Eval TypeCheckResult
validateProg (Program externalDeclarations) = do
	mapM_ (validateExternalDeclaration) externalDeclarations
	return TypeChecking.Ok


types :: Prog -> Either String ()
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty)) of
	(Right _) -> Right ()
	(Left msg) -> Left msg 	-- TODO We should be returning an error from here. The type of 'types' needs to change.
