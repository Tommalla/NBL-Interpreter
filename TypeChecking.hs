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
		deriving (Eq,Show)
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
validateDeclarator (InitDecl declarator (InitExpr expr)) specifiers = do
	validateDeclarator (PureDecl declarator) specifiers
	validateExp expr
	return TypeChecking.Ok
validateDeclarator _ _ = throwError "validateDeclarator not defined for this type of declaration."


validateBinaryOp :: Exp -> Exp -> (DataType -> DataType) -> Eval Exp
validateBinaryOp exp1 exp2 toResType = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	t1 <- getVarOrConstType res1
	t2 <- getVarOrConstType res2
	tRes <- getCommonType t1 t2
	case tRes of
		Just res -> do
			let finalRes = toConstant (toResType res)
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


expToDataType :: Exp -> Eval (Maybe DataType)
expToDataType expr = do
	res <- validateExp expr
	(env, _) <- lift $ get
	return (case res of
		ExpVar ident -> extractType ident env
		ExpConstant constant -> case constant of
				ExpChar _ -> Just (Raw TypeChar)
				ExpInt _ -> Just (Raw TypeInt)
				ExpDouble _ -> Just (Raw TypeDouble)
				ExpBool _ -> Just (Raw TypeBool)
				_ -> Nothing)


isNumeric :: Exp -> Eval Bool
isNumeric expr = do
	resType <- expToDataType expr
	if (isNothing resType) then 
		return False
	else
		return (case (fromJust resType) of
			Raw TypeInt -> True
			Raw TypeDouble -> True
			_ -> False)
	

isBoolean :: Exp -> Eval Bool
isBoolean expr = do
	resType <- expToDataType expr
	if (isNothing resType) then 
		return False
	else
		return (case (fromJust resType) of
			Raw TypeBool -> True
			_ -> False)


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
					-- TODO add non-const assignments.
					if (typesMatch res2 (fromJust lType)) then do
						lift $ put (insert ident (fromJust lType) env, penv)
						return res2
					else
						throwError ((shows (lType, res2)) "Assignment types don't match.")
		_ -> throwError "Trying to assign to something that isn't an lvalue!"
	-- TODO handle all sorts of different assignment operators
validateExp (ExpVar ident) = return (ExpVar ident)
validateExp (ExpConstant constant) = return (ExpConstant constant)
validateExp (ExpPlus exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpMinus exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpTimes exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpDiv exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpMod exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpOr exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpAnd exp1 exp2) = validateBinaryOp exp1 exp2 (id)
validateExp (ExpOr exp1 exp2) = validateBinaryOp exp1 exp2 (id)
-- All below need to return bool.
validateExp (ExpEq exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
validateExp (ExpNeq exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
validateExp (ExpLt exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
validateExp (ExpGt exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
validateExp (ExpLe exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
validateExp (ExpGe exp1 exp2) = validateBinaryOp exp1 exp2 (\_ -> Raw TypeBool)
-- TODO go deeper into types, forbid operations on types where it makes no sense.
-- Pre/Post Inc/Dec
validateExp (ExpPreInc expr) = do
	numeric <- isNumeric expr
	if numeric then
		return expr
	else
		throwError "Not a numeric value."
validateExp (ExpPreDec expr) = validateExp (ExpPreInc expr)
validateExp (ExpPostInc expr) = validateExp (ExpPreInc expr)
validateExp (ExpPostDec expr) = validateExp (ExpPreInc expr)
validateExp (ExpPreOp op expr) = do
	res <- validateExp expr
	numeric <- isNumeric res
	boolean <- isBoolean res
	case op of
		Plus -> if numeric then 
				return res
			else 
				throwError "Not a numeric type."
		Negative -> if numeric then 
				return res
			else 
				throwError "Not a numeric type."
		Negation -> if boolean then
				return res
			else
				throwError "Not a boolean type."
		_ -> throwError "This type of unary operation is not supported yet."
validateExp x = throwError ((shows x) "This type of expression is not supported yet.")


validateControlStmt :: ControlStatement -> Bool -> Eval TypeCheckResult
validateControlStmt (IfThenElse ctlExp s1 s2) inLoop = do
	validateExp ctlExp
	validateStmt s1 inLoop
	validateStmt s2 inLoop
	return TypeChecking.Ok
validateControlStmt (IfThen ctlExp s) inLoop = validateControlStmt (IfThenElse ctlExp s (CompS EmptyComp)) inLoop


validateLoopStmt :: LoopStatement -> Eval TypeCheckResult
validateLoopStmt (LoopWhile ctlExp s) = do
	validateExp ctlExp
	validateStmt s True
validateLoopStmt (LoopDoWhile s ctlExp) = validateLoopStmt (LoopWhile ctlExp s)
validateLoopStmt (LoopForThree (Declarators specifiers initDeclarators) ctlExpStmt deltaExp s) = do
	prevMapping <- lift $ get
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	validateStmt (ExprS ctlExpStmt) True
	validateExp deltaExp
	validateStmt s True
	lift $ put prevMapping
	return TypeChecking.Ok
validateLoopStmt (LoopForTwo decl ctlExpStmt s) = 
		validateLoopStmt (LoopForThree decl ctlExpStmt (ExpConstant (ExpInt 0)) s)


validateStmt :: Stmt -> Bool -> Eval TypeCheckResult
validateStmt (DeclS (Declarators specifiers initDeclarators)) _ = do
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	return TypeChecking.Ok
validateStmt (ExprS (ExtraSemicolon)) _ = return TypeChecking.Ok
validateStmt (ExprS (HangingExp exp)) _ = do
	validateExp exp
	return TypeChecking.Ok
validateStmt (CompS (StmtComp statements)) inLoop = do
	mapM_ (\stmt -> validateStmt stmt inLoop) statements
	return TypeChecking.Ok
validateStmt (CompS (EmptyComp)) _ = return TypeChecking.Ok
validateStmt (CtlS controlStatement) inLoop = validateControlStmt controlStatement inLoop
validateStmt (LoopS loopStatement) _ = validateLoopStmt loopStatement
validateStmt (JumpS Break) inLoop = if inLoop then return TypeChecking.Ok else throwError "Break without a loop."
validateStmt (JumpS Continue) inLoop = validateStmt (JumpS Break) inLoop
validateStmt (PrintS (Print expr)) _ = do
	validateExp expr
	return TypeChecking.Ok
validateStmt x _ = throwError ((shows x) " This type of statement is not supported yet.")


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
		validateStmt (CompS compoundStatement) False
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
