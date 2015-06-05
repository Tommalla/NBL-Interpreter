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
type PSign = (DataType, [DataType]) -- The tuple is the return type and then params types.
type PEnv = Map Ident PSign
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


extractVarType :: Ident -> Env -> Maybe DataType
extractVarType = Data.Map.lookup


-- Extracts the signature of the function.
extractFuncSign :: Ident -> Eval PSign
extractFuncSign ident = do
	(_, penv) <- lift $ get
	case Data.Map.lookup ident penv of
		Just res -> return res
		Nothing -> throwError ((shows ident) " - function not declared.")


getVarOrConstType :: Exp -> Eval (DataType)
getVarOrConstType (ExpConstant constant) = return (case constant of
	ExpChar _ -> (Raw TypeChar)
 	ExpDouble _ -> (Raw TypeDouble)
 	ExpInt _ -> (Raw TypeInt)
 	ExpBool  _ -> (Raw TypeBool))
getVarOrConstType (ExpVar ident) = do
	(env, _) <- lift $ get
	let res = extractVarType ident env
	if (isNothing res) then
		throwError "Variable not declared."
	else
		return (fromJust res)
getVarOrConstType _ = throwError "Unknown DataType for var or constant."


toConstant :: DataType -> Eval Exp
toConstant (Raw TypeChar) = return (ExpConstant (ExpChar '0'))
toConstant (Raw TypeDouble) = return (ExpConstant (ExpDouble 0))
toConstant (Raw TypeInt) = return (ExpConstant (ExpInt 0))
toConstant (Raw TypeBool) = return (ExpConstant (ExpBool ValTrue))
toConstant t = throwError ((shows t) " is inconvertible to ExpConstant.")


getCommonType :: DataType -> DataType -> Eval (Maybe DataType)
getCommonType t1 t2 = do
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
		Just res -> toConstant (toResType res)
		Nothing -> throwError ((shows (t1, t2))"Expressions on different types are not supported.")


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


expToDataType :: Exp -> Eval DataType
expToDataType expr = do
	res <- validateExp expr
	(env, _) <- lift $ get
	case res of
		ExpVar ident -> do
			let t = extractVarType ident env
			case t of
				Just res -> return res
				Nothing -> throwError ((shows ident) " does not type.")
		ExpConstant constant -> case constant of
				ExpChar _ -> return (Raw TypeChar)
				ExpInt _ -> return (Raw TypeInt)
				ExpDouble _ -> return (Raw TypeDouble)
				ExpBool _ -> return (Raw TypeBool)
				_ -> throwError "Constant of unknown type"


isNumeric :: Exp -> Eval Bool
isNumeric expr = do
	resType <- expToDataType expr
	return (case resType of
		Raw TypeInt -> True
		Raw TypeDouble -> True
		_ -> False)
	

isBoolean :: Exp -> Eval Bool
isBoolean expr = do
	resType <- expToDataType expr
	return (case resType of
		Raw TypeBool -> True
		_ -> False)


validateExp :: Exp -> Eval Exp
validateExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	case res1 of
		ExpVar ident -> do
				(env, penv) <- lift $ get
				let lType = extractVarType ident env
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
validateExp (ExpFunc expr) = do
	res <- validateExp expr
	case res of
		ExpVar ident -> do
			(_, penv) <- lift $ get
			(retType, paramTypes) <- extractFuncSign ident
			if (Prelude.null paramTypes) then do
				result <- toConstant retType
				return result
			else 
				throwError "Not enought arguments passed to the function."
		_ -> throwError "Function execution: Does not type."
validateExp (ExpFuncArg expr paramExprs) = do
	res <- validateExp expr
	paramTypesAppl <- mapM (\e -> do 
		expFinal <- validateExp e
		getVarOrConstType expFinal) paramExprs
	case res of
		ExpVar ident -> do
			(_, penv) <- lift $ get
			(retType, paramTypes) <- extractFuncSign ident
			if (paramTypes == paramTypesAppl) then do
				result <- toConstant retType
				return result
			else 
				throwError "Wrong types/quantity of arguments passed to the function"
		_ -> throwError "Function execution: Does not type."
validateExp x = throwError ((shows x) "This type of expression is not supported yet.")


validateControlStmt :: ControlStatement -> Bool -> DataType -> Eval TypeCheckResult
validateControlStmt (IfThenElse ctlExp s1 s2) inLoop retType = do
	validateExp ctlExp
	validateStmt s1 inLoop retType
	validateStmt s2 inLoop retType
	return TypeChecking.Ok
validateControlStmt (IfThen ctlExp s) inLoop retType = 
	validateControlStmt (IfThenElse ctlExp s (CompS EmptyComp)) inLoop retType


validateLoopStmt :: LoopStatement -> DataType -> Eval TypeCheckResult
validateLoopStmt (LoopWhile ctlExp s) retType = do
	validateExp ctlExp
	validateStmt s True retType
validateLoopStmt (LoopDoWhile s ctlExp) retType = validateLoopStmt (LoopWhile ctlExp s) retType
validateLoopStmt (LoopForThree (Declarators specifiers initDeclarators) ctlExpStmt deltaExp s) retType = do
	prevMapping <- lift $ get
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	validateStmt (ExprS ctlExpStmt) True retType
	validateExp deltaExp
	validateStmt s True retType
	lift $ put prevMapping
	return TypeChecking.Ok
validateLoopStmt (LoopForTwo decl ctlExpStmt s) retType = 
		validateLoopStmt (LoopForThree decl ctlExpStmt (ExpConstant (ExpInt 0)) s) retType


validateStmt :: Stmt -> Bool -> DataType -> Eval TypeCheckResult
validateStmt (DeclS (Declarators specifiers initDeclarators)) _ _ = do
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	return TypeChecking.Ok
validateStmt (ExprS (ExtraSemicolon)) _ _ = return TypeChecking.Ok
validateStmt (ExprS (HangingExp exp)) _ _ = do
	validateExp exp
	return TypeChecking.Ok
validateStmt (CompS (StmtComp statements)) inLoop retType = do
	mapM_ (\stmt -> validateStmt stmt inLoop retType) statements
	return TypeChecking.Ok
validateStmt (CompS (EmptyComp)) _ _ = return TypeChecking.Ok
validateStmt (CtlS controlStatement) inLoop retType = validateControlStmt controlStatement inLoop retType
validateStmt (LoopS loopStatement) _ retType = validateLoopStmt loopStatement retType
validateStmt (JumpS Break) inLoop _ = if inLoop then return TypeChecking.Ok else throwError "Break without a loop."
validateStmt (JumpS Continue) inLoop retType = validateStmt (JumpS Break) inLoop retType
validateStmt (PrintS (Print expr)) _ _ = do
	validateExp expr
	return TypeChecking.Ok
validateStmt (JumpS ReturnVoid) _ retType = if (retType == Raw TypeVoid) then 
		return TypeChecking.Ok
	else
		throwError "Return without a returned value in a non-void function."
validateStmt (JumpS (ReturnVal expr)) _ retType = do
	returnType <- expToDataType expr
	if (returnType == retType) then
		return TypeChecking.Ok
	else
		throwError ((shows (returnType, retType)) " Expected and actual return types don't match.")
validateStmt x _ _ = throwError ((shows x) " This type of statement is not supported yet.")


validateParamDecls :: ParameterDeclarations -> Eval TypeCheckResult
validateParamDecls (ParamDecl parameterDeclaration) = do 
	case parameterDeclaration of
		OnlyType _ -> return TypeChecking.Ok -- FIXME?
		TypeAndParam declarationSpecifiers declarator -> do
			case declarator of
				NoPointer directDeclarator -> validateDirect directDeclarator declarationSpecifiers
				_ -> throwError "Pointers not supported yet."
validateParamDecls (MoreParamDecl paramDecls paramDecl) = do
	validateParamDecls (paramDecls)
	validateParamDecls (ParamDecl paramDecl)


parametersToTypesList :: ParameterDeclarations -> Eval [DataType]
parametersToTypesList (ParamDecl parameterDeclaration) = do 
	case parameterDeclaration of
		OnlyType _ -> throwError "Not supported"
		TypeAndParam specifiers declarator -> do 
			case declarator of
				NoPointer _ -> do
					let t = getType specifiers
					if (isNothing t) then
						throwError "Cannot deduce the parameter type."
					else
						return [fromJust t]
				_ -> throwError "Unsupported declarator in parameters."
parametersToTypesList (MoreParamDecl paramDecls paramDecl) = do
	res1 <- parametersToTypesList paramDecls
	res2 <- parametersToTypesList (ParamDecl paramDecl)
	return ((head res2) : res1)


validateFunctionStmt :: Maybe DataType -> Stmt -> Eval TypeCheckResult
validateFunctionStmt returnType s = do
	if (isNothing returnType) then
		throwError "Incorrect function return type!"
	else do
		mem <- lift $ get
		validateStmt s False (fromJust returnType)
		lift $ put mem
		return TypeChecking.Ok


validateFunctionDeclaration :: [DeclarationSpecifier] -> Declarator -> CompoundStatement -> Bool -> Eval TypeCheckResult
validateFunctionDeclaration declarationSpecifiers (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) 
		compoundStatement statements = do
	(env, penv) <- lift $ get
	-- validate declarations of param variables
	validateParamDecls parameterDeclarations
	(tempEnv, _) <- lift $ get
	let returnType = getType declarationSpecifiers
	paramTypes <- parametersToTypesList parameterDeclarations
	let penvNew = insert ident (fromJust returnType, paramTypes) penv
	if statements then do
		lift $ put (tempEnv, penvNew)
		validateFunctionStmt returnType (CompS compoundStatement)
		lift $ put (env, penvNew)
		return TypeChecking.Ok
	else do
		lift $ put (env, penvNew)
		return TypeChecking.Ok
validateFunctionDeclaration declarationSpecifiers (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement 
		statements = do
	(env, penv) <- lift $ get
	let returnType = getType declarationSpecifiers
	let penvNew = insert ident (fromJust returnType, []) penv
	lift $ put (env, penvNew)	-- Have to put function in penv.
	if statements then
		validateFunctionStmt returnType (CompS compoundStatement)
	else
		return TypeChecking.Ok


validateExternalDeclaration :: ExternalDeclaration -> Bool -> Eval TypeCheckResult
validateExternalDeclaration (Global (Declarators declarationSpecifiers initDeclarators)) _ = return TypeChecking.Ok
validateExternalDeclaration (Func declarationSpecifiers declarator compoundStatement) statements = 
	validateFunctionDeclaration declarationSpecifiers declarator compoundStatement statements
validateExternalDeclaration _ _ = throwError "This type of external declaration is not supported yet."


validateProg :: Prog -> Eval TypeCheckResult
validateProg (Program externalDeclarations) = do
	mapM_ (\decl -> validateExternalDeclaration decl False) externalDeclarations
	mapM_ (\decl -> validateExternalDeclaration decl True) externalDeclarations
	return TypeChecking.Ok


types :: Prog -> Either String ()
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty)) of
	(Right _) -> Right ()
	(Left msg) -> Left msg 	-- TODO We should be returning an error from here. The type of 'types' needs to change.
