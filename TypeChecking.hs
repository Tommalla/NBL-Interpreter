{- Tomasz Zakrzewski, tz336079
 - New Better Language Type Checking
 -}
module TypeChecking (types,hashObjMember) where

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
data ClassMember = CFunc PSign | CVar DataType
type ClassSign = (Map Ident ClassMember, Map Ident ClassMember)
type CEnv = Map Ident ClassSign
type Eval a = ExceptT String (State (Env, PEnv, CEnv)) a


-- For convenience, we remember the class data members in the standard env with hashed names for the members.
hashObjMember :: Ident -> Ident -> Ident
hashObjMember (Ident objectName) (Ident memberName) = Ident (objectName ++ "$" ++ memberName)


-- TODO need to incorporate pointers into this.
getType :: DeclarationSpecifier -> Eval DataType
getType (Type specifier) = return (Raw specifier)
getType (QualType qual specifier) = case qual of
	Const -> do
		innerType <- getType (Type specifier)
		return (TConst innerType)
	_ -> throwError "Incorrect type."


stripConst :: DataType -> DataType
stripConst t = case t of
	(TConst res) -> res
	res -> res


extractFromMap :: Ident -> Map Ident a -> String -> Eval a
extractFromMap ident m err = case Data.Map.lookup ident m of
	Just res -> return res
	Nothing -> throwError ((shows ident) err)


extractVarType :: Ident -> Eval DataType
extractVarType ident = do
	(env, _, _) <- lift $ get
	extractFromMap ident env " - variable not declared."


-- Extracts the signature of the function.
extractFuncSign :: Ident -> Eval PSign
extractFuncSign ident = do
	(_, penv, _) <- lift $ get
	extractFromMap ident penv " - function not defined."


extractClassSign :: Ident -> Eval ClassSign
extractClassSign ident = do
	(_, _, cenv) <- lift $ get
	extractFromMap ident cenv " - object not declared."


getVarOrConstType :: Exp -> Eval (DataType)
getVarOrConstType (ExpConstant constant) = return (case constant of
	ExpChar _ -> (Raw TypeChar)
 	ExpDouble _ -> (Raw TypeDouble)
 	ExpInt _ -> (Raw TypeInt)
 	ExpBool  _ -> (Raw TypeBool))
getVarOrConstType (ExpVar ident) = do
	(env, _, _) <- lift $ get
	res <- extractVarType ident
	return res
getVarOrConstType _ = throwError "Unknown DataType for var or constant."


toConstant :: DataType -> Eval Exp
toConstant (Raw TypeChar) = return (ExpConstant (ExpChar '0'))
toConstant (Raw TypeDouble) = return (ExpConstant (ExpDouble 0))
toConstant (Raw TypeInt) = return (ExpConstant (ExpInt 0))
toConstant (Raw TypeBool) = return (ExpConstant (ExpBool ValTrue))
toConstant (Raw TypeVoid) = return (ExpConstant (ExpVoid))
toConstant t = throwError ((shows t) " is inconvertible to ExpConstant.")


getCommonType :: DataType -> DataType -> Eval (Maybe DataType)
getCommonType t1 t2 = do
	if t1 == t2 then 
		return (Just t1)
	else 
		return Nothing
-- TODO: If we get any casting, it goes here.
getCommonType _ _ = return Nothing


validateDirect :: DirectDeclarator -> DeclarationSpecifier -> Eval TypeCheckResult
validateDirect (Name ident) specifier = do
	(env, penv, cenv) <- lift $ get
	declType <- getType specifier
	lift $ put ((insert ident declType env), penv, cenv)
	case stripConst declType of
		Raw (TypeClass className) -> do
			-- Allocate the types for members
			(priv, publ) <- extractClassSign className
			mapM_ (\(member, memberType) -> do 
				case memberType of
					CVar varType -> do
						(currEnv, _, _) <- lift $ get
						lift $ put (insert (hashObjMember ident member) varType currEnv, penv, cenv)
					_ -> return ()) ((assocs priv) ++ (assocs publ))
			return TypeChecking.Ok
		_ -> return TypeChecking.Ok
validateDirect _ _ = throwError "This type of allocation is not supported yet."


validateDeclarator :: InitDeclarator -> DeclarationSpecifier -> Eval TypeCheckResult
validateDeclarator (PureDecl declarator) specifier = do
	case declarator of
		NoPointer directDeclarator -> validateDirect directDeclarator specifier
		_ -> throwError "Not a NoPointer"
validateDeclarator (InitDecl declarator (InitExpr expr)) specifier = do
	validateDeclarator (PureDecl declarator) specifier
	validateExp expr
	return TypeChecking.Ok
validateDeclarator _ _ = throwError "validateDeclarator not defined for this type of declaration."


validateBinaryOp :: Exp -> Exp -> (DataType -> DataType) -> Eval Exp
validateBinaryOp exp1 exp2 toResType = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	t1 <- getVarOrConstType res1
	t2 <- getVarOrConstType res2
	let t1Underlying = stripConst t1
	let t2Underlying = stripConst t2
	tRes <- getCommonType t1Underlying t2Underlying
	case tRes of
		Just res -> toConstant (toResType res)
		Nothing -> throwError ((shows (t1Underlying, t2Underlying))"Expressions on different types are not supported.")


typesMatch :: Exp -> DataType -> Eval Bool
typesMatch expr lType = do 
	case expr of 
		-- TODO pointers
		ExpVar ident -> do
			rType <- extractVarType ident
			return (lType == rType)
		ExpConstant (ExpInt _) -> case lType of
			Raw TypeInt -> return True
			_ -> return False
		ExpConstant (ExpBool _) -> case lType of
			Raw TypeBool -> return True
			_ -> return False
		ExpConstant (ExpString _) -> case lType of
			Raw TypeString -> return True
			_ -> return False
		_ -> return False


expToDataType :: Exp -> Eval DataType
expToDataType expr = do
	res <- validateExp expr
	(env, _, _) <- lift $ get
	case res of
		ExpVar ident -> do
			t <- extractVarType ident
			return t
		ExpConstant constant -> case constant of
				ExpChar _ -> return (Raw TypeChar)
				ExpInt _ -> return (Raw TypeInt)
				ExpDouble _ -> return (Raw TypeDouble)
				ExpBool _ -> return (Raw TypeBool)
				_ -> throwError "Constant of unknown type"


isNumeric :: Exp -> Eval Bool
isNumeric expr = do
	resType <- expToDataType expr
	return (case stripConst resType of
		Raw TypeInt -> True
		Raw TypeDouble -> True
		_ -> False)
	

isBoolean :: Exp -> Eval Bool
isBoolean expr = do
	resType <- expToDataType expr
	return (case stripConst resType of
		Raw TypeBool -> True
		_ -> False)


-- 'Lifts' the hidden class members to the top-level env.
exposeClassMemberTypes :: Ident -> Eval TypeCheckResult
exposeClassMemberTypes className = do
	(priv, publ) <- extractClassSign className
	mapM_ (\(name, val) -> do
		(env, penv, cenv) <- lift $ get
		case val of
			CVar var -> lift $ put (insert name var env, penv, cenv)
			CFunc psign -> lift $ put (env, insert name psign penv, cenv)
		) ((assocs priv) ++ (assocs publ))
	return TypeChecking.Ok


validateExp :: Exp -> Eval Exp
validateExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- validateExp exp1
	res2 <- validateExp exp2
	case res1 of
		ExpVar ident -> do
				(env, penv, cenv) <- lift $ get
				lType <- extractVarType ident
				-- TODO add non-const assignments.
				match <- typesMatch res2 lType
				if match then do
					lift $ put (insert ident lType env, penv, cenv)
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
			(_, penv, _) <- lift $ get
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
			(_, penv, _) <- lift $ get
			(retType, paramTypes) <- extractFuncSign ident
			if (paramTypes == paramTypesAppl) then do
				result <- toConstant retType
				return result
			else 
				throwError "Wrong types/quantity of arguments passed to the function"
		_ -> throwError "Function execution: Does not type."
validateExp (ExpClassVar objExp var) = do
	objEval <- validateExp objExp
	case objEval of
		ExpVar obj -> do
			objType <- extractVarType obj
			case objType of
				(Raw (TypeClass className)) -> do
					(_, publ) <- extractClassSign className
					t <- extractFromMap var publ (" is not a public class member of class " ++ (show className))
					case t of
						CVar res -> do
							return (ExpVar (hashObjMember obj var))
						_ -> throwError "This type of class member is not supported yet."
				_ -> throwError ("Not a valid class object: " ++ (show obj))
		_ -> throwError ("Not a valid class object: " ++ (show objExp))
validateExp (ExpClassFunc objExp func) = do
	objEval <- validateExp objExp
	case objEval of
		ExpVar obj -> do
			objType <- extractVarType obj
			case objType of
				(Raw (TypeClass className)) -> do
					let methodIdent = hashObjMember className func
					(env, penv, cenv) <- lift $ get
					
					res <- validateExp (ExpFunc (ExpVar methodIdent))
					lift $ put (env, penv, cenv)
					return res
				_ -> throwError ("Not a valid class object: " ++ (show obj))
		_ -> throwError ("Not a valid class object: " ++ (show objExp))
validateExp (ExpClassFuncArg objExp func paramExprs) = do
	objEval <- validateExp objExp
	case objEval of
		ExpVar obj -> do
			objType <- extractVarType obj
			case objType of
				(Raw (TypeClass className)) -> do
					let methodIdent = hashObjMember className func
					(env, penv, cenv) <- lift $ get
					
					res <- validateExp (ExpFuncArg (ExpVar methodIdent) paramExprs)
					lift $ put (env, penv, cenv)
					return res
				_ -> throwError ("Not a valid class object: " ++ (show obj))
		_ -> throwError ("Not a valid class object: " ++ (show objExp))
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
validateStmt (DeclS decl) _ _ = validateDecl decl True
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
		TypeAndParam declarationSpecifier declarator -> do
			case declarator of
				NoPointer directDeclarator -> validateDirect directDeclarator declarationSpecifier
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
					t <- getType specifiers
					return [t]
				_ -> throwError "Unsupported declarator in parameters."
parametersToTypesList (MoreParamDecl paramDecls paramDecl) = do
	res1 <- parametersToTypesList paramDecls
	res2 <- parametersToTypesList (ParamDecl paramDecl)
	return ((head res2) : res1)


validateFunctionStmt :: DataType -> Stmt -> Eval TypeCheckResult
validateFunctionStmt returnType s = do
	mem <- lift $ get
	validateStmt s False returnType
	lift $ put mem
	return TypeChecking.Ok


validateFunctionDeclaration :: DeclarationSpecifier -> Declarator -> CompoundStatement -> Bool -> Eval TypeCheckResult
validateFunctionDeclaration declarationSpecifier (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) 
		compoundStatement statements = do
	(env, penv, cenv) <- lift $ get
	-- validate declarations of param variables
	validateParamDecls parameterDeclarations
	(tempEnv, _, _) <- lift $ get
	returnType <- getType declarationSpecifier
	paramTypes <- parametersToTypesList parameterDeclarations
	let penvNew = insert ident (returnType, paramTypes) penv
	if statements then do
		lift $ put (tempEnv, penvNew, cenv)
		validateFunctionStmt returnType (CompS compoundStatement)
		lift $ put (env, penvNew, cenv)
		return TypeChecking.Ok
	else do
		lift $ put (env, penvNew, cenv)
		return TypeChecking.Ok
validateFunctionDeclaration declarationSpecifier (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement 
		statements = do
	(env, penv, cenv) <- lift $ get
	returnType <- getType declarationSpecifier
	let penvNew = insert ident (returnType, []) penv
	lift $ put (env, penvNew, cenv)	-- Have to put function in penv.
	if statements then
		validateFunctionStmt returnType (CompS compoundStatement)
	else
		return TypeChecking.Ok


-- True if the declaration block was public.
validateClassBlockDeclaration :: ClassDecl -> Bool -> Eval Bool
validateClassBlockDeclaration (PublicBlock decls) statements = do
	mapM_ (\decl -> validateDecl decl statements) decls
	return True
validateClassBlockDeclaration (ProtectedBlock decls) statements = do
	mapM_ (\decl -> validateDecl decl statements) decls
	return False


validateClassBlockDeclarationMeta :: ClassDecl -> Ident -> Bool -> Eval TypeCheckResult
validateClassBlockDeclarationMeta block name statements = do
	(env, penv, _) <- lift $ get
	public <- validateClassBlockDeclaration block statements
	(newEnv, newPEnv, cenv) <- lift $ get 
	let envDiff = newEnv \\ env
	let penvDiff = newPEnv \\ penv
	-- Put any changes to cenv
	mapM_ (\(k, e) -> do
		(curEnv, curPEnv, curCenv) <- lift $ get
		let (priv, publ) = curCenv ! name
		let newCenvEl = if public then
				(priv, insert k (CVar e) publ)
			else
				(insert k (CVar e) priv, publ)
		lift $ put (curEnv, curPEnv, insert name newCenvEl curCenv) ) (assocs envDiff)

	mapM_ (\(k, e) -> do
		(curEnv, curPEnv, curCenv) <- lift $ get
		let (priv, publ) = curCenv ! name
		let newCenvEl = if public then
				(priv, insert k (CFunc e) publ)
			else
				(insert k (CFunc e) priv, publ)
		lift $ put (curEnv, insert (hashObjMember name k) e curPEnv, insert name newCenvEl curCenv) 
		) (assocs penvDiff)

	(_, finalPEnv, finalCEnv) <- lift $ get
	lift $ put (env, finalPEnv \\ penvDiff, finalCEnv)	-- Forget the binding from inside the class.
	-- But don't drop the hashed methods!
	return TypeChecking.Ok


validateDecl :: Decl -> Bool -> Eval TypeCheckResult
validateDecl (Func declarationSpecifier declarator compoundStatement) statements = 
	validateFunctionDeclaration declarationSpecifier declarator compoundStatement statements
validateDecl (Declarators specifiers initDeclarators) _ = do
	mapM_ (\initDeclarator -> validateDeclarator initDeclarator specifiers) initDeclarators
	return TypeChecking.Ok
validateDecl (Class name blocks) statements = do
	(env, penv, cenv) <- lift $ get
	if (not statements) then do
		lift $ put (env, penv, insert name (empty, empty) cenv)
		mapM_ (\block -> validateClassBlockDeclarationMeta block name False) blocks
	else do
		exposeClassMemberTypes name
		mapM_ (\block -> validateClassBlockDeclaration block True) blocks
	return TypeChecking.Ok


validateExternalDeclaration :: ExternalDeclaration -> Bool -> Eval TypeCheckResult
validateExternalDeclaration (Global decl) statements = validateDecl decl statements
validateExternalDeclaration _ _ = throwError "This type of external declaration is not supported yet."


validateProg :: Prog -> Eval TypeCheckResult
validateProg (Program externalDeclarations) = do
	mapM_ (\decl -> validateExternalDeclaration decl False) externalDeclarations
	mapM_ (\decl -> validateExternalDeclaration decl True) externalDeclarations
	return TypeChecking.Ok


types :: Prog -> Either String ()
types prog = case fst (runState (runExceptT (validateProg prog)) (empty, empty, empty)) of
	(Right _) -> Right ()
	(Left msg) -> Left msg 	-- TODO We should be returning an error from here. The type of 'types' needs to change.
