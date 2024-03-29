{- Tomasz Zakrzewski, tz336079
 - New Better Language Interpreter
 -}
module Main where

import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.Fix
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
	| TObject Ident
	deriving (Show)

data ParseResult = ExecOk | Error String
	deriving (Eq)
type Loc = Int
type Env = Map Ident Loc
type Store = Map Loc DataType
type Func = ([Ident], CompoundStatement, Env)	-- The list is the list of argument names.
type ClassTemplate = (Env, PEnv)
type CEnv = Map Ident ClassTemplate
type PEnv = Map Ident Func
type StateType = (Env, PEnv, CEnv, Store)
type ContExec a = ContT StateType (ExceptT String (StateT StateType (IO))) a
type ContS = ContExec ParseResult
type ContExp = Exp -> ContExec Exp
data Operator = 
	  Plus 
	| Minus 
	| Times 
	| Div
	| Mod 
	| And 
	| Or 
	| Eq 
	| Neq 
	| Lt 
	| Gt 
	| Le 
	| Ge


add :: DataType -> DataType -> DataType
add (TInt a) (TInt b) = TInt (a + b)
add (TDouble a) (TDouble b) = TDouble (a + b)


sub :: DataType -> DataType -> DataType
sub (TInt a) (TInt b) = TInt (a - b)
sub (TDouble a) (TDouble b) = TDouble (a - b)


mul :: DataType -> DataType -> DataType
mul (TInt a) (TInt b) = TInt (a * b)
mul (TDouble a) (TDouble b) = TDouble (a * b)


div :: DataType -> DataType -> DataType
div (TInt a) (TInt b) = TInt (a `Prelude.div` b)
div (TDouble a) (TDouble b) = TDouble (a / b)


mod :: DataType -> DataType -> DataType
mod (TInt a) (TInt b) = TInt (a `Prelude.mod` b)


or :: DataType -> DataType -> DataType
or (TBool a) (TBool b) = TBool (a || b)


and :: DataType -> DataType -> DataType
and (TBool a) (TBool b) = TBool (a && b)


boolOp :: Eq a => a -> (a -> a -> Bool) -> a -> DataType
boolOp a op b = TBool (a `op` b)


eq :: DataType -> DataType -> DataType
eq (TBool a) (TBool b) = boolOp a (==) b
eq (TInt a) (TInt b) = boolOp a (==) b
eq (TDouble a) (TDouble b) = boolOp a (==) b


not :: DataType -> DataType
not (TBool b) = TBool (Prelude.not b)
not (TInt i) = TBool (i == 0)


neq :: DataType -> DataType -> DataType
neq = Main.eq . Main.not


lt :: DataType -> DataType -> DataType
lt (TInt a) (TInt b) = boolOp a (<) b
lt (TDouble a) (TDouble b) = boolOp a (<) b


gt :: DataType -> DataType -> DataType
gt (TInt a) (TInt b) = boolOp a (>) b
gt (TDouble a) (TDouble b) = boolOp a (>) b


le :: DataType -> DataType -> DataType
le a b = Main.not (Main.gt a b)


ge :: DataType -> DataType -> DataType
ge a b = Main.not (Main.lt a b)


canDivideBy :: DataType -> Bool
canDivideBy val = case val of
	TInt 0 -> False
	TDouble 0 -> False
	_ -> True

-- Returns a new location
newloc :: Store -> Loc
newloc memState = (safeMaximum (keys memState)) + 1 where
	safeMaximum :: [Loc] -> Loc 
	safeMaximum l = if (Prelude.null l) then 0 else maximum l


getLoc :: Ident -> Env -> Loc 
getLoc ident env = env ! ident


getVal :: Ident -> ContExec DataType
getVal ident = do
	(env, _, _, store) <- lift.lift $ get
	return (store ! (getLoc ident env))


getFunc :: Ident -> ContExec Func
getFunc ident = do
	(_, penv, _, _) <- lift.lift $ get
	return (penv ! ident)


getClass :: Ident -> ContExec ClassTemplate
getClass ident = do
	(_, _, cenv, _) <- lift.lift $ get
	return (cenv ! ident)


getBadBreakCont :: ContS
getBadBreakCont = callCC $ \retHere -> do lift $ throwError "Break called from top level!"


constantToDataType :: Constant -> DataType
constantToDataType (ExpChar c) = TChar c
constantToDataType (ExpDouble d) = TDouble d
constantToDataType (ExpInt i) = TInt i
constantToDataType (ExpBool b) = TBool (b == ValTrue)
constantToDataType (ExpString s) = TString s


dataTypeToConstant :: DataType -> Constant
dataTypeToConstant (TChar c) = ExpChar c
dataTypeToConstant (TDouble d) = ExpDouble d
dataTypeToConstant (TInt i) = ExpInt i
dataTypeToConstant (TBool b) = ExpBool (if b then ValTrue else ValFalse)
dataTypeToConstant (TString s) = ExpString s


-- Extracts the underlying value. Works only for vars and consts.
getDirectValue :: Exp -> ContExec DataType
getDirectValue (ExpConstant constant) = return (constantToDataType constant)
getDirectValue (ExpVar ident) = getVal ident
getDirectValue e = lift $ throwError ("Cannot extract value from an expression." ++ (show e))


-- Returns an initialized object of DataType based on the declaration specifiers.
createDefaultValue :: DeclarationSpecifier -> DataType
createDefaultValue (QualType qual specifier) = case qual of
	Const -> (TConst (createDefaultValue (Type specifier)))
createDefaultValue (Type specifier) = case specifier of
	TypeVoid -> TVoid
	TypeChar -> (TChar '\0')
	TypeInt -> (TInt 0)
	TypeDouble -> (TDouble 0.0)
	TypeBool -> (TBool False)
	TypeString -> (TString "")
	TypeClass ident -> (TObject ident)


stripConst :: DeclarationSpecifier -> TypeSpecifier
stripConst (QualType _ specifier) = specifier
stripConst (Type specifier) = specifier


instantiateClass :: Ident -> Ident -> ContExec ParseResult
instantiateClass objName className = do
	(classVars, _) <- getClass className
	mapM_ (\(varName, loc) -> do
		(env, penv, cenv, store) <- lift.lift $ get
		let newLoc = newloc store
		lift.lift $ put (insert (TypeChecking.hashObjMember objName varName) newLoc env,
				penv, cenv, insert newLoc (store ! loc) store)
		) (assocs classVars)
	return ExecOk


allocateDirect :: DirectDeclarator -> DeclarationSpecifier -> ContExec ParseResult
allocateDirect (Name ident) specifier = do
	(env, penv, cenv, state) <- lift.lift $ get
	let loc = newloc state
	lift.lift $ put (insert ident loc env, penv, cenv, insert loc (createDefaultValue specifier) state)
	case stripConst specifier of
		TypeClass className -> instantiateClass ident className
		_ -> return ExecOk


allocateDeclarator :: InitDeclarator -> DeclarationSpecifier -> ContExec ParseResult
allocateDeclarator (PureDecl declarator) specifier = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator specifier
		_ -> lift $ throwError ((shows declarator) " is not a NoPointer")
allocateDeclarator (InitDecl declarator (InitExpr expr)) specifier = do
	allocateDeclarator (PureDecl declarator) specifier
	case declarator of
		NoPointer (Name ident) -> executeExp (ExpAssign (ExpVar ident) Assign expr)
		_ -> lift $ throwError ((shows declarator) " is not a NoPointer")
	return ExecOk
allocateDeclarator declarator _ = lift $ throwError ((shows declarator) 
			" - allocate declarator not defined for this type of declaration.")


getBinaryExpResult :: Exp -> Operator -> Exp -> ContExec Exp
getBinaryExpResult exp1 operator exp2 = do
	res1 <- executeExp exp1
	res2 <- executeExp exp2
	val1 <- getDirectValue res1
	val2 <- getDirectValue res2
	case operator of
		Main.Plus -> return (ExpConstant (dataTypeToConstant (val1 `add` val2)))
		Main.Minus -> return (ExpConstant (dataTypeToConstant (val1 `sub` val2)))
		Main.Times -> return (ExpConstant (dataTypeToConstant (val1 `mul` val2)))
		Main.Div -> if (canDivideBy val2) then
				return (ExpConstant (dataTypeToConstant (val1 `Main.div` val2)))
			else
				lift $ throwError "Division by zero"
		Main.Mod -> if (canDivideBy val2) then
			return (ExpConstant (dataTypeToConstant (val1 `Main.mod` val2)))
			else
				lift $ throwError "Division by zero"
		Main.Or -> return (ExpConstant (dataTypeToConstant (val1 `Main.or` val2)))
		Main.And -> return (ExpConstant (dataTypeToConstant (val1 `Main.and` val2)))
		Main.Eq -> return (ExpConstant (dataTypeToConstant (val1 `Main.eq` val2)))
		Main.Neq -> return (ExpConstant (dataTypeToConstant (val1 `Main.neq` val2)))
		Main.Lt -> return (ExpConstant (dataTypeToConstant (val1 `Main.lt` val2)))
		Main.Gt -> return (ExpConstant (dataTypeToConstant (val1 `Main.gt` val2)))
		Main.Le -> return (ExpConstant (dataTypeToConstant (val1 `Main.le` val2)))
		Main.Ge -> return (ExpConstant (dataTypeToConstant (val1 `Main.ge` val2)))


simplifyAssign :: Exp -> AssignmentOperator -> Exp -> ContExec Exp
simplifyAssign exp1 operator exp2 = executeExp (ExpAssign exp1 Assign simpleExp) where
	simpleExp = case operator of
		AssignAdd -> ExpPlus exp1 exp2
		AssignSub -> ExpMinus exp1 exp2
		AssignMul -> ExpTimes exp1 exp2
		AssignDiv -> ExpDiv exp1 exp2
		AssignMod -> ExpMod exp1 exp2
		AssignAnd -> ExpAnd exp1 exp2
		AssignOr -> ExpOr exp1 exp2


executePostOp :: Exp -> (Exp -> Exp) -> ContExec Exp
executePostOp expr op = do
	res <- executeExp expr
	executeExp (op res)
	return res


executeToDirectVal :: Exp -> ContExec DataType
executeToDirectVal expr = do
	resExp <- executeExp expr
	getDirectValue resExp


executeExp :: Exp -> ContExec Exp
executeExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- executeExp exp1
	res2 <- executeExp exp2
	if (assignmentOperator /= Assign) then
		simplifyAssign res1 assignmentOperator res2
	else do
		let (ExpVar ident) = res1
		(env, penv, cenv, state) <- lift.lift $ get
		val <- do case res2 of 
				-- TODO pointers
				ExpConstant (ExpInt v) -> return (TInt v)
				ExpConstant (ExpBool b) -> return (TBool (b == ValTrue))
				ExpConstant (ExpString s) -> return (TString s)
				ExpVar ident -> getVal ident
		lift.lift $ put (env, penv, cenv, update (\_ -> Just val) (getLoc ident env) state)
		return res2
executeExp (ExpVar ident) = return (ExpVar ident)
executeExp (ExpConstant constant) = return (ExpConstant constant)
executeExp (ExpPlus exp1 exp2) = getBinaryExpResult exp1 Main.Plus exp2
executeExp (ExpMinus exp1 exp2) = getBinaryExpResult exp1 Main.Minus exp2
executeExp (ExpTimes exp1 exp2) = getBinaryExpResult exp1 Main.Times exp2
executeExp (ExpDiv exp1 exp2) = getBinaryExpResult exp1 Main.Div exp2
executeExp (ExpMod exp1 exp2) = getBinaryExpResult exp1 Main.Mod exp2
executeExp (ExpOr exp1 exp2) = getBinaryExpResult exp1 Main.Or exp2
executeExp (ExpAnd exp1 exp2) = getBinaryExpResult exp1 Main.And exp2
executeExp (ExpEq exp1 exp2) = getBinaryExpResult exp1 Main.Eq exp2
executeExp (ExpNeq exp1 exp2) = getBinaryExpResult exp1 Main.Neq exp2
executeExp (ExpLt exp1 exp2) = getBinaryExpResult exp1 Main.Lt exp2
executeExp (ExpGt exp1 exp2) = getBinaryExpResult exp1 Main.Gt exp2
executeExp (ExpLe exp1 exp2) = getBinaryExpResult exp1 Main.Le exp2
executeExp (ExpGe exp1 exp2) = getBinaryExpResult exp1 Main.Ge exp2
executeExp (ExpPreInc expr) = executeExp (ExpAssign expr AssignAdd (ExpConstant (ExpInt 1)))
executeExp (ExpPreDec expr) = executeExp (ExpAssign expr AssignSub (ExpConstant (ExpInt 1)))
executeExp (ExpPostInc expr) = executePostOp expr (\e -> (ExpAssign e AssignAdd (ExpConstant (ExpInt 1))))
executeExp (ExpPostDec expr) = executePostOp expr (\e -> (ExpAssign e AssignSub (ExpConstant (ExpInt 1))))
executeExp (ExpPreOp op expr) = do
	res <- executeExp expr
	val <- getDirectValue res
	case op of
		Negation -> case val of
			TBool b -> return (ExpConstant (ExpBool (if b then ValFalse else ValTrue)))
			_ -> lift $ throwError "Type not supported for negation."
		AbsNBL.Plus -> return res
		Negative -> executeExp (ExpTimes res (ExpConstant (ExpInt (-1))))
		_ -> lift $ throwError "This type of unary operator is not supported yet."
executeExp (ExpFunc expr) = executeExp (ExpFuncArg expr [])
executeExp (ExpFuncArg expr paramExprs) = do
	(ExpVar ident) <- executeExp expr
	(paramIdents, compoundStatement, funcEnv) <- getFunc ident
	(env, penv, cenv, store) <- lift.lift $ get
	lift.lift $ put (funcEnv, penv, cenv, store)
	mapM_ (\(e, i) -> bindParam i e env) (zip paramExprs paramIdents)
	let breakC = getBadBreakCont
	res <- callCC $ \retC -> do
		executeStmt (CompS compoundStatement) retC breakC breakC
		retC (ExpConstant (ExpVoid))
	(_, _, _, newStore) <- lift.lift $ get
	lift.lift $ put (env, penv, cenv, newStore)
	return res
executeExp (ExpClassVar objExp var) = do
	(ExpVar obj) <- executeExp objExp
	return (ExpVar (hashObjMember obj var))
executeExp (ExpClassFunc objExp func) = executeExp (ExpClassFuncArg objExp func [])
executeExp (ExpClassFuncArg objExp func paramExprs) = do
	(ExpVar obj) <- executeExp objExp
	(TObject className) <- getVal obj
	(classVars, classMethods) <- getClass className
	(env, penv, cenv, store) <- lift.lift $ get
	mapM_ (\var -> do
		(currEnv, _, _, store) <- lift.lift $ get
		lift.lift $ put (insert var (env ! (hashObjMember obj var)) env, penv, cenv, store)
		) (keys classVars)
	(env, _, _, _) <- lift.lift $ get
	lift.lift $ put (env, union classMethods penv, cenv, store)
	(paramIdents, compoundStatement, _) <- getFunc func
	mapM_ (\(e, i) -> bindParam i e env) (zip paramExprs paramIdents)
	let breakC = getBadBreakCont
	res <- callCC $ \retC -> do
		executeStmt (CompS compoundStatement) retC breakC breakC
		retC (ExpConstant (ExpVoid))
	(_, _, _, newStore) <- lift.lift $ get
	lift.lift $ put (env, penv, cenv, newStore)
	return res
executeExp e = lift $ throwError ((shows e) " - this type of expression is not supported.")


bindParam :: Ident -> Exp -> Env -> ContExec ParseResult
bindParam ident expr origEnv = do
	(env, penv, cenv, store) <- lift.lift $ get
	lift.lift $ put (origEnv, penv, cenv, store)
	res <- executeExp expr
	(_, penv, cenv, store) <- lift.lift $ get
	lift.lift $ put (origEnv, penv, cenv, store)
	let loc = newloc store
	val <- getDirectValue res
	lift.lift $ put (insert ident loc env, penv, cenv, insert loc val store)
	return ExecOk


evaluateCondition :: Exp -> ContExec Bool
evaluateCondition ctlExp = do
	res <- executeExp ctlExp
	val <- getDirectValue res
	return (case val of
		TBool b -> b
		TInt i -> i /= 0
		_ -> False)


executeControlStmt :: ControlStatement -> ContExp -> ContS -> ContS -> ContExec ParseResult
executeControlStmt (IfThenElse ctlExp s1 s2) retCont breakCont contCont = do
	expTrue <- evaluateCondition ctlExp
	let s = if expTrue then s1 else s2
	executeStmt s retCont breakCont contCont
executeControlStmt (IfThen ctlExp s) retCont breakCont contCont = 
	executeControlStmt (IfThenElse ctlExp s (CompS EmptyComp)) retCont breakCont contCont


executeForInside :: Exp -> Exp -> Stmt -> ContExp -> ContS -> ContS -> ContExec ParseResult
executeForInside ctlExp deltaExp s retCont breakCont contCont = do
	cond <- evaluateCondition ctlExp
	if cond then do
		callCC $ \contC -> do
			executeStmt s retCont breakCont (contC ExecOk)
			breakCont
		executeExp deltaExp
		executeForInside ctlExp deltaExp s retCont breakCont contCont
	else
		breakCont


executeLoopStmt :: LoopStatement -> ContExp -> ContS -> ContS -> ContExec ParseResult
executeLoopStmt (LoopWhile ctlExp s) retCont breakCont contCont = do
	cond <- evaluateCondition ctlExp
	if cond then do
		callCC $ \contC -> do
			executeStmt s retCont breakCont (contC ExecOk)
			breakCont
		executeLoopStmt (LoopWhile ctlExp s) retCont breakCont contCont
	else
		breakCont
executeLoopStmt (LoopDoWhile s ctlExp) retCont breakCont contCont = 
	executeStmt (CompS (StmtComp [s, (LoopS (LoopWhile ctlExp s))])) retCont breakCont contCont
executeLoopStmt (LoopForThree (Declarators specifiers initDeclarators) ctlExpStmt deltaExp s) retCont breakCont contCont = do
	(env, penv, cenv, _) <- lift.lift $ get
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	let expr = case ctlExpStmt of 
		ExtraSemicolon -> ExpConstant (ExpBool ValTrue)	-- For without condition equals while(True)
		HangingExp e -> e
	executeForInside expr deltaExp s retCont breakCont contCont
	(_, _, cenv, store) <- lift.lift $ get
	lift.lift $ put (env, penv, cenv, store)
	return ExecOk
executeLoopStmt (LoopForTwo decl ctlExpStmt s) retCont breakCont contCont = 
		executeLoopStmt (LoopForThree decl ctlExpStmt (ExpConstant (ExpInt 0)) s) retCont breakCont contCont 
		-- Yup, it's a hack


executeStmt :: Stmt -> ContExp -> ContS -> ContS -> ContExec ParseResult
executeStmt (DeclS decl) _ _ _ = executeDecl decl
executeStmt (ExprS (ExtraSemicolon)) _ _ _ = return ExecOk
executeStmt (ExprS (HangingExp exp)) _ _ _ = do
	mem <- lift.lift $ get
	executeExp exp
	return ExecOk
executeStmt (CompS (StmtComp statements)) retCont breakCont contCont = do
	(env, penv, cenv, _) <- lift.lift $ get 
	mapM_ (\stmt -> executeStmt stmt retCont breakCont contCont) statements
	(_, _, _, store) <- lift.lift $ get
	lift.lift $ put (env, penv, cenv, store)
	return ExecOk
executeStmt (CompS EmptyComp) _ _ _ = return ExecOk
executeStmt (CtlS controlStatement) retCont breakCont contCont = 
	executeControlStmt controlStatement retCont breakCont contCont
executeStmt (LoopS loopStatement) retCont _ contCont =
	callCC $ \breakC -> executeLoopStmt loopStatement retCont (breakC ExecOk) contCont
executeStmt (JumpS Break) _ breakCont _ = breakCont
executeStmt (JumpS Continue) _ _ contCont = contCont
executeStmt (JumpS ReturnVoid) retCont _ _ = do
	retCont (ExpConstant (ExpInt 0))
	return ExecOk
executeStmt (JumpS (ReturnVal expr)) retCont _ _ = do
	val <- executeToDirectVal expr
	retCont (ExpConstant (dataTypeToConstant val))	
	return ExecOk
executeStmt (PrintS (Print expr)) _ _ _ = do
	val <- executeToDirectVal expr
	liftIO $ (case val of
		TInt i -> print i
		TDouble d -> print d
		TString s -> print s
		_ -> print "<Unable to print: printing for this type not defined>")
	return ExecOk
executeStmt _ _ _ _ = lift $ throwError "This type of statement is not supported yet."


executeStmtEntry :: Stmt -> ContExec ParseResult
executeStmtEntry stmt = do
	let breakC = getBadBreakCont
	callCC $ \retC -> do
		executeStmt stmt retC breakC breakC
		liftIO $ print "Warning: exiting top level function without using a return."
		return (ExpConstant (ExpVoid))
	return ExecOk


parametersToIdentList :: ParameterDeclarations -> ContExec [Ident]
parametersToIdentList (ParamDecl parameterDeclaration) = do 
	let (TypeAndParam specifiers declarator) = parameterDeclaration
	let (NoPointer (Name ident)) = declarator
	return [ident]
parametersToIdentList (MoreParamDecl paramDecls paramDecl) = do
	res1 <- parametersToIdentList paramDecls
	res2 <- parametersToIdentList (ParamDecl paramDecl)
	return ((head res2) : res1)


memorizeFunc :: Ident -> ([Ident], CompoundStatement) -> ContExec ParseResult
memorizeFunc ident (paramIdents, s) = do
	(env, penv, cenv, store) <- lift.lift $ get
	lift.lift $ put (env, insert ident (paramIdents, s, env) penv, cenv, store)
	return ExecOk 


executeFunctionDeclaration :: Declarator -> CompoundStatement -> ContExec ParseResult
executeFunctionDeclaration (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) compoundStatement = do
	idents <- parametersToIdentList parameterDeclarations
	memorizeFunc ident (idents, compoundStatement)
executeFunctionDeclaration (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement =
	memorizeFunc ident ([], compoundStatement)


executeClassBlockDeclarationMeta :: ClassDecl -> Ident -> ContExec ParseResult
executeClassBlockDeclarationMeta block name = do
	(env, penv, _, _) <- lift.lift $ get
	let decls = case block of
		PublicBlock d -> d
		ProtectedBlock d -> d
	mapM_ (executeDecl) decls
	(newEnv, newPEnv, cenv, _) <- lift.lift $ get 
	let envDiff = newEnv \\ env
	let penvDiff = newPEnv \\ penv
	-- Put any changes to cenv
	mapM_ (\(k, e) -> do
		(curEnv, curPEnv, curCenv, curStore) <- lift.lift $ get
		let (classVars, classFunc) = curCenv ! name
		lift.lift $ put (curEnv, curPEnv, 
				insert name (insert k e classVars, classFunc) curCenv, curStore)) (assocs envDiff)

	mapM_ (\(k, e) -> do
		(curEnv, curPEnv, curCEnv, curStore) <- lift.lift $ get
		let (classVars, classFunc) = curCEnv ! name
		lift.lift $ put (curEnv, curPEnv,
				insert name (classVars, insert k e classFunc) curCEnv, curStore)) (assocs penvDiff)

	(_, _, finalCEnv, store) <- lift.lift $ get
	lift.lift $ put (env, penv, finalCEnv, store)	-- Forget the binding from inside the class.
	return ExecOk


executeDecl :: Decl -> ContExec ParseResult
executeDecl (Func declarationSpecifiers declarator compoundStatement) =
	executeFunctionDeclaration declarator compoundStatement
executeDecl (Declarators specifiers initDeclarators) = do
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	return ExecOk
executeDecl (Class name blocks) = do
	(env, penv, cenv, store) <- lift.lift $ get
	lift.lift $ put (env, penv, insert name (empty, empty) cenv, store)
	mapM_ (\block -> executeClassBlockDeclarationMeta block name) blocks
	return ExecOk


executeExternalDeclaration :: ExternalDeclaration -> ContExec ParseResult
executeExternalDeclaration (Global decl) = executeDecl decl


executeProg :: Prog -> ContExec ParseResult
executeProg (Program externalDeclarations) = do
	mapM_ (executeExternalDeclaration) externalDeclarations
	return ExecOk


run :: String -> IO StateType
run s = do case (pProg (myLexer s)) of
    		Bad err -> do 
    			print ("Parsing error: " ++ err)
    			return (empty, empty, empty, empty)
    		Ok p -> case types p of
    			Left str -> do
    				print ("Typechecking failed: " ++ str)
    				return (empty, empty, empty, empty)
    			Right _ ->	do-- This bit needs a refactor...
    				res <- (runStateT (runExceptT (runContT (executeProg p) 
    						(\_ -> return (empty, empty, empty, empty)))) (empty, empty, empty, empty))
    				case res of
    					((Right _), (e, penv, cenv, store)) -> do
    						let mainFunc = Data.Map.lookup (Ident "main") penv
    						if (isNothing mainFunc) then do
    							print "No main declared."
    							return (e, penv, cenv, store)
    						else do
								let (params, compoundStatement, env) = fromJust mainFunc
								res2 <- (runStateT (runExceptT (runContT (executeStmtEntry (CompS compoundStatement)) 
										(\_ -> return (env, penv, cenv, store)))) (env, penv, cenv, store))
								case res2 of
									((Right _), mem) -> do
										print "Run successful"
										return mem
									((Left str), mem) -> do
										print ("Runtime error: " ++ str)
										return mem
    					((Left str), mem) -> do
    						print ("Runtime error: " ++ str)
    						return mem


main = do
  code <- getContents
  (env, _, _, store) <- run code
  print $ ("Env:", env)
  print $ ("Store:", store)
