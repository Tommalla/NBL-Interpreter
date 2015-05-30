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

data ParseResult = ExecOk | Error String
	deriving (Eq)
type Loc = Int
type Env = Map Ident Loc
type Store = Map Loc DataType
type PEnv = Map Ident ([Ident], CompoundStatement, Env)	-- The list is the list of argument names.
type StateType = (Env, PEnv, Store)
type Exec a = ExceptT String (State StateType) a
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


-- TODO move all those to monads?
add :: DataType -> DataType -> DataType
add (TInt a) (TInt b) = TInt (a + b)
add _ _ = undefined


sub :: DataType -> DataType -> DataType
sub (TInt a) (TInt b) = TInt (a - b)
sub _ _ = undefined


mul :: DataType -> DataType -> DataType
mul (TInt a) (TInt b) = TInt (a * b)
mul _ _ = undefined


div :: DataType -> DataType -> DataType
div (TInt a) (TInt b) = TInt (a `Prelude.div` b)
div _ _ = undefined


mod :: DataType -> DataType -> DataType
mod (TInt a) (TInt b) = TInt (a `Prelude.mod` b)
mod _ _ = undefined


or :: DataType -> DataType -> DataType
or (TBool a) (TBool b) = TBool (a || b)
or _ _ = undefined


and :: DataType -> DataType -> DataType
and (TBool a) (TBool b) = TBool (a && b)
and _ _ = undefined


boolOp :: Eq a => a -> (a -> a -> Bool) -> a -> DataType
boolOp a op b = TBool (a `op` b)


eq :: DataType -> DataType -> DataType
eq (TBool a) (TBool b) = boolOp a (==) b
eq (TInt a) (TInt b) = boolOp a (==) b
eq (TDouble a) (TDouble b) = boolOp a (==) b
eq _ _ = undefined


not :: DataType -> DataType
not (TBool b) = TBool (Prelude.not b)
not (TInt i) = TBool (i == 0)
not _ = undefined


neq :: DataType -> DataType -> DataType
neq = Main.eq . Main.not


lt :: DataType -> DataType -> DataType
lt (TInt a) (TInt b) = boolOp a (<) b
lt (TDouble a) (TDouble b) = boolOp a (<) b
lt _ _ = undefined


gt :: DataType -> DataType -> DataType
gt (TInt a) (TInt b) = boolOp a (>) b
gt (TDouble a) (TDouble b) = boolOp a (>) b
gt _ _ = undefined


le :: DataType -> DataType -> DataType
le a b = Main.not (Main.gt a b)


ge :: DataType -> DataType -> DataType
ge a b = Main.not (Main.lt a b)


-- Returns a new location
newloc :: Store -> Loc
newloc memState = (safeMaximum (keys memState)) + 1
	where
		safeMaximum :: [Loc] -> Loc 
		safeMaximum l = if (Prelude.null l) then 0 else maximum l


getLoc :: Ident -> Env -> Loc 
getLoc ident env = env ! ident


getVal :: Ident -> Exec DataType
getVal ident = do
	(env, _, store) <- lift $ get
	return (store ! (getLoc ident env))


constantToDataType :: Constant -> DataType
constantToDataType (ExpChar c) = TChar c
constantToDataType (ExpDouble d) = TDouble d
constantToDataType (ExpInt i) = TInt i
constantToDataType (ExpBool b) = TBool (b == ValTrue)


dataTypeToConstant :: DataType -> Constant
dataTypeToConstant (TChar c) = ExpChar c
dataTypeToConstant (TDouble d) = ExpDouble d
dataTypeToConstant (TInt i) = ExpInt i
dataTypeToConstant (TBool b) = ExpBool (if b then ValTrue else ValFalse)
dataTypeToConstant _ = undefined


-- Extracts the underlying value. Works only for vars and consts.
getDirectValue :: Exp -> Exec DataType
getDirectValue (ExpConstant constant) = return (constantToDataType constant)
getDirectValue (ExpVar ident) = getVal ident
getDirectValue _ = throwError "Cannot extract value from an expression."


-- Returns an initialized object of DataType based on the declaration specifiers.
createDefaultValue :: [DeclarationSpecifier] -> DataType
createDefaultValue (h:t) = if (Prelude.not (Prelude.null t)) then
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


allocateDirect :: DirectDeclarator -> [DeclarationSpecifier] -> Exec ParseResult
allocateDirect (Name ident) specifiers = do
	(env, penv, state) <- lift $ get
	let loc = newloc state
	lift $ put (insert ident loc env, penv, insert loc (createDefaultValue specifiers) state)
	return ExecOk
allocateDirect _ _ = throwError "This type of allocation is not supported yet."


allocateDeclarator :: InitDeclarator -> [DeclarationSpecifier] -> Exec ParseResult
allocateDeclarator (PureDecl declarator) specifiers = do
	case declarator of
		NoPointer directDeclarator -> allocateDirect directDeclarator specifiers
		_ -> throwError "Not a NoPointer"
allocateDeclarator (InitDecl declarator (InitExpr expr)) specifiers = do
	allocateDeclarator (PureDecl declarator) specifiers
	case declarator of
		NoPointer (Name ident) -> executeExp (ExpAssign (ExpVar ident) Assign expr)
		_ -> throwError "Not a NoPointer"
	return ExecOk
allocateDeclarator _ _ = throwError "Allocate declarator not defined for this type of declaration."


canDivideBy :: DataType -> Bool
canDivideBy val = case val of
	TInt 0 -> False
	TDouble 0 -> False
	_ -> True


getBinaryExpResult :: Exp -> Operator -> Exp -> Exec Exp
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
				throwError "Division by zero"
		Main.Mod -> if (canDivideBy val2) then
			return (ExpConstant (dataTypeToConstant (val1 `Main.mod` val2)))
			else
				throwError "Division by zero"
		Main.Or -> return (ExpConstant (dataTypeToConstant (val1 `Main.or` val2)))
		Main.And -> return (ExpConstant (dataTypeToConstant (val1 `Main.and` val2)))
		Main.Eq -> return (ExpConstant (dataTypeToConstant (val1 `Main.eq` val2)))
		Main.Neq -> return (ExpConstant (dataTypeToConstant (val1 `Main.neq` val2)))
		Main.Lt -> return (ExpConstant (dataTypeToConstant (val1 `Main.lt` val2)))
		Main.Gt -> return (ExpConstant (dataTypeToConstant (val1 `Main.gt` val2)))
		Main.Le -> return (ExpConstant (dataTypeToConstant (val1 `Main.le` val2)))
		Main.Ge -> return (ExpConstant (dataTypeToConstant (val1 `Main.ge` val2)))
		-- TODO boolean conditions.
		_ -> throwError "Operator not supported yet,"


simplifyAssign :: Exp -> AssignmentOperator -> Exp -> Exec Exp
simplifyAssign exp1 operator exp2 = executeExp (ExpAssign exp1 Assign simpleExp) where
	simpleExp = case operator of
		AssignAdd -> ExpPlus exp1 exp2
		AssignSub -> ExpMinus exp1 exp2
		AssignMul -> ExpTimes exp1 exp2
		AssignDiv -> ExpDiv exp1 exp2
		AssignMod -> ExpMod exp1 exp2
		AssignAnd -> ExpAnd exp1 exp2
		AssignOr -> ExpOr exp1 exp2


executePostOp :: Exp -> (Exp -> Exp) -> Exec Exp
executePostOp expr op = do
	res <- executeExp expr
	executeExp (op res)
	return res


executeExp :: Exp -> Exec Exp
executeExp (ExpAssign exp1 assignmentOperator exp2) = do
	res1 <- executeExp exp1
	res2 <- executeExp exp2
	if (assignmentOperator /= Assign) then
		simplifyAssign res1 assignmentOperator res2
	else
		case res1 of
			ExpVar ident -> do
					(env, penv, state) <- lift $ get
					let val = case res2 of 
						-- TODO pointers
						ExpConstant (ExpInt v) -> TInt v
						ExpConstant (ExpBool b) -> TBool (b == ValTrue)
						-- FIXME remove this undef. by moving this to a function inside the monad.
						_ -> undefined
					lift $ put (env, penv, update (\_ -> Just val) (getLoc ident env) state)
					return res2
			_ -> throwError "Trying to assign to something that isn't an lvalue!"
		-- TODO handle all sorts of different assignment operators
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
executeExp _ = throwError "This type of expression is not supported yet."


evaluateCondition :: Exp -> Exec Bool
evaluateCondition ctlExp = do
	res <- executeExp ctlExp
	val <- getDirectValue res
	return (case val of
		TBool b -> b
		TInt i -> i /= 0
		_ -> False)


executeControlStmt :: ControlStatement -> Exec ParseResult
executeControlStmt (IfThenElse ctlExp s1 s2) = do
	expTrue <- evaluateCondition ctlExp
	if (expTrue) then
		executeStmt s1
	else
		executeStmt s2
executeControlStmt (IfThen ctlExp s) = executeControlStmt (IfThenElse ctlExp s (CompS EmptyComp))


executeLoopStmt :: LoopStatement -> Exec ParseResult
executeLoopStmt (LoopWhile ctlExp s) = 
	executeStmt (CtlS (IfThen ctlExp (CompS (StmtComp [s, (LoopS (LoopWhile ctlExp s))]))))
executeLoopStmt (LoopDoWhile s ctlExp) = executeStmt (CompS (StmtComp [s, (LoopS (LoopWhile ctlExp s))]))
executeLoopStmt (LoopForThree (Declarators specifiers initDeclarators) ctlExpStmt deltaExp s) = do
	(env, penv, _) <- lift $ get
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	let expr = case ctlExpStmt of 
		ExtraSemicolon -> ExpConstant (ExpBool ValTrue)	-- For without condition equals while(True)
		HangingExp e -> e
	executeLoopStmt (LoopWhile expr (CompS (StmtComp [s, (ExprS (HangingExp deltaExp))])))
	(_, _, store) <- lift $ get
	lift $ put (env, penv, store)
	return ExecOk
executeLoopStmt (LoopForTwo decl ctlExpStmt s) = 
		executeLoopStmt (LoopForThree decl ctlExpStmt (ExpConstant (ExpInt 0)) s) -- Yup, it's a hack


executeStmt :: Stmt -> Exec ParseResult
executeStmt (DeclS (Declarators specifiers initDeclarators)) = do
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	return ExecOk
executeStmt (ExprS (ExtraSemicolon)) = return ExecOk
executeStmt (ExprS (HangingExp exp)) = do
	mem <- lift $ get
	case runState (runExceptT (executeExp exp)) mem of
		(Right _, mem) -> lift $ put mem
		(Left err, _) -> throwError err
	return ExecOk
executeStmt (CompS (StmtComp statements)) = do
	(env, penv, _) <- lift $ get 
	mapM_ (executeStmt) statements
	(_, _, store) <- lift $ get
	lift $ put (env, penv, store)
	return ExecOk
executeStmt (CompS EmptyComp) = return ExecOk
executeStmt (CtlS controlStatement) = executeControlStmt controlStatement
executeStmt (LoopS loopStatement) = executeLoopStmt loopStatement
executeStmt _ = throwError "This type of statement is not supported yet."


executeFunctionDeclaration :: Declarator -> CompoundStatement -> Exec ParseResult
executeFunctionDeclaration (NoPointer (ParamFuncDecl (Name ident) parameterDeclarations)) compoundStatement = 
	throwError "Functions with parameters are not supported yet."
executeFunctionDeclaration (NoPointer (EmptyFuncDecl (Name ident))) compoundStatement = do
	(env, penv, store) <- lift $ get
	lift $ put (env, insert ident ([], compoundStatement, env) penv, store)
	return ExecOk
executeFunctionDeclaration declarator _ = throwError "Malformed function declaration. "


executeExternalDeclaration :: ExternalDeclaration -> Exec ParseResult
executeExternalDeclaration (Func declarationSpecifiers declarator compoundStatement) =
	executeFunctionDeclaration declarator compoundStatement
executeExternalDeclaration (Global (Declarators specifiers initDeclarators)) = do
	mapM_ (\initDeclarator -> allocateDeclarator initDeclarator specifiers) initDeclarators
	return ExecOk 


executeProg :: Prog -> Exec ParseResult
executeProg (Program externalDeclarations) = do
	mapM_ (executeExternalDeclaration) externalDeclarations
	return ExecOk


run :: String -> (String, StateType)
run s = case pProg (myLexer s) of
    Bad err -> ("Parsing error: " ++ err, (empty, empty, empty))
    Ok p -> 
    	case types p of
    		Left str -> ("Typechecking failed: " ++ str, (empty, empty, empty))
    		Right _ ->	-- This bit needs a refactor...
    			case (runState (runExceptT (executeProg p)) (empty, empty, empty)) of
    				((Right _), (e, penv, store)) -> 
    					let mainFunc = Data.Map.lookup (Ident "main") penv in
    						if (isNothing mainFunc) then ("No main declared.", (e, penv, store)) else
								let (params, compoundStatement, env) = fromJust mainFunc in
									case (runState (runExceptT (
												executeStmt (CompS compoundStatement))) (env, penv, store)) of
										((Right _), mem) -> ("Run successful", mem)
										((Left str), mem) -> ("Runtime error: " ++ str, mem)
    				((Left str), mem) -> ("Runtime error: " ++ str, mem)


main = do
  code <- getContents
  let (out, (env, _, store)) = run code
  print $ out 
  print $ ("Env:", env)
  print $ ("Store:", store)
 