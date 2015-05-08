{- Tomasz Zakrzewski, tz336079
 - New Better Language Type Checking
 -}
module TypeChecking (types) where


import LexNBL
import ParNBL
import SkelNBL
import PrintNBL
import AbsNBL
import ErrM


type TypeEval = Maybe Int   -- TODO a monad-based type here just as in the interpreter
					 		-- We need some sort of a map of identifiers to types.


getProgTypes :: Prog -> TypeEval
getProgTypes = undefined


types :: Prog -> Bool
types prog = case getProgTypes prog of
	Just _ -> True
	Nothing -> False


