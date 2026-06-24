||| Helpers for locating type-tests in source code.
module TTest.Locate

import Core.Name.Scoped
import Core.TT.Binder
import Core.TT.Primitive
import Core.TT.Term

import TTImp.TTImp

typeOf : {vars : _} -> Term vars -> Maybe RawImp
typeOf (Ref fc nt name) = Just (IVar fc name)
typeOf (Meta fc n i ts) = Nothing
typeOf (Bind fc x b scope) = Nothing
typeOf (TType fc n) = Nothing
typeOf (Local fc isLet idx p) = Nothing
typeOf (App fc fn arg) = Nothing
typeOf (As fc side as pat) = Nothing
typeOf (TDelayed fc lz t) = Nothing
typeOf (TDelay fc lz ty arg) = Nothing
typeOf (TForce fc lz t) = Nothing
typeOf (PrimVal fc constant@(PrT _)) = Just (IPrimVal fc constant)
typeOf (PrimVal fc _) = Nothing
typeOf (Erased fc why) = Nothing

export
findWithin : {vars : _} -> (target : Name) -> (ty : Term vars) -> Maybe (List RawImp)
findWithin t (Ref fc nt name) = if t == name then Just [] else Nothing
findWithin t (Bind fc x (Let fc1 rig val ty) scope) = findWithin t scope
findWithin t (Bind fc x (Pi fc1 rig pinfo ty) scope) = 
  case typeOf ty of
       Just x => (x ::) <$> findWithin t scope
       Nothing => findWithin t scope
findWithin t (App fc fn arg) = findWithin t fn
findWithin _ _ = Nothing

