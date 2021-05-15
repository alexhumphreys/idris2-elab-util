module Doc.Enum1

import Language.Reflection
import Language.Reflection.Syntax
import Language.Reflection.Types

import Language.JSON

%language ElabReflection

enumDecl1 : (name : String) -> (cons : List String) -> Decl
enumDecl1 name cons = IData EmptyFC Public dat
  where
    enumName : Name
    enumName = UN name
    mkCon : String -> ITy
    mkCon n = MkTy EmptyFC EmptyFC (UN n) (IVar EmptyFC enumName)
    dat : Data
    dat = MkData EmptyFC enumName (IType EmptyFC) [] (map mkCon cons)

export
enumDecl : (name : String) -> (cons : List String) -> Decl
enumDecl name = simpleData Private (UN name) . map mkCon
  where
    mkCon : String -> ITy
    mkCon n = mkTy (UN n) (varStr name)

export
mkEnum : (name : String) -> (cons : List String) -> Elab ()
mkEnum name cons = declare [enumDecl name cons]

%runElab (mkEnum "Gender" ["Female","Male","NonBinary"])

export
Eq Gender where
  Female     == Female     = True
  Male       == Male       = True
  NonBinary  == NonBinary  = True
  _          == _          = False

-- enum2.md
export
eqDecl1 : String -> List String -> List Decl
eqDecl1 enumName cons =
  let functionName = UN $ "impl1Eq" ++ enumName
      function = var functionName
      enum = arg $ varStr enumName
      defClause = function .$ implicitTrue .$ implicitTrue .= `(False)
      conClause = \c => function .$ varStr c .$ varStr c .= `(True)
  in
  [ public' functionName $ enum .-> enum .-> `(Bool)
  , def functionName $ map conClause cons ++ [defClause] ]

export
mkEq1 : String -> List String -> Elab ()
mkEq1 n cons = declare $ eqDecl1 n cons

%runElab (mkEq1 "Gender" ["Female","Male","NonBinary"])

eqTest : impl1EqGender Female Female = True
eqTest = Refl

export
eqInfo : TypeInfo
eqInfo = getInfo "Eq"

export
eqImpl : String -> List String -> List Decl
eqImpl enumName cons =
  let --names
      mkEq = singleCon "Eq"
      eqName = UN "eq"
      functionName = UN $ "implEq" ++ enumName

      --vars
      eq = var eqName
      function = var functionName
      enum = arg $ varStr enumName

      --catchall
      defEq = eq .$ implicitTrue .$ implicitTrue .= `(False)

      --single pattern
      mkC = \x => eq .$ varStr x .$ varStr x .= `(True)

      --implementation of (/=)
      neq = `(\a,b => not $ eq a b)

      --local where block
      impl = local [ private' eqName $ enum .-> enum .-> `(Bool)
                   , def eqName $ map mkC cons ++ [defEq]
                   ] (var mkEq .$ eq .$ neq)
  in
  [ interfaceHint Public functionName (var "Eq" .$ type enum)
  , def functionName [ function .= impl ]
  ]

export
mkEqImpl : String -> List String -> Elab ()
mkEqImpl enumName cons = declare (eqImpl enumName cons)

%runElab (mkEqImpl "Gender" ["Female","Male","NonBinary"])

eqTest2 : (Male == NonBinary) = False
eqTest2 = Refl

eqTest3 : (Male /= NonBinary) = True
eqTest3 = Refl

||| from idris2-lsp
stripNs : Name -> Name
stripNs (NS _ x) = x
stripNs x = x

||| from idris2-lsp
covering
genReadableSym : String -> Elab Name
genReadableSym hint = do
  MN v i <- genSym hint
    | _ => fail "cannot generate readable argument name"
  pure $ UN (v ++ show i)

||| from idris2-lsp
primStr : String -> TTImp
primStr = IPrimVal EmptyFC . Str

||| from idris2-lsp
bindvar : String -> TTImp
bindvar = IBindVar EmptyFC

||| from idris2-lsp
implicit' : TTImp
implicit' = Implicit EmptyFC True

public export
interface FromJSON a where
  fromJSON : JSON -> Maybe a

export
FromJSON Nat where
  fromJSON (JNumber x) = pure (fromInteger $ cast x)
  fromJSON _ = neutral

||| moved from where clause
getArgs : TTImp -> Elab (List (Name, TTImp))
getArgs (IPi _ _ _ (Just n) argTy retTy) = ((n, argTy) ::) <$> getArgs retTy
getArgs (IPi _ _ _ Nothing _ _) = fail $ "All arguments must be explicitly named"
getArgs _ = pure []

||| moved from where clause
genClause : Name -> Name -> Name -> List (Name, TTImp) -> Elab (TTImp)
genClause funName t m xs = do
      let rhs = foldr (\(n, type), acc => let name = primStr $ (show n) in
                                              case type of
                                                   `(Prelude.Types.Maybe _) => `(~acc <*> (pure $ lookup ~name ~(var m) >>= fromJSON))
                                                   _ => `(~acc <*> (lookup ~name ~(var m) >>= fromJSON)))
                      `(pure ~(var t)) xs
      pure (rhs)

logCons : (List (Name, List (Name, TTImp))) -> Elab ()
logCons [] = pure ()
logCons (x :: xs) = do
  more x
  logCons xs
where
  go : List (Name, TTImp) -> Elab ()
  go [] =  pure ()
  go ((n, t) :: ys) = do
    logMsg "" 0 ("Name: " ++ show n)
    logTerm "" 0 "Type" t
    go ys
  more : (Name, List (Name, TTImp)) -> Elab ()
  more (n, xs) = do
    logMsg "" 0 ("name1: " ++ show n)
    go xs

-- attempt JSON
deriveFromJSON : (name : Name) -> Elab ()
deriveFromJSON n =
  do [(n, _)] <- getType n
             | _ => fail "Ambiguous name"
     logMsg "" 0 ("Resolved name: " ++ show n)

     let funName = UN ("fromJSON" ++ show (stripNs n))
     logMsg "" 0 ("funName: " ++ show funName)

     let objName = UN ("__impl_fromJSON" ++ show (stripNs n))
     logMsg "" 0 ("objName: " ++ show objName)

     conNames <- getCons n
     logMsg "" 0 ("Constructors: " ++ show conNames)

     argName <- genReadableSym "arg"
     logMsg "" 0 ("argName: " ++ show argName)

     cons <- for conNames $ \n => do
       [(conName, conImpl)] <- getType n
         | _ => fail $ show n ++ "constructor must be in scope and unique"
       args <- getArgs conImpl
       pure (conName, args)

     logCons cons

     clauses <- traverse (\(cn, as) => genClause funName cn argName (reverse as)) cons
     -- ?jjj
     let name = n
     let clauses = [patClause `(~(var funName) (JObject ~(bindvar $ show argName)))
                              (foldl (\acc, x => `(~x <|> ~acc)) `(Nothing) (clauses))]
     let funClaim = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funName `(JSON -> Maybe ~(var name)))
     let funDecl = IDef EmptyFC funName (clauses ++ [patClause `(~(var funName) ~implicit') `(Nothing)])
     declare [funClaim, funDecl]
     [(ifName, _)] <- getType `{{FromJSON}}
       | _ => fail "FromJSON interface must be in scope and unique"
     [NS _ (DN _ ifCon)] <- getCons ifName
       | _ => fail "Interface constructor error"
     let retty = `(FromJSON ~(var name))
     let objClaim = IClaim EmptyFC MW Export [Hint True, Inline] (MkTy EmptyFC EmptyFC objName retty)
     let objrhs = `(~(var ifCon) ~(var funName))
     let objDecl = IDef EmptyFC objName [(PatClause EmptyFC (var objName) objrhs)]
     declare [objClaim, objDecl]

record Example where
  constructor MkExample
  foo : Maybe Nat

dummy1 : ()
dummy1 = %runElab (deriveFromJSON `{{ Example }})
