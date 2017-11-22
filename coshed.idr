import Data.List
import Data.Vect
import Data.So

%default total
%access public export

--------------------------------------------------------------------------
-- Universes
--------------------------------------------------------------------------
data CryptTy = AES | RC4 -- | ElGamal | RSA | ...

||| PCI refers to the schema : Prewatermark -> Crypt -> Insert

data WmTy = GIG | WIT | PCI

data Ty   = BOOL | NAT | TEXT | WATERMARK WmTy Ty | CHAR | IMAGE
          | CRYPT CryptTy Ty | DATE | PRE_WATERMARK WmTy Ty


data Entity = Genetician | T3rdP | Cloud

--Entity : Type
--Entity = (Env n,EntityTy)          

REQUEST : Type
REQUEST = String 

                
interpTy : Ty -> Type
interpTy BOOL  = Bool
interpTy NAT   = Nat
interpTy CHAR  = Char
interpTy TEXT  = String
interpTy DATE  = String
interpTy IMAGE = Vect 16 (Vect 16 Nat)
interpTy (CRYPT _ _) = String
-- type de la donnée ne devrait pas changer en la tatouant          
interpTy (WATERMARK wms ty) = (interpTy ty) 
-- type de la donnée ne devrait pas changer en la tatouant         
interpTy (PRE_WATERMARK wms ty) = (interpTy ty) 



Attribute : Type
Attribute =  (String, Ty)
Schema : Type
Schema = List Attribute

Env : Nat -> Type
Env n = Vect (S n) Schema

Key : Type
Key = String

data Key_Wat = K_PRE | K_Wat

--------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------

Eq CryptTy where
     AES == AES = True
     RC4 == RC4 = True
     _   == _   = False

 
Eq WmTy where 
  WIT  ==  WIT   = True 
  GIG ==  GIG  = True
  PCI ==  PCI  = True
  _   ==  _    = False


Eq Ty where 
   BOOL                    == BOOL                   = True
   NAT                     == NAT                    = True
   TEXT                    == TEXT                   = True 
   IMAGE                   == IMAGE                  = True
   CHAR                    == CHAR                   = True  
   DATE                    == DATE                   = True
   (WATERMARK x y)         == (WATERMARK z t)        = x==z && y==t
   (PRE_WATERMARK x y)     == (PRE_WATERMARK z t)    = x==z && y==t
   (CRYPT x y)             == (CRYPT  z t)           = x==z && y==t
   _                       == _                      = False     


Eq Entity where 
  Genetician == Genetician = True
  T3rdP      == T3rdP      = True
  Cloud      == Cloud      = True
  _          == _          = False 
--implementation Prelude.Interfaces.Eq (WATERMARK TEXT) where   
--      Wm TEXT == Wm TEXT = True
--      Wm TEXT == _       = False
   
   

--------------------------------------------------------------------------
-- Boolean tests to use in proofs
-------------------------------------------------------------------------- 
-- add this later :   {auto p : So (elem oa schema)} 
||| it uses isInEnv (Ronan's func) to proof that @oa is in @env
||| here it is 

-- maybe later use a predicate istead of So (IsInEnv ...)

isInEnv : (a : Attribute) -> (env : Env n) -> Bool
isInEnv a env = any (elem a) env

-- this function is used to guarantee that every data intended to be prewatermarked  is raw. (not watermarked nor crypted).
 

isRawType : Ty -> Bool
isRawType NAT  = True
isRawType CHAR = True
isRawType TEXT = True
isRawType BOOL = True
isRawType DATE = True
isRawType _    = False

isEncrypted : Ty -> Bool
isEncrypted (CRYPT _ _)         = True                  
isEncrypted (WATERMARK _ t)     = isEncrypted t
isEncrypted (PRE_WATERMARK _ t) = isEncrypted t
isEncrypted _                   = False


  
-------------------------------------------------------
-- Ronan's copied functions 
------------------------------------------------------- 
data Inc : (xs : Schema) -> (ys : Schema) -> Type where
    
    Stop : {auto p : Elem x ys} -> Inc [x] ys
    
    Pop  : Inc xs ys -> {auto p : Elem x ys} -> Inc (x :: xs) ys
    
makeId : (Id : Attribute) -> Env n -> Env n 
makeId Id env = map (\s => if (not (elem Id s)) then (Id::s) else s) env  

fragSchema : (δ : Schema) -> (Δ : Schema) -> (Id : Attribute) -> Env 1
fragSchema δ Δ Id = let Δl = the (Schema) (intersect δ Δ)
                        Δr = nub (Δ \\ δ)
                    in makeId Id [Δl,Δr] 
    

fragEnv : (δ : Schema) -> (Id : Attribute) -> (env : Env n) -> 
          {auto p : Inc δ (last env)} ->
          Env (S n)
fragEnv δ Id env {n} =  let  Δs  = init env
                             Δ   = last env
                             lΔ  = fragSchema δ Δ Id
                             --Δl  = the (Schema) (intersect δ Δ) --++ [Id])
                             --Δr  = nub (Δ \\ δ) --++ [Id])
                             res = (Δs ++ lΔ )
                        --in res     
                        in rewrite sym (plusTwoSucSuc n) in  res
                        
    where
     --a gentle proof
    plusTwoSucSuc : (n : Nat) -> n + 2 = S (S n)
    plusTwoSucSuc Z     = Refl   
    plusTwoSucSuc (S k) = let inductHypo = plusTwoSucSuc k
                          in cong inductHypo {f=S}

    

       
---------------------------------------------------------
-- End Ronan's copied functions 
--------------------------------------------------------- 


watEnv : (a : Attribute) -> WmTy -> (env :Env n) -> 
         {auto p : So (isInEnv a env)} -> Env n
watEnv  a wms env  =  map (\s => if (elem a s) then replaceOn a (fst a,
                       WATERMARK wms (snd a)) s else s) env 

preWatEnv : (a : Attribute) -> WmTy -> (env :Env n) -> 
            {auto p : So (isInEnv a env)} -> Env n
preWatEnv a wms env  =  map (\s => if (elem a s) then replaceOn a (fst a,                                 PRE_WATERMARK wms (snd a)) s else s) env 

cryptEnv : (oa : Attribute) -> CryptTy -> (env:Env n) -> 
           {auto p : So (isInEnv oa env)} -> Env n
cryptEnv oa c env  =  map (\s => if (elem oa s) then replaceOn oa (fst oa
                                , CRYPT c (snd oa)) s else s) env 
                                
||| forces utilization of PCI watermarking scheme                                
                                
preWatEnvPCI : (a : Attribute) -> (env:Env n) ->
               {auto p1 : So (isInEnv a env)} ->  
               Env n     
preWatEnvPCI a env = preWatEnv a Main.PCI env  
                                 
||| forces utilization of RC4 encryption scheme and verifies that @a 
||| is already prewatermarked 

cryptEnvPCI : (a : Attribute) -> (env:Env n) ->
              {auto p1 : So (isInEnv a env)} ->
              {default Refl p2 : snd a = PRE_WATERMARK PCI t} ->
              Env n
cryptEnvPCI a env = cryptEnv a Main.RC4 env  
            
||| forces utilization of PCI and verifies that @a was prewatermarked 
||| and encrypted              

insertEnvPCI : (a : Attribute) -> (env:Env n) ->
               {default Oh p1 : So (isInEnv a env)} ->
               {default Refl p2 : snd a = CRYPT RC4 (PRE_WATERMARK PCI t)} ->
               Env n
insertEnvPCI a env = watEnv a  Main.PCI env     

-------------------------------------------------------------------------------
-- Pred +  Query
-------------------------------------------------------------------------------
using (Δ : Schema, Δ' : Schema, δ : Schema, δ' : Schema,
       Δs : Vect n Schema, e1 : Entity, e2 : Entity, e3 : Entity,
       env : Env n , env' : Env m , env'' : Env k) {
namespace query

 data Pred : (Δ : Schema) -> Type where
    ||| Logical AND
    AND      : Pred Δ -> Pred Δ -> Pred Δ
    ||| Logical OR
    OR       : Pred Δ  -> Pred Δ  -> Pred Δ
    ||| Test that values of `a` contains `pat`.
    |||
    ||| @ p proof that `a` is an attribute of `Δ`.
    Like     : (a : Attribute) -> (pat : String) ->
               {auto p : Elem a Δ} ->
               -- Like (snd a) => -- to add the like interface
               Pred Δ
    ||| Test that values of `a` are a next week date.
    |||
    ||| @ p1 proof that `a` is a `DATE`.
    ||| @ p2 proof that `a` is an attribute of `Δ`.
    NextWeek : (a : Attribute) ->
               {default Refl p1 : DATE = (snd a)} ->
               {auto p2 : Elem a Δ} ->
               Pred Δ
    ||| Test that values of `a` are equals to `v`.
    |||
    ||| @ v a value with the idris type of `a`.
    ||| @ p proof that `a` is an attribute of `Δ`.
    Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
               {auto p : Elem a Δ} -> Pred Δ
               --Equal (snd a) => -- Note the presence of our interface
               --Eq (interpTy (snd a))   => -- For debugging only,
               --Show (interpTy (snd a)) => -- not required
    IN       : (a : Attribute) -> (s : Schema) -> {auto p1 : So ((length s) == 1)} ->
               {auto p2 : Elem a Δ} -> Pred Δ
             
||| predicate that contains information for reading the tattoo
--|||
--|||  @ t secret threshold for feature selection  
--|||  @ s seed value for watermark string generation
--|||  @ k secret key of number of characters and symbols for digram matrix
--|||  @ r secret number of rounds 

 data ReadM : WmTy -> Type where
       RGIG : (k:Key) -> (t:Nat) -> (s:List String) -> (r:Nat) -> ReadM GIG
       RPCI : Key -> Key -> ReadM PCI
      
||| predicate that contains information for decryption     
      
 data DecryptI : CryptTy -> Type where
   AESD     : Key -> DecryptI AES
   RC4D     : Key -> DecryptI RC4
   
--------------------------------------------------------------------------
-- Query ADT  ------------  -----------  -------------     ------------
-------------------------------------------------------------------------- 

 data Query : Schema -> Type where

       ReadW   : (a : Attribute) -> (info : ReadM GIG) -> 
                 {default Refl p1 : (snd a) = (WATERMARK GIG t)} ->
                 Query Δ ->
                 {auto p2 :Data.List.Elem a Δ} -> 
                 Query ((replaceOn a (fst a, t) Δ)++[MyTattoo])
                 
       Project : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
                 Query δ
       Product : Query Δ -> Query Δ' -> Query (Δ ++ Δ')
       NJoin   : Query Δ -> Query Δ' ->
                 {default Oh p : So (hasAny Δ Δ')} ->
                 Query (nub (Δ ++ Δ'))
     
       Count   : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
                 Query (δ ++ [Cnt])
      
       Select  : (p : Pred Δ) -> Query Δ -> Query Δ
     
       Decrypt : (a : Attribute) -> (d : DecryptI c) ->
                 {default Refl p1 : (CRYPT c t) = (snd a)} ->
                
                 {auto p2 : Elem a Δ} ->
                 Query Δ -> Query (replaceOn a (fst a, t) Δ)
      
       Defrag : (q1 : Query δ) -> (q2 : Query δ') ->
                 Query (nub (δ ++ δ'))
                

       DecryptPCI : (a : Attribute) -> (info : DecryptI RC4) -> 
                    {default Oh p1 : So (isEncrypted (snd a))} ->
                    {auto p2 : Elem a Δ} ->
                    Query Δ' ->
                    {default Refl p3 : Δ = Δ'} ->
                    Query 
                    (replaceOn a (fst a,WATERMARK PCI (PRE_WATERMARK PCI IMAGE)) Δ)
       Fe    : (a : Attribute) -> (info : ReadM PCI) -> 
               {default Refl p1 : (snd a) = WATERMARK PCI (CRYPT RC4 
               (PRE_WATERMARK PCI IMAGE))} ->
               Query Δ ->
               {auto p2 : Data.List.Elem a Δ} -> Query (Δ++[MyTattoo])
        
       Fs    : (a : Attribute) -> (info : ReadM PCI) -> 
               {default Refl p1 : (snd a) = WATERMARK PCI (PRE_WATERMARK PCI IMAGE)} ->
               Query Δ ->
               {auto p2 : Data.List.Elem a Δ} -> Query (Δ++[MyTattoo])           
              
       ToQuery  : (Δ : Schema) -> Query Δ 
       Limit : (rownum : Integer) -> Query Δ -> Query Δ                                  
-------------------------------------------------------------------------------
-- Privy
-------------------------------------------------------------------------------

namespace privy      

 data Privy : (env0 : Env n) -> (env1 : Env m) -> (Δ : Schema) -> Type where
    
   Wat          : (a : Attribute)-> 
                  {auto p1 : So (isRawType (snd a))} ->
                  {auto p2 : So (isInEnv a env)} -> 
                  Privy env (watEnv a GIG env) []
             
   PreWatPCI    : (a : Attribute) -> 
                  {auto p1 : So (isInEnv a env)} ->  
                  --{auto p2 : So (isRawType (snd a))} ->        
                  Privy env (preWatEnvPCI a env {p1=p1}) []
            
   CryptPCI     : (a : Attribute) -> 
                  {auto p1 : So (isInEnv a env)} ->
                  {default Refl p2 : snd a = PRE_WATERMARK PCI t} ->
                  Privy env (cryptEnvPCI a env {p1=p1} {p2=p2}) []
            
   InsertPCI    : (a : Attribute) -> 
                  {auto p1 : So (isInEnv a env)} ->
                  {default Refl p2 : snd a = CRYPT RC4 (PRE_WATERMARK PCI t)} ->
                  Privy env (insertEnvPCI a env {p1=p1} {p2=p2}) []  
                  
   Crypt        : (a : Attribute) -> (c : CryptTy) ->
                  {auto p : So (isInEnv a env)} ->
                   Privy env (cryptEnv a c env) []
                     
   Frag         : (δ : Schema) -> (Id : Attribute) ->
                  {auto p : Inc δ (last env)} ->
                  Privy env (fragEnv δ Id env) []   
                          
   Query        : {env : Env n} ->
                  (fId : Fin (S n)) -> (q : Query (index fId env) ->
                   Query Δ') -> Privy env env Δ'   
                 
                  
   (>>=)        : Privy  env env' δ ->
                  (Query δ -> Privy env' env'' δ') ->
                  Privy env env'' δ'
                    
   Return       : Query δ -> Privy env env δ   
  -- Extract      :  Privy env env δ -> Query δ    

-----------------------------------------------------------------------------------
-- GeneticQuery ADT 
-----------------------------------------------------------------------------------
 
||| complete this function's definition

basicType : Ty -> Ty
basicType  NAT                     =  NAT
basicType  TEXT                    =  TEXT
basicType  BOOL                    =  BOOL
basicType  CHAR                    =  CHAR
basicType  DATE                    =  DATE
basicType  IMAGE                   =  IMAGE
basicType (CRYPT _ t)              = basicType t
basicType (WATERMARK _ t)          = basicType t
basicType (PRE_WATERMARK _ t)      = basicType t


extractData : {Δ:Schema}   -> Query Δ -> Schema
extractData (Project s _)       = s                                           
extractData (Count s _)         = s ++ [Cnt]
extractData (Limit _ d)         = extractData d                                      
extractData (Product d d')      = (extractData d) ++ (extractData d')
extractData (Select _ d)        = extractData d    
extractData (NJoin d d')        = nub (extractData d ++ extractData d')  
extractData (Defrag d d')       = (nub (extractData d ++ extractData d'))
extractData (ReadW _ _ d)       = extractData d ++ [MyTattoo]  
extractData (Fe _ _ d)          = extractData d ++ [MyTattoo]  
extractData (Fs _ _ d)          = extractData d ++ [MyTattoo]  
extractData (Decrypt a _ d)     = replaceOn a (fst a, basicType (snd a)) (extractData d)
extractData (DecryptPCI a _ d') = replaceOn a (fst a, WATERMARK PCI (PRE_WATERMARK PCI IMAGE)) (extractData d')      
extractData (ToQuery s)         = s   
         
executeRequest  :  (executer : Entity) -> 
                   {auto p : So (executer == T3rdP || executer == Cloud)} ->
                   (request : List (Query Δ)) -> Schema
executeRequest _ ld = foldl union [] (map (extractData) ld)                       
                                                           
                                                                                
----------------------------------------------------
                                                                 
namespace geneticquery
 
 
 data GeneticQuery :   Schema -> Type where
 
  SendRequest    :  (sender : Entity) -> (Entity,List (Query Δ)) -> GeneticQuery Δ 
                    
  SendData       :  (sender : Entity) -> (couple : (Entity,Schema)) -> 
                     GeneticQuery (snd couple)
             
  Compute        : (processor : Entity) -> 
                   {auto p : So (processor == Genetician || processor == T3rdP)} ->
                   Query Δ -> GeneticQuery Δ
                   
  AskMCData      : (requester : Entity) -> (Entity,Query Δ ) -> GeneticQuery Δ 
                  
  ProvideMCData  : (sender : Entity) -> (Entity,Query Δ) -> GeneticQuery Δ
                   
  (>>=)          : GeneticQuery δ -> (Query δ -> GeneticQuery δ') -> GeneticQuery δ'
                   
  ReturnResults  : (sender : Entity) -> (Entity,GeneticQuery δ) -> GeneticQuery δ 
                   
                   

--------------------------------------------------------------------------
-- Privy sugar  ------------  -----------  -------------      ------------
-------------------------------------------------------------------------- 
namespace sugar

 wat : (a : Attribute) -> 
       {auto p1 : So (isRawType (snd a))} ->
       {auto p2 : So (isInEnv a env)} -> 
       Privy env (watEnv a GIG env) []
 wat a {p1} {p2} = Wat a {p1=p1} {p2=p2}    


-- drop the implicit first argument later, it's just for testing
-- I think no need to test whether given @a is raw or not, as a developer
-- would never try to preWat an attribute which type is CRYPT or ?!! really !
-- so what's the goal !!! 

 preWatPCI : (a : Attribute) -> 
             {auto p1 : So (isInEnv a env)} ->  
             --{auto p2 : So (isRawType (snd a))} ->        
             Privy env (preWatEnvPCI a env) [] 
 preWatPCI  = PreWatPCI

            
 cryptPCI : (a : Attribute) -> 
            {auto p1 : So (isInEnv a env)} ->
            {default Refl p2 : snd a = PRE_WATERMARK PCI t} ->
            Privy env (cryptEnvPCI a env {p1=p1} {p2=p2}) []           
 cryptPCI = CryptPCI                                                


 insertPCI : (a : Attribute) -> 
             {auto  p1 : So (isInEnv a env)} ->
             {default Refl p2 : snd a = CRYPT RC4 (PRE_WATERMARK PCI t)} ->
             Privy env (insertEnvPCI a env {p1=p1} {p2=p2}) []  
 insertPCI = InsertPCI            

 crypt : (a : Attribute) -> (c : CryptTy) ->
         {auto  p1 : So (isInEnv a env)}  -> Privy env (cryptEnv a c env) []
 crypt = Crypt

 frag : (δ : Schema) -> (Id : Attribute) -> {auto p : Inc δ (last env)} -> 
        Privy env (fragEnv δ Id env) []
 frag = Frag

 query : {env : Env n} ->
         (fId : Fin (S n)) -> (q : Query (index fId env) -> Query Δ') ->
          Privy env env Δ'
 query = Query

 return : Query δ -> Privy env env δ
 return = Return

  


 |||  function that does all of the three steps in PCI


--watPCI : (a : Attribute ) -> (env : Env n)  ->
--         Env n
        
--watPCI a env  =  let env1 = preWatEnvPCI a env 
--                     env2 = cryptEnvPCI (fst a,  PRE_WATERMARK PCI (snd a)) env1  
--                     env3 = insertEnvPCI (fst a, CRYPT RC4 (PRE_WATERMARK PCI (snd a)))  env2
--                 in   env2   

 --insertEnvPCI (fst a, CRYPT RC4 (PRE_WATERMARK PCI (snd a))) 
   --             $ cryptEnvPCI (fst a,  PRE_WATERMARK PCI (snd a)) 
     --           $ preWatEnvPCI a env 
                
--------------------------------------------------------------------------
-- pred and Query sugar  ------------  -----------  -------------      ---
-------------------------------------------------------------------------- 

-- Predicate sugar

  -- export
 like : (a : Attribute) -> String -> {auto p : Elem a Δ} ->
        Pred Δ
 like = Like

  -- export
 (&&) : Pred Δ -> Pred Δ -> Pred Δ
 (&&) = AND

  -- export
 (||) : Pred Δ -> Pred Δ -> Pred Δ
 (||) = OR

  -- export
 (==) : (a : Attribute) -> (v : interpTy (snd a)) ->
        {auto p : Elem a Δ} ->
       --Equal (snd a) =>
       --Eq (interpTy (snd a))   =>
       --Show (interpTy (snd a)) =>
        Pred Δ
 (==) = Equal

  -- export
 nextWeek : (a : Attribute) -> {default Refl p1 : DATE = (snd a)} ->
            {auto p2 : Elem a Δ} -> Pred Δ
 nextWeek = NextWeek

-------------------------------------------------------- Query sugar

 π : (δ : Schema) -> Query Δ -> {auto p :Inc δ Δ} -> Query δ
 π = Project

-- export
 count : (δ : Schema) -> Query Δ -> {auto p : Inc δ Δ} ->
         Query (δ ++ [Cnt])
 count = Count
-- export
 σ : Pred Δ -> Query Δ' ->
      -- XXX: Instruct the unifyier to infer the Δ from Δ'
     {default Refl p : Δ = Δ'} -> Query Δ
 σ f q {p=Refl} = Select f q

  -- export
 decrypt : (a : Attribute) -> (d : DecryptI c) ->
          --{default Oh p1 : So (isEncrypted (snd a))} ->
           {default Refl p1 : (CRYPT c t) = (snd a)} ->
           {auto p2 : Elem a Δ} ->
           Query Δ' ->
           {default Refl p3 : Δ = Δ'} ->
           Query (replaceOn a (fst a, t) Δ)
 decrypt a d q {p1} {p2} {p3=Refl} = Decrypt a d q {p1=p1} {p2=p2}


  -- export
 defrag : (q1 : Query δ) -> (q2 : Query δ') ->
           -- {auto p : So (countLaw q1 q2)} ->
          Query (nub (δ ++ δ'))
 defrag = Defrag

 readW  : (a : Attribute) -> (info : ReadM GIG) -> 
          {default Refl p1 : (snd a) = (WATERMARK GIG t)} ->
          {auto p2 :Data.List.Elem a Δ} ->
          Query Δ ->
          Query ((replaceOn a (fst a, t) Δ)++[MyTattoo])

 readW a info q {p1} {p2} = ReadW a info q {p1} {p2}


 decryptPCI : (a : Attribute) -> (info : DecryptI RC4) -> 
              {default Oh p1 : So (isEncrypted (snd a))} ->
              {auto p2 : Elem a Δ} ->
              Query Δ' ->
             {default Refl p3 : Δ = Δ'} ->
             Query 
             (replaceOn a (fst a,WATERMARK PCI (PRE_WATERMARK PCI IMAGE)) Δ)
 decryptPCI a d q {p1} {p2} {p3=Refl} = DecryptPCI a d q {p1=p1} {p2=p2} 
     
              
 fe    : (a : Attribute) -> (info : ReadM PCI) -> 
         {default Refl p1 : (snd a) =  WATERMARK PCI (CRYPT RC4 
         (PRE_WATERMARK PCI IMAGE))} ->
         Query Δ ->
         {auto p2 : Data.List.Elem a Δ} -> Query (Δ++[MyTattoo])
 fe  a info q {p1} {p2}  = Fe a info q {p1=p1} {p2=p2}          
        
 fs    : (a : Attribute) -> (info : ReadM PCI) -> 
         {default Refl p1 : (snd a) = WATERMARK PCI (PRE_WATERMARK PCI IMAGE)} ->
         Query Δ ->
         {auto p2 : Data.List.Elem a Δ} -> Query (Δ++[MyTattoo])  
 fs a info q {p1} {p2}   = Fs a info q {p1=p1} {p2=p2}
 
 toQuery : (Δ : Schema) -> Query Δ
 toQuery = ToQuery

}
--------------------------------------------------------------------------
-- Application, trusted party application
-------------------------------------------------------------------------- 

Radiography : Attribute 
Radiography = ("radiography", IMAGE)

ZIP : Attribute
ZIP = ("ZIP code",NAT)

Age : Attribute
Age = ("Age", NAT)

Gender : Attribute
Gender = ("gender",TEXT)

Disease : Attribute
Disease = ("disease",TEXT)

CaseCtrl : Attribute
CaseCtrl = ("case/control",BOOL)

SubjectId : Attribute
SubjectId = ("ID_SUB", TEXT)

Id_control : Attribute
Id_control = ("ID_CON", TEXT)

Code_Huntington : String 
Code_Huntington = "TG76JU"

subject : Schema
subject = [SubjectId,ZIP,Age,Gender,CaseCtrl]

Variant : Attribute
Variant = ("VARIANT", CHAR)

TypeVar : Attribute
TypeVar = ("TYPE_VARIANT", TEXT)

VariantE : Attribute
VariantE = ("VARIANT", CRYPT AES CHAR)

VariantW : Attribute
VariantW = ("VARIANT", WATERMARK GIG CHAR)

TypeVarE : Attribute
TypeVarE = ("TYPE_VARIANT", CRYPT AES TEXT)

TypeVarW : Attribute
TypeVarW = ("TYPE_VARIANT", WATERMARK GIG TEXT)

VariantWE     : Attribute
VariantWE     = ("VARIANT",  (CRYPT AES (WATERMARK GIG CHAR)))

TypeVarWE : Attribute 
TypeVarWE = ("TYPE_VARIANT", (CRYPT AES (WATERMARK GIG TEXT)))

RadiographyP : Attribute
RadiographyP = ("radiography", PRE_WATERMARK PCI IMAGE)

RadiographyPC : Attribute
RadiographyPC = ("radiography",  CRYPT RC4 (PRE_WATERMARK PCI IMAGE))

RadiographyPCI : Attribute
RadiographyPCI = ("radiography", WATERMARK PCI ( CRYPT RC4 (PRE_WATERMARK PCI IMAGE)))

RadiographyPW : Attribute
RadiographyPW = ("radiography", WATERMARK PCI (PRE_WATERMARK PCI IMAGE))

position : Attribute
position = ("POS", NAT)

subject_vcf : Schema
subject_vcf = [SubjectId, Variant, TypeVar, position]

CONTROL : Integer
CONTROL = 1000

CASE : Integer
CASE = 10000


LocalEnv : Env 1
LocalEnv = [subject_vcf,subject]

SafeTPEnv : Env 2
SafeTPEnv = [[SubjectId,VariantWE, TypeVarWE,position],
                          [SubjectId,ZIP,Gender],[SubjectId,Age,CaseCtrl]]

SafeTPEnv' : Env 2           
SafeTPEnv' = fragEnv [ZIP,Gender] SubjectId 
                          --$ insertEnvPCI RadiographyPC
                          --$ cryptEnvPCI RadiographyP
                          --$ preWatEnvPCI Radiography
                          $ cryptEnv (fst TypeVar,WATERMARK GIG 
                                     (snd TypeVar)) AES 
                          $ cryptEnv (fst Variant,WATERMARK GIG (snd Variant)) AES
                          $ watEnv TypeVar GIG
                          $ watEnv Variant GIG LocalEnv



leftCloudEnv : Env 0
leftCloudEnv = [index 1 SafeTPEnv']

rightCloudEnv : Env 1
rightCloudEnv = [index 0 SafeTPEnv',  index 2 SafeTPEnv']

leftCloudTab : Schema
leftCloudTab = index 1 SafeTPEnv'

rightCloudTab1 : Schema
rightCloudTab1 = index 0 SafeTPEnv'

rightCloudTab2 : Schema
rightCloudTab2 = index 2 SafeTPEnv'
-------------------------------------------- Spécification de l'environnement

specTPEnv'' : Privy LocalEnv  SafeTPEnv' []
specTPEnv'' = do frag [ZIP,Gender] SubjectId; 
                 wat Variant;
                 wat TypeVar;
                 crypt (fst Variant,WATERMARK GIG (snd Variant)) AES;  
                 crypt (fst TypeVar,WATERMARK GIG (snd TypeVar)) AES;
-- ill-typed-env
                                                        
--specTPEnv''' : Privy LocalEnv  SafeTPEnv' []
--specTPEnv''' = do frag [ZIP,Gender] SubjectId; 
--                  crypt Variant AES;  
--                  wat (fst Variant,CRYPT AES (snd Variant));
--                  wat TypeVar;
--                  crypt (fst TypeVar,WATERMARK GIG (snd TypeVar)) AES;  
                            
-------------------------------------------------------------------------
-- 
-------------------------------------------------------------------------        

||| import genetic data of one subject (the 1st) with Radiography
||| Query Type


request2 : String
request2 = "SELECT Age, ZIP WHERE SubjectId=id1 "

request3 : String
request3 = "get plain data !"

G1 : Entity
G1 = Genetician

G2 : Entity
G2 = Genetician

TTP : Entity
TTP = T3rdP

LeftCloud : Entity
LeftCloud = Cloud

RightCloud : Entity
RightCloud = Cloud

Q1 : Query [SubjectId,ZIP,Gender]
Q1 = π [SubjectId,ZIP,Gender]
   $ σ (Gender == "male") (toQuery leftCloudTab); 
      
IDs1 : Schema
IDs1 = extractData (π [SubjectId] Q1)

Q2 : Query [SubjectId,Age]                          
Q2 =  π [SubjectId,Age]
    $ Limit CASE 
    $ σ ((SubjectId `IN` IDs1) && (CaseCtrl == True)) (toQuery rightCloudTab2);

-- ill-typed, wrong targeted table !    
-- replace 2 by 1.
    
Q2bis : Query [SubjectId,Age]                          
Q2bis =  π [SubjectId,Age]
    $ Limit CASE 
    $ σ ((SubjectId `IN` IDs1) && (CaseCtrl == True)) (toQuery rightCloudTab2);    
    
    
Q2' : Query [SubjectId,Age]                          
Q2' =  π [SubjectId,Age]
     $ Limit CASE 
     $ σ ((SubjectId `IN` IDs1) && (CaseCtrl == False)) (toQuery rightCloudTab2);  
    
IDs2 : Schema
IDs2 = extractData (π [SubjectId] Q2) 

IDs2' : Schema
IDs2' = extractData (π [SubjectId] Q2') 
    
Q3 : Query [SubjectId,VariantWE,TypeVarWE] -- ajouter un group by probab!          
Q3 = π [SubjectId,VariantWE,TypeVarWE] 
   $ σ ((SubjectId `IN` IDs2) && (position == 2 || position == 10))
       (toQuery rightCloudTab1);     


Q3' : Query [SubjectId,VariantWE,TypeVarWE]      
Q3' = π [SubjectId,VariantWE,TypeVarWE] 
   $ σ ((SubjectId `IN` IDs2') && (position == 2 || position == 10))
       (toQuery rightCloudTab1);     
                                                                           
                         
scenario : GeneticQuery [SubjectId,ZIP,Gender,Age,Variant,TypeVar,MyTattoo]
scenario =  do

 G1  `SendRequest` (TTP,[Q1]) 
 G1  `SendRequest` (TTP,[Q2,Q2'])
 G1  `SendRequest` (TTP,[Q3,Q3'])

 TTP  `SendRequest` (LeftCloud,[Q1]) 
 TTP  `SendRequest` (RightCloud,[Q2,Q2'])
 TTP  `SendRequest` (RightCloud,[Q3,Q3'])
 
 let q1 = LeftCloud  `executeRequest` [Q1];
 let q2 = RightCloud `executeRequest` [Q2,Q2'];
 let q3 = RightCloud `executeRequest` [Q3,Q3'];
 
 demDatal       <- LeftCloud  `SendData` (TTP,q1)  
 demDatar       <- RightCloud `SendData` (TTP,q2)
 vcfFiles       <- RightCloud `SendData` (TTP,q3)
 
 let r1          = decrypt VariantWE (AESD "key2") vcfFiles;
 let r2          = decrypt TypeVarWE (AESD "key1") r1;
 let r3          = readW VariantW (RGIG "wkey1" 1 ["seed1"] 1) r2;
 let vcfFiles    = readW TypeVarW (RGIG "wkey2" 2 ["seed2"] 2) r3;
 let plainData   = defrag (defrag demDatal demDatar) vcfFiles 
 
 TTP `ReturnResults` (G1,TTP `Compute` plainData)
   
 
  
   
    
      

                                                    
            
             
             
             
             
                             
                             
                             
                             
             
             
             
             
             
             
              
                    
                        
            
             
          
             

            
                        
                                    
                                                
                                                            
                                                                     
             

                      
                                                                      
                                                                      
                                                                               
    
          
     