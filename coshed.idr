-- #based on https://github.com/rcherrueau/C2QL/blob/master/composition-checker/Privy.idr

import Data.List
import Data.Vect
import Data.So

%default total
%access public export

--------------------------------------------------------------------------
-- Universes
--------------------------------------------------------------------------

data CryptTy = AES | RC4 -- | ElGamal | RSA | ...

data WmTy = GIG  

data Ty   = BOOL | NAT | TEXT | CHAR | CRYPT CryptTy Ty   
          | WATERMARK WmTy Ty

data Entity = Genetician | T3rdP | Cloud
                
interpTy : Ty -> Type
interpTy BOOL  = Bool
interpTy NAT   = Nat
interpTy CHAR  = Char
interpTy TEXT  = String
interpTy (CRYPT _ _) = String
interpTy (WATERMARK wms ty) = (interpTy ty) 

Attribute : Type
Attribute =  (String, Ty)

Schema : Type
Schema = List Attribute

Env : Nat -> Type
Env n = Vect (S n) Schema

Key : Type
Key = String

--------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------

Eq CryptTy where
     AES == AES = True
     RC4 == RC4 = True
     _   == _   = False

 
Eq WmTy where 
  GIG ==  GIG  = True
  _   ==  _    = False


Eq Ty where 
   BOOL                    == BOOL                   = True
   NAT                     == NAT                    = True
   TEXT                    == TEXT                   = True 
   CHAR                    == CHAR                   = True  
   (WATERMARK x y)         == (WATERMARK z t)        = x==z && y==t
   (CRYPT x y)             == (CRYPT  z t)           = x==z && y==t
   _                       == _                      = False     


Eq Entity where 
  Genetician == Genetician = True
  T3rdP      == T3rdP      = True
  Cloud      == Cloud      = True
  _          == _          = False 

--------------------------------------------------------------------------
-- Boolean tests to use in proofs
-------------------------------------------------------------------------- 

||| it uses isInEnv (Cherrrueau's et al. func) to proof that @oa is in @env
||| here it is 

isInEnv : (a : Attribute) -> (env : Env n) -> Bool
isInEnv a env = any (elem a) env

||| guarantee that every data intended to be prewatermarked is raw. (not watermarked yet nor encrypted).
isRawType : Ty -> Bool
isRawType NAT  = True
isRawType CHAR = True
isRawType TEXT = True
isRawType BOOL = True
isRawType _    = False

||| verifies if an attribtue is encrypted by evaluating its type
isEncrypted : Ty -> Bool
isEncrypted (CRYPT _ _)         = True                  
isEncrypted (WATERMARK _ t)     = isEncrypted t
isEncrypted _                   = False

-----------------------------------------------------------------
-- needed functions in the definition of ADTs, 
----------------------------------------------------------------- 

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
                             res = (Δs ++ lΔ )
                        in rewrite sym (plusTwoSucSuc n) in  res
    where
     --a gentle proof
    plusTwoSucSuc : (n : Nat) -> n + 2 = S (S n)
    plusTwoSucSuc Z     = Refl   
    plusTwoSucSuc (S k) = let inductHypo = plusTwoSucSuc k
                          in cong inductHypo {f=S}

cryptEnv : (oa : Attribute) -> CryptTy -> (env:Env n) -> 
           {auto p : So (isInEnv oa env)} -> Env n
cryptEnv oa c env  =  map (\s => if (elem oa s) then replaceOn oa (fst oa
                                , CRYPT c (snd oa)) s else s) env 

||| new function

watEnv : (a : Attribute) -> WmTy -> (env :Env n) -> 
         {auto p : So (isInEnv a env)} -> Env n
watEnv  a wms env  =  map (\s => if (elem a s) then replaceOn a (fst a,
                       WATERMARK wms (snd a)) s else s) env 
                       
------------------------------------------------------------------------------
-- Pred ADT
------------------------------------------------------------------------------

using (Δ : Schema, Δ' : Schema, δ : Schema, δ' : Schema,
       Δs : Vect n Schema, e1 : Entity, e2 : Entity, e3 : Entity,
       env : Env n , env' : Env m , env'' : Env k) {
       
namespace query

 data Pred : (Δ : Schema) -> Type where
    ||| Logical AND
    AND      : Pred Δ -> Pred Δ -> Pred Δ
    ||| Logical OR
    OR       : Pred Δ  -> Pred Δ  -> Pred Δ
    
    ||| Test that values of `a` are equals to `v`.
    |||
    ||| @ v a value with the idris type of `a`.
    ||| @ p proof that `a` is an attribute of `Δ`.
    Equal    : (a : Attribute) -> (v : interpTy (snd a)) ->
               {auto p : Elem a Δ} -> Pred Δ
               --Equal (snd a) => -- Note the presence of our interface
               --Eq (interpTy (snd a))   => -- For debugging only,
               --Show (interpTy (snd a)) => -- not required
    IN       : (a : Attribute) -> (s : Schema) ->  {auto p1 : So ((length s) == 1)} ->
               {auto p2 : Elem a Δ} -> Pred Δ
             
||| predicate that contains information for reading the tattoo
--|||
--|||  @ t secret threshold for feature selection  
--|||  @ s seed value for watermark string generation
--|||  @ k secret key of number of characters and symbols for digram matrix
--|||  @ r secret number of rounds 

 data ReadM : WmTy -> Type where
       RGIG : (k:Key) -> (t:Nat) -> (s:List String) -> (r:Nat) -> ReadM GIG
       
||| predicate that contains information for decryption     
      
 data DecryptI : CryptTy -> Type where
   AESD     : Key -> DecryptI AES
   RC4D     : Key -> DecryptI RC4
   
--------------------------------------------------------------------------
-- Query ADT  
-------------------------------------------------------------------------- 

-- needed attributes

 MyTattoo : Attribute
 MyTattoo = ("watermark",TEXT)
 
 Cnt : Attribute
 Cnt = ("Count", NAT)  

 data Query : Schema -> Type where

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
                 
       |||@ ReadW is the newly added watermarking destructor
       ReadW   : (a : Attribute) -> (info : ReadM GIG) -> 
                 {default Refl p1 : (snd a) = (WATERMARK GIG t)} ->
                 Query Δ ->
                 {auto p2 :Data.List.Elem a Δ} -> 
                 Query ((replaceOn a (fst a, t) Δ)++[MyTattoo])
                                
       ToQuery  : (Δ : Schema) -> Query Δ 
       
       Limit : (rownum : Integer) -> Query Δ -> Query Δ                                  
-------------------------------------------------------------------------------
-- Privy
-------------------------------------------------------------------------------

namespace privy      

 data Privy : (env0 : Env n) -> (env1 : Env m) -> (Δ : Schema) -> Type where
 
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
   
   |||@ Wat is the newly added watermarking constructor 
   Wat          : (a : Attribute)-> 
                  {auto p1 : So (isRawType (snd a))} ->
                  {auto p2 : So (isInEnv a env)} -> 
                  Privy env (watEnv a GIG env) []
   

-----------------------------------------------------------------------------------
-- GeneticQuery ADT 
-----------------------------------------------------------------------------------
 
basicType : Ty -> Ty
basicType  NAT                     =  NAT
basicType  TEXT                    =  TEXT
basicType  BOOL                    =  BOOL
basicType  CHAR                    =  CHAR
basicType  DATE                    =  DATE
basicType (CRYPT _ t)              = basicType t
basicType (WATERMARK _ t)          = basicType t

||| an abstract query execution consists in data extraction 
extractData : {Δ:Schema}   -> Query Δ -> Schema
extractData (Project s _)       = s                                           
extractData (Count s _)         = s ++ [Cnt]
extractData (Limit _ d)         = extractData d                                      
extractData (Product d d')      = (extractData d) ++ (extractData d')
extractData (Select _ d)        = extractData d    
extractData (NJoin d d')        = nub (extractData d ++ extractData d')  
extractData (Defrag d d')       = (nub (extractData d ++ extractData d'))
extractData (ReadW _ _ d)       = extractData d ++ [MyTattoo]  
extractData (Decrypt a _ d)     = replaceOn a (fst a, basicType (snd a)) (extractData d)
extractData (ToQuery s)         = s   
         
executeRequest  :  (executer : Entity) -> 
                   {auto p : So (executer == T3rdP || executer == Cloud)} ->
                   (request : List (Query Δ)) -> Schema
executeRequest _ ld = foldl union [] (map (extractData) ld)                       
                                                           
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
-- Privy sugar  
-------------------------------------------------------------------------- 

namespace sugar

 wat : (a : Attribute) -> 
       {auto p1 : So (isRawType (snd a))} ->
       {auto p2 : So (isInEnv a env)} -> 
       Privy env (watEnv a GIG env) []
 wat a {p1} {p2} = Wat a {p1=p1} {p2=p2}    

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

--------------------------------------------------------------------------
-- pred and Query sugar  
-------------------------------------------------------------------------- 

-- Predicate sugar

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
 
 toQuery : (Δ : Schema) -> Query Δ
 toQuery = ToQuery
}

--------------------------------------------------------------------------
-- Instantiations for the trusted party genetic application
-------------------------------------------------------------------------- 

ZIP : Attribute
ZIP = ("ZIP code",NAT)

Age : Attribute
Age = ("Age", NAT)

Gender : Attribute
Gender = ("gender",TEXT)

CaseCtrl : Attribute
CaseCtrl = ("case/control",BOOL)

SubjectId : Attribute
SubjectId = ("ID_SUB", TEXT)

subject : Schema
subject = [SubjectId,ZIP,Age,Gender,CaseCtrl]

Variant : Attribute
Variant = ("VARIANT", CHAR)

VariantE : Attribute
VariantE = ("VARIANT", CRYPT AES CHAR)

VariantW : Attribute
VariantW = ("VARIANT", WATERMARK GIG CHAR)

TypeVar : Attribute
TypeVar = ("TYPE_VARIANT", TEXT)

TypeVarE : Attribute
TypeVarE = ("TYPE_VARIANT", CRYPT AES TEXT)

TypeVarW : Attribute
TypeVarW = ("TYPE_VARIANT", WATERMARK GIG TEXT)

VariantWE     : Attribute
VariantWE     = ("VARIANT",  (CRYPT AES (WATERMARK GIG CHAR)))

TypeVarWE : Attribute 
TypeVarWE = ("TYPE_VARIANT", (CRYPT AES (WATERMARK GIG TEXT)))

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
           $ cryptEnv (fst TypeVar,WATERMARK GIG (snd TypeVar)) AES 
           $ cryptEnv (fst Variant,WATERMARK GIG (snd Variant)) AES
           $ watEnv TypeVar GIG
           $ watEnv Variant GIG LocalEnv

leftCloudEnv : Env 0
leftCloudEnv = [index 1 SafeTPEnv']

rightCloudEnv : Env 1
rightCloudEnv = [index 0 SafeTPEnv',  index 2 SafeTPEnv']

leftCloudTab : Schema -- zip, gender
leftCloudTab = index 1 SafeTPEnv'

rightCloudTab1 : Schema  -- genetic data
rightCloudTab1 = index 0 SafeTPEnv'

rightCloudTab2 : Schema  -- age, caseCtrl
rightCloudTab2 = index 2 SafeTPEnv'
-------------------------------------------- Spécification de l'environnement

specTPEnv : Privy LocalEnv  SafeTPEnv' []
specTPEnv = do frag [ZIP,Gender] SubjectId; 
                 wat Variant;
                 wat TypeVar;
                 crypt (fst Variant,WATERMARK GIG (snd Variant)) AES;  
                 crypt (fst TypeVar,WATERMARK GIG (snd TypeVar)) AES;

-------------------------------------------------------------------------
-- Scenario entities
-------------------------------------------------------------------------        

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

Q2' : Query [SubjectId,Age]                          
Q2' =  π [SubjectId,Age]
     $ Limit CASE 
     $ σ ((SubjectId `IN` IDs1) && (CaseCtrl == False)) (toQuery rightCloudTab2);  
    
IDs2 : Schema
IDs2 = extractData (π [SubjectId] Q2) 

IDs2' : Schema
IDs2' = extractData (π [SubjectId] Q2') 
    
Q3 : Query [SubjectId,VariantWE,TypeVarWE]       
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

 -----------------------------------------------------------------------
 -- Examples of type checking errors
 -----------------------------------------------------------------------
 
-- drop comments to see type checking errors 

-- ill-typed-env; 
                                                        
--specTPEnv' : Privy LocalEnv  SafeTPEnv' []
--specTPEnv' = do frag [ZIP,Gender] SubjectId; 
--                  crypt Variant AES;  
--                  wat (fst Variant,CRYPT AES (snd Variant));
--                  wat TypeVar;
--                  crypt (fst TypeVar,WATERMARK GIG (snd TypeVar)) AES;  
  
-- replace rightCloudTab2 with rightCloudTab1 
-- ill-typed, wrong targeted table ! 
    
--IllTypedQ2 : Query [SubjectId,Age]                          
--IllTypedQ2 =  π [SubjectId,Age]
--    $ Limit CASE 
--   $ σ ((SubjectId `IN` IDs1) && (CaseCtrl == True)) (toQuery rightCloudTab2);   
    
      

                                                    
            
             
             
             
             
                             
                             
                             
                             
             
             
             
             
             
             
              
                    
                        
            
             
          
             

            
                        
                                    
                                                
                                                            
                                                                     
             

                      
                                                                      
                                                                      
                                                                               
    
          
     
