{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-binds -fno-warn-missing-signatures #-}

module CodeGen where

-- import qualified Data.Set as Set
import Asm
import Ast
import qualified Data.Map as Map
import Lexer
import Parser
import Typing
import qualified Data.ByteString.Lazy.Char8 as BS
-- import Data.IntMap (fromList, foldlWithKey)

type Variable = (String, DataType)

data Config = Dict
  { capability :: Capability,
    extension :: String,
    memoryModel :: MemoryModel,
    addressModel :: AddressingModel,
    executionMode :: ExecutionMode,
    shaderType :: ExecutionModel,
    source :: (SourceLanguage, Int),
    entryPoint :: String,
    uniforms :: [(String, DataType, StorageClass, Int)] -- (name, type, position)
  }

type VariableOpIdMap = Map.Map String OpId

data CodeGenState = CodeGenState
  { idCount :: Int,
    idMap :: VariableOpIdMap,

    headerFields :: [Instruction],
    nameFields :: [Instruction],
    uniformsFields :: [Instruction],
    constFields :: [Instruction],
    functionFields :: [Instruction]
  }
  deriving (Show)

defaultConfig :: Config
defaultConfig =
  Dict
    { capability = Shader,
      addressModel = Logical,
      memoryModel = GLSL450,
      source = (GLSL, 450),
      shaderType = Fragment,
      executionMode = OriginUpperLeft,
      extension = "GLSL.std.450",
      entryPoint = "main",
      uniforms = [("uv", vector2, Input, 0), ("outColor", vector4, Output, 0)]
    }


data IdType
  = IdTypeDataType DataType -- done
  | IdTypeConstant Literal --done
  | IdTypeVariable String --tbd
  | IdTypeFunction String DataType -- name return type, arguments --tbd
  | IdTypeCodeSegment Range --tbd
  deriving (Show)

idTypeToKey:: IdType -> String
idTypeToKey d = case d of
  IdTypeDataType t -> "type " ++ show t
  IdTypeConstant v -> "const " ++ show v
  IdTypeVariable s -> "var " ++ s
  IdTypeFunction s t -> "func " ++ s ++ " " ++ show t
  IdTypeCodeSegment r -> "code segment " ++ show r

findId :: IdType -> VariableOpIdMap -> Maybe OpId
findId d = Map.lookup (idTypeToKey d)

insertId :: IdType -> Int-> VariableOpIdMap -> (Int,VariableOpIdMap)
insertId key count m =
  case findId key m of
    Just _ -> (count,m)
    Nothing -> (count, 
      Map.insert (idTypeToKey key) (case key of 
        IdTypeDataType t -> IdName (show t)
        IdTypeConstant l -> 
          let name= case l of
                            LUint i -> "uint_"++ show i
                            LInt i -> "int_"++show i
                            LFloat f -> "float_"++show f
          in IdName name
        IdTypeVariable s -> IdName s
        IdTypeFunction s t -> IdName  (s ++
          (case t of
            DTypeFunction returnType [] -> ""
            DTypeFunction returnType argTypes -> "_"++ (show argTypes)
            _ -> error "Invalid function type"
          ) )
        IdTypeCodeSegment r -> Id (count+1)
        ) m)

searchTypeId :: VariableOpIdMap -> DataType -> OpId
searchTypeId m dt= case findId (IdTypeDataType dt) m of
  Just x -> x
  Nothing -> error (show dt ++ " type not found")

genTypeCode :: CodeGenState -> DataType -> CodeGenState
genTypeCode state dtype =
  case findId (IdTypeDataType dtype) (idMap state) of
    Just _ -> state
    Nothing ->
      let
        state' = case dtype of
          DTypeVoid -> state
          DTypeBool -> state
          DTypeInt _ _ -> state
          DTypeFloat _ -> state
          DTypeVector _ baseType -> genTypeCode state baseType
          DTypeMatrix _  baseType -> genTypeCode state baseType
          DTypeArray _ baseType -> genTypeCode state baseType
          DTypePointer baseType _-> genTypeCode state baseType
          DTypeStruct _ fields -> foldl genTypeCode state fields
          DTypeFunction returnType argsType -> foldl genTypeCode (genTypeCode state returnType) argsType

        (newCount, newMap) = insertId (IdTypeDataType dtype) (idCount state') (idMap state')

        searchTypeId' = searchTypeId newMap

        typeId = searchTypeId' dtype

        typeInstruction = [Instruction (Just typeId , case dtype of
          DTypeVoid -> OpTypeVoid
          DTypeBool -> OpTypeBool
          DTypeInt size sign-> OpTypeInt size sign
          DTypeFloat size -> OpTypeFloat size
          DTypeVector size baseType ->
              OpTypeVector (searchTypeId' baseType) size
          DTypeMatrix col baseType ->
              OpTypeMatrix (searchTypeId' baseType) col
          DTypeArray size baseType ->
              OpTypeArray (searchTypeId' baseType) size
          DTypePointer baseType storage ->
              OpTypePointer (searchTypeId' baseType) storage
          DTypeStruct name baseTypes->
              OpTypeStruct (ShowList (map searchTypeId' baseTypes))
          DTypeFunction returnType argTypes->
              OpTypeFunction (searchTypeId' returnType) (ShowList (map searchTypeId' argTypes))
          )]
        updatedState = state'
          { idCount = newCount,
            idMap = newMap,
            constFields = constFields state' ++ typeInstruction
          }
       in updatedState

genConstCode :: CodeGenState -> Literal -> CodeGenState
genConstCode state v =
  let
    dtype = case v of
      LUint _ -> DTypeInt 32 0
      LInt _ -> DTypeInt 32 1
      LFloat _ -> DTypeFloat 32
    state'= genTypeCode state dtype
    (newCount, newMap) = insertId (IdTypeConstant v ) (idCount state') (idMap state')
    typeId = searchTypeId newMap dtype

    constId = case findId (IdTypeConstant v) newMap of
      Just x -> x
      Nothing -> error (show v++" const not found")

    constInstruction =[Instruction (Just constId, OpConstant typeId v)]
  in state'
    { idCount = newCount,
      idMap = newMap,
      constFields = constFields state' ++ constInstruction
    }

genUniformCode :: CodeGenState -> [(String, DataType, StorageClass, Int)] -> CodeGenState
genUniformCode = foldl
    (\accState (name, dtype, storage, _) ->
       let
        state' = genTypeCode accState (DTypePointer dtype storage)
        pointerTypeId = case findId (IdTypeDataType (DTypePointer dtype storage)) (idMap state') of
          Just x -> x
          Nothing -> error (show dtype ++ show storage ++"Pointer base not found")

        variableInstruction = [Instruction (Just (IdName name) , OpVariable pointerTypeId storage)]
        nameInstruction = [Instruction (Nothing, OpName (IdName name) name)]
        uniformsInstruction = [Instruction (Nothing, OpDecorate (IdName name) (Location 0))]

        updatedState = state'{
          nameFields = nameFields state' ++ nameInstruction,
          uniformsFields = uniformsFields state' ++ uniformsInstruction,
          constFields = constFields state' ++ variableInstruction
        }
       in updatedState
    )


genInitCode :: Config -> CodeGenState
genInitCode h =
  genUniformCode state (uniforms h)
  where
    startId = 0
    headInstruction =
      [ Instruction (Nothing, OpCapability (capability h)),
        Instruction (Just (Id (startId + 1)), OpExtInstImport (extension h)),
        Instruction (Nothing, OpMemoryModel (addressModel h) (memoryModel h)),
        Instruction (Nothing, OpEntryPoint (shaderType h) (IdName (entryPoint h)) (entryPoint h) (ShowList (map (\(name, _, _, _) -> IdName name) (uniforms h)))),
        Instruction (Nothing, OpExecutionMode (IdName (entryPoint h)) (executionMode h)),
        Instruction (Nothing, OpSource (fst (source h)) (snd (source h)))
      ]

    idMap = Map.insert ("extension " ++ extension h) (Id (startId + 1)) Map.empty
    idCount = startId+1
    constInstruction = []
    state = CodeGenState
        { idCount = idCount,
          idMap = idMap,
          headerFields = Instruction (Nothing, Comment "Generated Header") : headInstruction,
          nameFields = [Instruction (Nothing, Comment "Generated Names")],
          uniformsFields = [Instruction (Nothing, Comment "Generated Uniforms")],
          constFields = [Instruction (Nothing, Comment "Generated Constants And Type") ],
          functionFields = [Instruction (Nothing, Comment "Generated Functions")]
        }

genVariableCode :: CodeGenState -> Variable -> CodeGenState
genVariableCode state (name, dtype) =
  let
    state' = genTypeCode state dtype
    (newCount, newMap) = insertId (IdTypeVariable name) (idCount state') (idMap state')
    typeId = case findId (IdTypeDataType dtype) newMap of
      Just x -> x
      Nothing -> error (show dtype ++ " type not found")

    variableInstruction = [Instruction (Just (IdName name), OpVariable typeId Private)]
    nameInstruction = [Instruction (Nothing, OpName (IdName name) name)]
    updatedState = state'
      { idCount = newCount,
        idMap = newMap,
        nameFields = nameFields state' ++ nameInstruction,
        constFields = constFields state' ++ variableInstruction
      }
   in updatedState

genFunctionCode :: CodeGenState -> Dec Range -> CodeGenState
genFunctionCode state (DecAnno r name t) =
  state
genFunctionCode state (Dec range name args expr) =
  let

    funcName = case name of
      Name _ n -> BS.unpack n
    -- Process the function arguments
    typeConvert t = (case t of
        Just (TVar _ (Name _ "int")) -> int32
        Just (TVar _ (Name _ "float")) -> float32
        Just _ -> error "Invalid type"
        Nothing -> error "No type"
      )
    (argsTypes , returnType)=case funcName of
      "main" -> (
          [],
          DTypeVoid
        )
      _ -> (
          map (\(Argument _ (Name _ name) t) -> ( typeConvert t,name)) args,
          typeConvert (Just (TVar (Range (AlexPn 0 0 0) (AlexPn 0 0 0)) (Name (Range (AlexPn 0 0 0) (AlexPn 0 0 0)) "int"))) --TODO: Change this to the actual return type
        )

    argsPointer = map (\(t,name) -> (DTypePointer t Function,name)) argsTypes
    functionType = DTypeFunction returnType (map fst argsPointer)

    key = IdTypeFunction funcName functionType
  in
    case findId key (idMap state) of
      Just _ -> state
      Nothing ->
        let
          state' = genTypeCode state functionType

          typeId = searchTypeId (idMap state') functionType
          returnTypeId = searchTypeId (idMap state') returnType

          (newCount,newMap)=insertId key (idCount state') (idMap state')

          funcId = case findId key newMap of
            Just x -> x
            Nothing -> error (show key ++ " function not found")
            -- Nothing -> error (Map.foldlWithKey   (\acc k v -> acc ++"\n"++ show k ++" @ "++ show v) "" newMap)

          functionParameterInstruction = map (\(t,name) -> Instruction(Just (IdName (BS.unpack name)), OpFunctionParameter (searchTypeId newMap t))) argsPointer
          startInstruction = [Instruction (Just funcId, OpFunction returnTypeId None typeId)]

          functionInstruction =startInstruction ++ functionParameterInstruction ++[Instruction (Nothing, OpFunctionEnd)]

          constInstruction = []
        in
          state'
            {
              idCount = idCount state',
              idMap = newMap,
              constFields = constFields state' ++ constInstruction,
              functionFields = functionFields state' ++ functionInstruction
            }





genCode :: Config -> [Dec Range] -> CodeGenState
genCode config decs =
  let header = genInitCode config
      functions = foldl genFunctionCode header decs
      -- test = genConstCode functions (LInt 1)
      -- test =genTypeCode functions (DTypeVoid)
      test =functions

   in test
