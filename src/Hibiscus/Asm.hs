{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -w #-}

module Hibiscus.Asm
  ( Instruction (..),
    Literal (..),
    Ops (..),
    OpId (..),
    ShowList (..),
    Capability (..),
    AddressingModel (..),
    SourceLanguage (..),
    StorageClass (..),
    Decoration (..),
    FunctionControl (..),
    MemoryModel (..),
    ExecutionModel (..),
    ExecutionMode (..),
  )
where

data Literal
  = LBool Bool
  | LUint Int
  | LInt Int
  | LFloat Float
  deriving (Show, Eq, Ord)

data OpId
  = IdName String
  | Id Int

instance Show OpId where
  show (IdName s) = "%" ++ s
  show (Id i) = "%" ++ show i

type ResultType = OpId

newtype ShowList a = ShowList [a]

instance (Show a) => Show (ShowList a) where
  show (ShowList []) = ""
  show (ShowList (x : xs)) = show x ++ " " ++ show (ShowList xs)

type ResultId = OpId

data Capability
  = Matrix
  | Shader
  deriving (Show)

data SourceLanguage
  = Unknown
  | HLSL
  | GLSL
  deriving (Show)

data StorageClass
  = Function
  | Input
  | Output
  | UniformConstant
  | Uniform
  | Private
  | FunctionParameter
  | Incoming
  | Outgoing
  | Pointer
  deriving (Show, Eq, Ord)

data ExecutionModel
  = Vertex
  | TessellationControl
  | TessellationEvaluation
  | Geometry
  | Fragment
  | GLCompute
  | Kernel
  deriving (Show)

data ExecutionMode
  = Invocations Int
  | OriginUpperLeft
  | OriginLowerLeft
  deriving (Show)

data Decoration
  = RelaxedPrecision
  | SpecId Int
  | Block
  | Location Int

instance Show Decoration where
  show RelaxedPrecision = "RelaxedPrecision"
  show (SpecId i) = "SpecId " ++ show i
  show Block = "Block"
  show (Location i) = "Location " ++ show i

data FunctionControl
  = None
  | Inline
  | DontInline
  | Pure
  | Const
  deriving (Show)

data AddressingModel
  = Logical
  | Physical32
  | Physical64
  deriving (Show)

data MemoryModel
  = Simple
  | GLSL450
  | OpenCL
  | Vulkan
  deriving (Show)

data Ops
  = -- OpMiscellaneous
    OpNop
  | OpUndef ResultType
  | OpSourceContinued String
  | OpSource SourceLanguage Int
  | OpSourceExtension String
  | OpName OpId String
  | OpMemberName OpId Int String
  | OpString OpId String
  | OpLine Int Int
  | OpNoLine
  | -- OpAnnotation
    OpDecorate OpId Decoration
  | OpMemberDecorateStringGO OpId Int Decoration String
  | -- OpExtension
    OpExtension String
  | OpExtInstImport String
  | OpExtInst OpId OpId (ShowList OpId)
  | -- OpModeSetting
    OpMemoryModel AddressingModel MemoryModel
  | OpEntryPoint ExecutionModel OpId String (ShowList OpId)
  | OpExecutionMode OpId ExecutionMode
  | OpCapability Capability
  | -- OpTypeDeclaration
    OpTypeVoid
  | OpTypeBool
  | OpTypeInt Int Int -- bit width  , 0 indicates unsigned,1 indicates signed semantics.
  | OpTypeFloat Int -- bit width
  | OpTypeVector OpId Int -- component count
  | OpTypeMatrix OpId Int -- vectorTypeId column count
  | OpTypeArray OpId Int -- data type id
  | OpTypeStruct (ShowList OpId) -- data types id
  | OpTypePointer OpId StorageClass
  | OpTypeFunction OpId (ShowList OpId) -- data types id
  | -- OpConstant
    OpConstantTrue ResultType
  | OpConstantFalse ResultType
  | OpConstant ResultType Literal
  | OpConstantComposite ResultType (ShowList OpId)
  | OpConstantSampler ResultType Int Int
  | OpConstantNull ResultType
  | -- OpMemory
    OpVariable OpId StorageClass
  | OpLoad ResultType OpId
  | OpStore OpId OpId
  | -- OpFunction
    OpFunction ResultType FunctionControl OpId
  | OpFunctionParameter ResultType
  | OpFunctionEnd
  | OpFunctionCall ResultType OpId (ShowList OpId)
  | -- OpConversion
    OpConvertFToU ResultType OpId -- float to unsigned int
  | OpConvertFToS ResultType OpId -- float to signed int
  | OpConvertSToF ResultType OpId -- signed int to float
  | OpConvertUToF ResultType OpId -- unsigned int to float
  | OpUConvert ResultType OpId -- unsigned int to unsigned int
  | OpSConvert ResultType OpId -- signed int to signed int
  | OpFConvert ResultType OpId -- float to float
  | OpBitcast ResultType OpId
  | -- OpComposite
    OpCompositeConstruct ResultType (ShowList OpId)
  | OpCompositeExtract ResultType OpId [Int]
  | OpCompositeInsert ResultType OpId OpId (ShowList OpId)
  | -- OpArithmetic
    OpSNegate ResultType OpId
  | OpFNegate ResultType OpId
  | OpIAdd ResultType OpId OpId
  | OpISub ResultType OpId OpId
  | OpIMul ResultType OpId OpId
  | OpUDiv ResultType OpId OpId -- unsigned division
  | OpSDiv ResultType OpId OpId -- signed division
  | OpUMod ResultType OpId OpId -- unsigned modulo
  | OpSMod ResultType OpId OpId -- signed modulo
  | OpFAdd ResultType OpId OpId -- float
  | OpFSub ResultType OpId OpId
  | OpFMul ResultType OpId OpId
  | OpFDiv ResultType OpId OpId
  | OpFMod ResultType OpId OpId
  | OpFRem ResultType OpId OpId
  | OpVectorTimesScalar ResultType OpId OpId
  | OpVectorTimesMatrix ResultType OpId OpId
  | OpMatrixTimesScalar ResultType OpId OpId
  | OpMatrixTimesVector ResultType OpId OpId
  | OpMatrixTimesMatrix ResultType OpId OpId
  | -- OpLogical
    OpLogicalEqual ResultType OpId OpId
  | OpLogicalNotEqual ResultType OpId OpId
  | OpLogicalOr ResultType OpId OpId
  | OpLogicalAnd ResultType OpId OpId
  | OpLogicalNot ResultType OpId
  | OpLogicalXor ResultType OpId OpId
  | OpIEqual ResultType OpId OpId -- int
  | OpINotEqual ResultType OpId OpId
  | OpUGreaterThan ResultType OpId OpId
  | OpSGreaterThan ResultType OpId OpId
  | OpUGreaterThanEqual ResultType OpId OpId
  | OpSGreaterThanEqual ResultType OpId OpId
  | OpULessThan ResultType OpId OpId
  | OpSLessThan ResultType OpId OpId
  | OpULessThanEqual ResultType OpId OpId
  | OpSLessThanEqual ResultType OpId OpId
  | OpFOrdEqual ResultType OpId OpId -- float
  | OpFUnordEqual ResultType OpId OpId
  | OpFOrdNotEqual ResultType OpId OpId
  | OpFUnordNotEqual ResultType OpId OpId
  | OpFOrdLessThan ResultType OpId OpId
  | OpFUnordLessThan ResultType OpId OpId
  | OpFOrdGreaterThan ResultType OpId OpId
  | OpFUnordGreaterThan ResultType OpId OpId
  | OpFOrdLessThanEqual ResultType OpId OpId
  | OpFUnordLessThanEqual ResultType OpId OpId
  | OpFOrdGreaterThanEqual ResultType OpId OpId
  | OpFUnordGreaterThanEqual ResultType OpId OpId
  | -- OpControlFlow
    OpLabel
  | OpBranch OpId
  | OpBranchConditional OpId OpId OpId
  | OpSwitch OpId OpId [(Int, OpId)]
  | OpKill
  | OpReturn
  | OpReturnValue OpId
  | OpUnreachable
  | Comment String
  deriving (Show)

newtype Instruction = Instruction (Maybe ResultId, Ops)

instance Show Instruction where
  show (Instruction (_, Comment s)) = "; " ++ s
  show (Instruction (Just res, OpConstant r l)) =
    show res
      ++ " = "
      ++ "OpConstant "
      ++ show r
      ++ " "
      ++ ( case l of
             LBool b -> show b
             LUint i -> show i
             LInt i -> show i
             LFloat f -> show f
         )
  show (Instruction (Nothing, op)) = show op
  show (Instruction (Just res, op)) = show res ++ " = " ++ show op

test :: () -> [Instruction]
test () =
  [ Instruction (Nothing, OpTypeFloat 8),
    Instruction (Just (IdName "name"), OpTypeInt 32 0),
    Instruction (Just (Id 2), OpTypeInt 16 1)
  ]
