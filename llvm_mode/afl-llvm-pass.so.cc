/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}

/*
 * Build the canary check function.
 */
static void buildCheck(Module *M)
{
    Function *F = M->getFunction("__canary_check");
    if (F == nullptr)
        return;
    BasicBlock *Entry = BasicBlock::Create(M->getContext(), "", F);
    IRBuilder<> builder(Entry);

    auto i = F->arg_begin();
    Value *Ptr  = &(*(i++));
    Value *Size = &(*(i++));

    Value *IPtr = builder.CreatePtrToInt(Ptr, builder.getInt64Ty());
    IPtr = builder.CreateAdd(IPtr, builder.getInt64(-1));
    IPtr = builder.CreateAdd(IPtr, Size);
    IPtr = builder.CreateAnd(IPtr, builder.getInt64(-sizeof(uint64_t)));
    Ptr = builder.CreateIntToPtr(IPtr, builder.getInt64Ty()->getPointerTo());
    Value *Val64 = builder.CreateAlignedLoad(Ptr, MaybeAlign(sizeof(uint64_t)));

    const char *asmStr =
        "addq %fs:40, $0\n"
        "jne .Lok_${:uid}\n"
        "ud2\n"
        ".Lok_${:uid}:";
    llvm::FunctionType *AsmTy = llvm::FunctionType::get(
        builder.getInt64Ty(), {builder.getInt64Ty()}, false);
    const char *asmFlags = "=r,0,~{dirflag},~{fpsr},~{flags}";
    auto *AsmFunc = llvm::InlineAsm::get(AsmTy, asmStr, asmFlags,
        /*hasSideEffects=*/true);

    builder.CreateCall(AsmFunc, {Val64});
    builder.CreateRetVoid();

    F->setDoesNotThrow();
    F->setLinkage(GlobalValue::InternalLinkage);
    F->addFnAttr(llvm::Attribute::AlwaysInline);
}

/*
 * Build the initialization code.
 */
static void buildInit(Module *M, std::vector<Constant *> &Metadata)
{
    {
        // Stack initialization
        Function *F = M->getFunction("__init_stk_obj");
        if (F != nullptr)
            F->setDoesNotThrow();

        std::string Asm; // Insert the canary value fs:0x28 to the tail of the allocated memory location
        Asm +=
            ".type __init_stk_obj, @function\n"
            ".weak __init_stk_obj\n"
            "__init_stk_obj:\n"
            "\tlea (%rdi,%rsi),%rsi\n"
            "\tandq $-8,%rsi\n"
            "\taddq $-8,%rsi\n"
            "\txor %eax,%eax\n"
            ".Lloop:\n"
            "\tcmpq %rsi,%rdi\n"
            "\tjge .Lexit\n"
            "\tmov %rax,(%rdi)\n"
            "\tadd $8,%rdi\n"
            "\tjmp .Lloop\n"
            ".Lexit:\n"
            "\tmov %fs:40, %rax\n"
            "\tmov %rax,(%rsi)\n"
            "\tnegq (%rsi)\n"
            "\tretq\n";
        M->appendModuleInlineAsm(Asm);
    }

    {
        // Global initialization
        if (Metadata.size() == 0)
            return;

        LLVMContext &Cxt = M->getContext();
        /*
        Value *Ctor = M->getOrInsertFunction("__init_gbl_objs_ctor",
            Type::getVoidTy(Cxt), nullptr);
        Function *F = dyn_cast<Function>(Ctor);
        assert(F != nullptr);
        F->setLinkage(GlobalValue::InternalLinkage);
        */
        llvm::FunctionType *glbFunTy = llvm::FunctionType::get(
        Type::getVoidTy(Cxt), {}, false);
        Function *F = Function::Create(glbFunTy, GlobalValue::InternalLinkage, "__init_gbl_objs_ctor", M); // create global variable initialization function
        BasicBlock *Entry = BasicBlock::Create(M->getContext(), "", F);
        IRBuilder<> builder(Entry);

        Type *ElemTy = Metadata[0]->getType();
        Metadata.push_back(ConstantPointerNull::get(builder.getInt8PtrTy()));
        ArrayType *ArrayTy = ArrayType::get(ElemTy, Metadata.size());
        Constant *ArrayInit = ConstantArray::get(ArrayTy, Metadata);
        GlobalVariable *GV = new GlobalVariable(*M, ArrayTy, false, // set a new global variable array storing all canaries
            GlobalValue::InternalLinkage, ArrayInit, "");

        FunctionCallee Init = M->getOrInsertFunction("__init_gbl_objs", // call the assembly code to initialize the array
            builder.getVoidTy(), builder.getInt8PtrTy()->getPointerTo());

        Value *Array = builder.CreateBitCast(GV,
            builder.getInt8PtrTy()->getPointerTo());
        builder.CreateCall(Init, {Array});
        builder.CreateRetVoid();

        appendToGlobalCtors(*M, F, 1);

        std::string Asm; // Polulate all elements in the array with fs:0x28
        Asm +=
            ".type __init_gbl_objs, @function\n"
            ".weak __init_gbl_objs\n"
            "__init_gbl_objs:\n"
            "\tmovq (%rdi),%rsi\n"
            "\taddq $8,%rdi\n"
            "\ttestq %rsi,%rsi\n"
            "\tje .Lreturn\n"
            "\tandq $-8,%rsi\n"
            "\taddq $8,%rsi\n"

            // It seems that some globals can escape the __canary_gbls
            // section, so we add an additional sanity check...

            "\tlea __start___canary_gbls(%rip), %rax\n"
            "\tcmpq %rax,%rsi\n"
            "\tjl __init_gbl_objs\n"
            "\tlea __stop___canary_gbls(%rip),%rax\n"
            "\tcmpq %rax,%rsi\n"
            "\tjge __init_gbl_objs\n"

            "\tmov %fs:40,%rax\n"
            "\tmov %rax,(%rsi)\n"
            "\tnegq (%rsi)\n"
            "\tjmp __init_gbl_objs\n"
            ".Lreturn:\n"
            "\tretq\n";
        M->appendModuleInlineAsm(Asm);
    }

}

/*
 * Replace allocas (stack allocation) with an canary-version.
 */
static void replaceAlloca(Module *M, Instruction *I,
    std::vector<Instruction *> &dels)
{
    auto *Alloca = dyn_cast<llvm::AllocaInst>(I);
    if (Alloca == nullptr)
        return;

    Value *Size = Alloca->getArraySize(); // get the number of element allocated
    Type *Ty = Alloca->getAllocatedType(); // get the type of element allocated
    assert(Ty->isSized());

    IRBuilder<> builder(I);

    const DataLayout &DL = M->getDataLayout(); // get the original data layout
    Value *OldSize = builder.CreateMul(Size,  // old size = the number of new element * the size of each element
        builder.getInt64(DL.getTypeAllocSize(Ty)));
    Value *NewSize = builder.CreateAdd(OldSize, // new size = old size + 15
        builder.getInt64(2 * sizeof(uint64_t) - 1));

    AllocaInst *NewAlloca = builder.CreateAlloca(builder.getInt8Ty(), // rewrite the new allocation instruction
        NewSize);
    NewAlloca->setAlignment(Align(Alloca->getAlignment()));

    FunctionCallee Init = M->getOrInsertFunction("__init_stk_obj",
        builder.getVoidTy(), builder.getInt8PtrTy(),
        builder.getInt64Ty());

    builder.CreateCall(Init, {NewAlloca, NewSize}); // call the canary initialization fun with allocation pointer and size
    Value *Ptr = builder.CreateBitCast(NewAlloca, Alloca->getType()); // convert the pointer to the original pointer

    std::vector<User *> Replace, Lifetimes; // Update the user info
    for (User *Usr: Alloca->users())
    {
        if (auto Intr = dyn_cast<IntrinsicInst>(Usr))
        {
            if (Intr->getIntrinsicID() == Intrinsic::lifetime_start ||
                Intr->getIntrinsicID() == Intrinsic::lifetime_end)
            {
                Lifetimes.push_back(Intr);
                continue;
            }
        }
        if (BitCastInst *Cast = dyn_cast<BitCastInst>(Usr))
        {
            for (User *Usr2: Cast->users())
            {
                IntrinsicInst *Intr = dyn_cast<IntrinsicInst>(Usr2);
                if (Intr == nullptr)
                    continue;
                if (Intr->getIntrinsicID() == Intrinsic::lifetime_start ||
                        Intr->getIntrinsicID() == Intrinsic::lifetime_end)
                    Lifetimes.push_back(Usr2);
            }
        }
        Replace.push_back(Usr);
    }
    for (User *Usr: Replace)
        Usr->replaceUsesOfWith(Alloca, Ptr);
    for (User *Usr: Lifetimes)
    {
        if (auto *Lifetime = dyn_cast<Instruction>(Usr))
            dels.push_back(Lifetime);
    }
//        Usr->replaceUsesOfWith(Alloca, NewAlloca);

    Alloca->replaceAllUsesWith(Ptr);
    dels.push_back(Alloca);
}

/*
 * Replace global variables with a canary version.
 */
static void replaceGlobal(Module *M, GlobalVariable *GV,
    std::vector<Constant *> &Metadata, std::vector<GlobalVariable *> &dels)
{
    if (GV->isDeclaration() || GV->hasSection() || GV->isThreadLocal())
        return;
    switch (GV->getLinkage())
    {
        case GlobalValue::ExternalLinkage:
        case GlobalValue::InternalLinkage:
        case GlobalValue::PrivateLinkage:
        case GlobalValue::WeakAnyLinkage:
        case GlobalValue::WeakODRLinkage:
        case GlobalValue::CommonLinkage:
            break;
        default:
            return;     // Weird linkage
    }

    Type *Ty = GV->getType();
    PointerType *PtrTy = dyn_cast<PointerType>(Ty);
    if (PtrTy == nullptr)
        return;
    Ty = PtrTy->getElementType();
    if (!Ty->isSized())
        return;

    const DataLayout &DL = M->getDataLayout();
    size_t size = DL.getTypeAllocSize(Ty); // get original size
    size_t new_size = size + 2 * sizeof(uint64_t); // set the new size = old size + 16
    size_t canary_size = new_size - size; // the size storing the canary

    LLVMContext &Cxt = M->getContext();
    Type *CanaryTy = ArrayType::get(Type::getInt8Ty(Cxt), canary_size); // set the type of the memory storing canary
    StructType *WrapTy = StructType::get(Cxt, {Ty, CanaryTy}, false); // set overall type combining old data and canary

    Constant *WrapInit = ConstantStruct::get(WrapTy, {GV->getInitializer(),
        Constant::getNullValue(CanaryTy)});

    GlobalVariable *NewGV = new GlobalVariable(*M, WrapTy, GV->isConstant(), // set the new global variable
        GV->getLinkage(), WrapInit, "", GV, GV->getThreadLocalMode());
    NewGV->copyAttributesFrom(GV);
//    if (NewGV->isConstant() && NewGV->getLinkage() == GlobalValue::PrivateLinkage)
//        NewGV->setLinkage(GlobalValue::InternalLinkage);
    NewGV->setConstant(false);
    NewGV->setSection("__canary_gbls"); // set the section storing the new global variable

    Type *Int32Ty = Type::getInt32Ty(Cxt);
    Constant *Idxs00[2] = {ConstantInt::get(Int32Ty, 0),
                           ConstantInt::get(Int32Ty, 0)};
    GV->replaceAllUsesWith( // change all user pointer
        ConstantExpr::getGetElementPtr(WrapTy, NewGV, Idxs00, true));
    NewGV->takeName(GV);
    dels.push_back(GV);

    Constant *Idxs01[2] = {ConstantInt::get(Int32Ty, 0),
                           ConstantInt::get(Int32Ty, 1)};
    Constant *CanaryPtr = ConstantExpr::getGetElementPtr(WrapTy, NewGV,
        Idxs01, true);
    CanaryPtr = ConstantExpr::getBitCast(CanaryPtr, Type::getInt8PtrTy(Cxt));
    Metadata.push_back(CanaryPtr); // metadata stores the all canary global variables.
}

/*
 * Determine if a memory access should be checked.
 */
static bool shouldCheck(Module *M, Value *Ptr)
{
    const DataLayout *DL = &M->getDataLayout();
    ObjectSizeOffsetVisitor Visitor(*DL, /*TLI=*/nullptr, Ptr->getContext());
    SizeOffsetType Offset = Visitor.compute(Ptr);
    if (!Visitor.bothKnown(Offset))
        return true;
    size_t size      = (size_t)Offset.first.getZExtValue();
    off_t  offset    = (off_t)Offset.second.getSExtValue();
    Type *Ty = Ptr->getType();
    size_t type_size = UINT32_MAX;
    if (auto *PtrTy = dyn_cast<PointerType>(Ty))
    {
        Ty = PtrTy->getElementType();
        type_size = DL->getTypeAllocSize(Ty);
    }
    return (offset < 0 || (size_t)offset >= size + type_size);
}

/*
 * Insert a memory access check if necessary.
 */
static bool insertCheck(Module *M, Instruction *I)
{
    const DataLayout *DL = &M->getDataLayout();
    IRBuilder<> builder(I);

    Value *Ptr = nullptr;
    if (LoadInst *Load = dyn_cast<LoadInst>(I))
        Ptr = Load->getPointerOperand();
    else if (StoreInst *Store = dyn_cast<StoreInst>(I))
        Ptr = Store->getPointerOperand();
    if (Ptr == nullptr)
        return false;
    if (!shouldCheck(M, Ptr))
        return false;

    size_t size = 0;
    Type *Ty = Ptr->getType();
    if (auto *PtrTy = dyn_cast<PointerType>(Ty))
    {
        Ty = PtrTy->getElementType();
        size = DL->getTypeAllocSize(Ty);
    }
    Value *Size = builder.getInt64(size);

    Ptr = builder.CreateBitCast(Ptr, builder.getInt8PtrTy());

    FunctionCallee Check = M->getOrInsertFunction("__canary_check",
        builder.getVoidTy(), builder.getInt8PtrTy(),
        builder.getInt64Ty());

    builder.CreateCall(Check, {Ptr, Size});
    return true;
}


char AFLCoverage::ID = 0;


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }
    // Canary add-on
    uint16_t alloca_num = 0;
    uint16_t global_num = 0;
    uint16_t heap_num = 0;
    std::vector<Constant *> Metadata;
    bool AFL_CHECK_CANARY = (getenv("AFL_CHECK_CANARY") != nullptr);
    if (AFL_CHECK_CANARY) {
      {
        std::vector<Instruction *> dels;
        for (auto &F : M)
            for (auto &BB: F)
                for (auto &I: BB)
                    replaceAlloca(&M, &I, dels);
        alloca_num += dels.size();
        for (auto *I: dels)
            I->eraseFromParent();
      }
      {
        std::vector<GlobalVariable *> dels;
        for (auto &GV: M.getGlobalList())
            replaceGlobal(&M, &GV, Metadata, dels);
        global_num += dels.size();
        for (auto *V: dels)
            V->eraseFromParent();
      }
        for (auto &F : M)
            for (auto &BB: F)
                for (auto &I: BB)
                    heap_num += insertCheck(&M, &I) ? 1 : 0;
    }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

    // Canary Add-on
    if (AFL_CHECK_CANARY) {
        buildCheck(&M);
        buildInit(&M, Metadata);
        errs() << alloca_num << " " << global_num << " " << heap_num << "\n";
    }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
