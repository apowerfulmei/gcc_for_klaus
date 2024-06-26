//===-- DiffConsumer.cpp - Difference Consumer ------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This files implements the LLVM difference Consumer
//
//===----------------------------------------------------------------------===//

#include "DiffConsumer.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"

using namespace llvm;

static void ComputeNumbering(Function *F,
                             DenseMap<Value *, unsigned> &Numbering) {
  unsigned IN = 0;

  // Arguments get the first numbers.
  for (Function::arg_iterator AI = F->arg_begin(), AE = F->arg_end(); AI != AE;
       ++AI)
    if (!AI->hasName())
      Numbering[&*AI] = IN++;

  // Walk the basic blocks in order.
  for (Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {
    if (!FI->hasName())
      Numbering[&*FI] = IN++;

    // Walk the instructions in order.
    for (BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; ++BI)
      // void instructions don't get numbers.
      if (!BI->hasName() && !BI->getType()->isVoidTy())
        Numbering[&*BI] = IN++;
  }

  assert(!Numbering.empty() && "asked for numbering but numbering was no-op");
}

void Consumer::anchor() {}

void DiffConsumer::printValue(Value *V, bool isL) {
  if (V->hasName()) {
    out << "xxxx";
    out << (isa<GlobalValue>(V) ? '@' : '%') << V->getName();
    return;
  }
  if (V->getType()->isVoidTy()) {
    if (isa<StoreInst>(V)) {
      out << "store to ";
      printValue(cast<StoreInst>(V)->getPointerOperand(), isL);
    } else if (isa<CallInst>(V)) {
      out << "call to ";
      printValue(cast<CallInst>(V)->getCalledOperand(), isL);
    } else if (isa<InvokeInst>(V)) {
      out << "invoke to ";
      printValue(cast<InvokeInst>(V)->getCalledOperand(), isL);
    } else {
      out << *V;
    }
    return;
  }
  if (isa<Constant>(V)) {
    out << *V;
    return;
  }

  unsigned N = contexts.size();
  while (N > 0) {
    --N;
    DiffContext &ctxt = contexts[N];
    if (!ctxt.IsFunction)
      continue;
    if (isL) {
      if (ctxt.LNumbering.empty())
        ComputeNumbering(cast<Function>(ctxt.L), ctxt.LNumbering);
      out << '%' << ctxt.LNumbering[V];
      return;
    } else {
      if (ctxt.RNumbering.empty())
        ComputeNumbering(cast<Function>(ctxt.R), ctxt.RNumbering);
      out << '%' << ctxt.RNumbering[V];
      return;
    }
  }

  out << "<anonymous>";
}

void DiffConsumer::header() {
  if (contexts.empty())
    return;

  DiffContext *pre = nullptr;
  for (SmallVectorImpl<DiffContext>::iterator I = contexts.begin(),
                                              E = contexts.end();
       I != E; ++I) {
    if (I->Differences)
      continue;
    if (isa<Function>(I->L)) {
      // Extra newline between functions.
      if (Differences)
        out << "\n";

      Function *L = cast<Function>(I->L);
      Function *R = cast<Function>(I->R);
      if (L->getName() != R->getName())
        out << "in function " << L->getName() << " / " << R->getName() << ":\n";
      else
        out << "in function " << L->getName() << ":\n";
    } else if (isa<BasicBlock>(I->L)) {
      BasicBlock *L = cast<BasicBlock>(I->L);
      BasicBlock *R = cast<BasicBlock>(I->R);
      if (L->hasName() && R->hasName() && L->getName() == R->getName())
        out << "  in block %" << L->getName() << ":\n";
      else {
        out << "  in block ";
        printValue(L, true);
        out << " / ";
        printValue(R, false);
        out << ":\n";
      }

      // store the diff information
      if (logDiff) {
        if (diff.find(L->getParent()->getName()) == diff.end()) {
          SmallSet<std::pair<BasicBlock *, BasicBlock *>, 32> blockSet;
          blockSet.insert(std::make_pair(L, R));
          diff[L->getParent()->getName()] = blockSet;
          // out << "left : " << *L << "\n";
          // out << "right : " << *R << "\n";
        } else {
          diff[L->getParent()->getName()].insert(std::make_pair(L, R));
          // out << "left : " << *L << "\n";
          // out << "right : " << *R << "\n";
        }
      }

      if (pre && isa<Function>(pre->L)) {
        std::string diffInfo = cast<Function>(pre->L)->getName().str() + ":";
        // if (!I->L->hasName()) I->L->setName("changed");
        // if (!I->R->hasName()) I->R->setName("changed");
        diffInfo += std::to_string(pre->LNumbering[L]) + ":";
        diffInfo += std::to_string(pre->RNumbering[R]);
        diffBlock.push_back(diffInfo);
      }

    } else if (isa<Instruction>(I->L)) {
      out << "    in instruction ";
      printValue(I->L, true);
      out << " / ";
      printValue(I->R, false);
      out << ":\n";
    }

    I->Differences = true;
    pre = I;
  }
}

void DiffConsumer::indent() {
  unsigned N = Indent;
  while (N--)
    out << ' ';
}

bool DiffConsumer::hadDifferences() const { return Differences; }

void DiffConsumer::enterContext(Value *L, Value *R) {
  contexts.push_back(DiffContext(L, R));
  Indent += 2;
}

void DiffConsumer::exitContext() {
  Differences |= contexts.back().Differences;
  contexts.pop_back();
  Indent -= 2;
}

void DiffConsumer::log(StringRef text) {
  header();
  indent();
  out << text << '\n';
}

void DiffConsumer::logf(const LogBuilder &Log) {
  header();
  indent();

  unsigned arg = 0;

  StringRef format = Log.getFormat();
  while (true) {
    size_t percent = format.find('%');
    if (percent == StringRef::npos) {
      out << format;
      break;
    }
    assert(format[percent] == '%');

    if (percent > 0)
      out << format.substr(0, percent);

    switch (format[percent + 1]) {
    case '%':
      out << '%';
      break;
    case 'l':
      printValue(Log.getArgument(arg++), true);
      break;
    case 'r':
      printValue(Log.getArgument(arg++), false);
      break;
    default:
      llvm_unreachable("unknown format character");
    }

    format = format.substr(percent + 2);
  }

  out << '\n';
}

void DiffConsumer::logd(const DiffLogBuilder &Log) {
  logDiff = true;
  header();
  logDiff = false;
#if 1
  for (unsigned I = 0, E = Log.getNumLines(); I != E; ++I) {
    Instruction *cur;
    indent();
    switch (Log.getLineKind(I)) {
    case DC_match:
      out << "  ";
      cur = Log.getLeft(I);
      cur->print(dbgs());
      dbgs() << '\n';
      // printValue(Log.getLeft(I), true);
      break;
    case DC_left:
      out << "< ";
      cur = Log.getLeft(I);
      cur->print(dbgs());
      dbgs() << '\n';
      // printValue(Log.getLeft(I), true);
      // store the diffed information
      // if (auto inst = dyn_cast<Instruction>(Log.getLeft(I))) {
      // }
      break;
    case DC_right:
      out << "> ";
      cur = Log.getRight(I);
      cur->print(dbgs());
      dbgs() << '\n';
      // printValue(Log.getRight(I), false);
      // store the diffed information
      // if (auto inst = dyn_cast<Instruction>(Log.getLeft(I))) {
      // }
      break;
    }
  }
#endif
}
