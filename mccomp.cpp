#include "computeSets.hpp"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include "llvm/TargetParser/Host.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <queue>
#include <stdexcept>
#include <string.h>
#include <string>
#include <system_error>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace llvm;
using namespace llvm::sys;

FILE* pFile;

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//
// The lexer returns one of these for known things.
enum TOKEN_TYPE {

  IDENT = -1,        // [a-zA-Z_][a-zA-Z_0-9]*
  ASSIGN = int('='), // '='

  // delimiters
  LBRA = int('{'),  // left brace
  RBRA = int('}'),  // right brace
  LPAR = int('('),  // left parenthesis
  RPAR = int(')'),  // right parenthesis
  SC = int(';'),    // semicolon
  COMMA = int(','), // comma

  // types
  INT_TOK = -2,   // "int"
  VOID_TOK = -3,  // "void"
  FLOAT_TOK = -4, // "float"
  BOOL_TOK = -5,  // "bool"

  // keywords
  EXTERN = -6,  // "extern"
  IF = -7,      // "if"
  ELSE = -8,    // "else"
  WHILE = -9,   // "while"
  RETURN = -10, // "return"
  // TRUE   = -12,     // "true"
  // FALSE   = -13,     // "false"

  // literals
  INT_LIT = -14,   // [0-9]+
  FLOAT_LIT = -15, // [0-9]+.[0-9]+
  BOOL_LIT = -16,  // "true" or "false" key words

  // logical operators
  AND = -17, // "&&"
  OR = -18,  // "||"

  // operators
  PLUS = int('+'),    // addition or unary plus
  MINUS = int('-'),   // substraction or unary negative
  ASTERIX = int('*'), // multiplication
  DIV = int('/'),     // division
  MOD = int('%'),     // modular
  NOT = int('!'),     // unary negation

  // comparison operators
  EQ = -19,      // equal
  NE = -20,      // not equal
  LE = -21,      // less than or equal to
  LT = int('<'), // less than
  GE = -23,      // greater than or equal to
  GT = int('>'), // greater than

  // special tokens
  EOF_TOK = 0, // signal end of file

  // invalid
  INVALID = -100 // signal invalid token
};
// TOKEN struct is used to keep track of information about a token
struct TOKEN {
  int type = -100;
  std::string lexeme;
  int lineNo;
  int columnNo;
};

static std::string IdentifierStr; // Filled in if IDENT
static int IntVal;                // Filled in if INT_LIT
static bool BoolVal;              // Filled in if BOOL_LIT
static float FloatVal;            // Filled in if FLOAT_LIT
static std::string StringVal;     // Filled in if String Literal
static int lineNo, columnNo;

static TOKEN returnTok(std::string lexVal, int tok_type) {
  TOKEN return_tok;
  return_tok.lexeme = lexVal;
  return_tok.type = tok_type;
  return_tok.lineNo = lineNo;
  return_tok.columnNo = columnNo - lexVal.length() - 1;
  return return_tok;
}

// Read file line by line -- or look for \n and if found add 1 to line number
// and reset column number to 0
/// gettok - Return the next token from standard input.
static TOKEN gettok() {

  static int LastChar = ' ';
  static int NextChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar)) {
    if (LastChar == '\n' || LastChar == '\r') {
      lineNo++;
      columnNo = 1;
    }
    LastChar = getc(pFile);
    columnNo++;
  }

  if (isalpha(LastChar) || (LastChar == '_')) { // identifier: [a-zA-Z_][a-zA-Z_0-9]*
    IdentifierStr = LastChar;
    columnNo++;

    while (isalnum((LastChar = getc(pFile))) || (LastChar == '_')) {
      IdentifierStr += LastChar;
      columnNo++;
    }

    if (IdentifierStr == "int")
      return returnTok("int", INT_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "float")
      return returnTok("float", FLOAT_TOK);
    if (IdentifierStr == "void")
      return returnTok("void", VOID_TOK);
    if (IdentifierStr == "bool")
      return returnTok("bool", BOOL_TOK);
    if (IdentifierStr == "extern")
      return returnTok("extern", EXTERN);
    if (IdentifierStr == "if")
      return returnTok("if", IF);
    if (IdentifierStr == "else")
      return returnTok("else", ELSE);
    if (IdentifierStr == "while")
      return returnTok("while", WHILE);
    if (IdentifierStr == "return")
      return returnTok("return", RETURN);
    if (IdentifierStr == "true") {
      BoolVal = true;
      return returnTok("true", BOOL_LIT);
    }
    if (IdentifierStr == "false") {
      BoolVal = false;
      return returnTok("false", BOOL_LIT);
    }

    return returnTok(IdentifierStr.c_str(), IDENT);
  }

  if (LastChar == '=') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // EQ: ==
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("==", EQ);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("=", ASSIGN);
    }
  }

  if (LastChar == '{') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("{", LBRA);
  }
  if (LastChar == '}') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("}", RBRA);
  }
  if (LastChar == '(') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok("(", LPAR);
  }
  if (LastChar == ')') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(")", RPAR);
  }
  if (LastChar == ';') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(";", SC);
  }
  if (LastChar == ',') {
    LastChar = getc(pFile);
    columnNo++;
    return returnTok(",", COMMA);
  }

  if (isdigit(LastChar) || LastChar == '.') { // Number: [0-9]+.
    std::string NumStr;

    if (LastChar == '.') { // Floatingpoint Number: .[0-9]+
      do {
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      FloatVal = strtof(NumStr.c_str(), nullptr);
      return returnTok(NumStr, FLOAT_LIT);
    } else {
      do { // Start of Number: [0-9]+
        NumStr += LastChar;
        LastChar = getc(pFile);
        columnNo++;
      } while (isdigit(LastChar));

      if (LastChar == '.') { // Floatingpoint Number: [0-9]+.[0-9]+)
        do {
          NumStr += LastChar;
          LastChar = getc(pFile);
          columnNo++;
        } while (isdigit(LastChar));

        FloatVal = strtof(NumStr.c_str(), nullptr);
        return returnTok(NumStr, FLOAT_LIT);
      } else { // Integer : [0-9]+
        IntVal = strtod(NumStr.c_str(), nullptr);
        return returnTok(NumStr, INT_LIT);
      }
    }
  }

  if (LastChar == '&') {
    NextChar = getc(pFile);
    if (NextChar == '&') { // AND: &&
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("&&", AND);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("&", int('&'));
    }
  }

  if (LastChar == '|') {
    NextChar = getc(pFile);
    if (NextChar == '|') { // OR: ||
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("||", OR);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("|", int('|'));
    }
  }

  if (LastChar == '!') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // NE: !=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("!=", NE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("!", NOT);
      ;
    }
  }

  if (LastChar == '<') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // LE: <=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok("<=", LE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok("<", LT);
    }
  }

  if (LastChar == '>') {
    NextChar = getc(pFile);
    if (NextChar == '=') { // GE: >=
      LastChar = getc(pFile);
      columnNo += 2;
      return returnTok(">=", GE);
    } else {
      LastChar = NextChar;
      columnNo++;
      return returnTok(">", GT);
    }
  }

  if (LastChar == '/') { // could be division or could be the start of a comment
    LastChar = getc(pFile);
    columnNo++;
    if (LastChar == '/') { // definitely a comment
      do {
        LastChar = getc(pFile);
        columnNo++;
      } while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

      if (LastChar != EOF)
        return gettok();
    } else
      return returnTok("/", DIV);
  }

  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF) {
    columnNo++;
    return returnTok("0", EOF_TOK);
  }

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  std::string s(1, ThisChar);
  LastChar = getc(pFile);
  columnNo++;
  return returnTok(s, int(ThisChar));
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.

void addIndents(int n, std::string& str) {
  for (int i = 0; i < n; i++) {
    str += "\t";
  }
}

static TOKEN CurTok;
static std::deque<TOKEN> tok_buffer;

static void populateBuffer() {
  while (tok_buffer.size() <= 2)
    tok_buffer.push_back(gettok());
}

static TOKEN getNextToken() {
  // populate buffer so we have a lookahead of 2
  populateBuffer();

  TOKEN temp = tok_buffer.front();
  tok_buffer.pop_front();

  return CurTok = temp;
}

static TOKEN peekNext() {
  populateBuffer();
  return tok_buffer.front();
}

static void throwParserError(const std::unordered_set<std::string>& expected, std::string found) {
  std::cout << "Encountered an error on line " + std::to_string(lineNo) + " column " + std::to_string(columnNo) + ".\n";
  std::cout << "Expected one of: ";
  for (const auto& element : expected) {
    std::cout << element << ' ';
  }
  std::cout << "\nFound: " + found << std::endl;
  exit(1);
}

static void throwCodegenError(std::string message, TOKEN token) {
  std::cout << "Encountered an error during compilation: " << message << "\n" << std::endl;
  std::cout << "Lexeme: " + token.lexeme + "\nOn line: " + std::to_string(token.lineNo) + " column: " + std::to_string(token.columnNo) << std::endl;
  exit(1);
}
//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

template <typename T> using ptrVec = std::vector<std::unique_ptr<T>>;

// we also reverse when casting a vector of pointers to another vector due to the way we build up our left recursions backwards
template <typename Base, typename Derived> void castToDerived(std::vector<std::unique_ptr<Base>>& nodes, std::vector<std::unique_ptr<Derived>>& target) {
  for (int i = nodes.size() - 1; i >= 0; i--) {
    auto& node = nodes[i];
    Derived* derivedPtr = static_cast<Derived*>(node.release());
    target.push_back(std::unique_ptr<Derived>(derivedPtr));
  }
}

template <typename Base, typename Derived> void castToDerived(std::vector<std::unique_ptr<Base>>& nodes, std::unique_ptr<Derived>& target) {
  for (auto& node : nodes) {
    Derived* derivedPtr = static_cast<Derived*>(node.release());
    target.reset(derivedPtr);
    break;
  }
}

template <typename Base, typename Derived> void castToDerived(std::unique_ptr<Base>& node, std::vector<std::unique_ptr<Derived>>& target) {

  Derived* derivedPtr = static_cast<Derived*>(node.release());
  target.push_back(std::unique_ptr<Derived>(derivedPtr));
}

template <typename Base, typename Derived> void castToDerived(std::unique_ptr<Base>& node, std::unique_ptr<Derived>& target) {

  Derived* derivedPtr = static_cast<Derived*>(node.release());
  target.reset(derivedPtr);
}

//-- codegen shit --//
// so we add a new symbol table only if this is not an immediate function block
bool isFunctionBlock = false;
// so we dont add branch instructions after a return statement in a while/if
bool hasCreatedReturn = false;

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

using SymbolTable = std::unordered_map<std::string, AllocaInst*>;
using GlobalTable = std::unordered_map<std::string, GlobalVariable*>;
using Tables = std::vector<SymbolTable>;
Tables tables;
GlobalTable globalTable;

void printTables(const Tables& tables) {
  for (size_t i = 0; i < tables.size(); ++i) {
    std::cout << "Table " << i << ":\n";
    for (const auto& pair : tables[i]) {
      std::cout << "  Key: " << pair.first << ", AllocaInst*: ";

      if (pair.second != nullptr) {
        // Print some identifiable information about AllocaInst
        // This depends on what members/methods AllocaInst has.
        // For example:
        // std::cout << pair.second->someIdentifierMethod();
        std::cout << static_cast<void*>(pair.second); // As an example, print the pointer value
      } else {
        std::cout << "nullptr";
      }

      std::cout << "\n";
    }
  }
}

Type* stringToPtrType(std::string type) {
  if (type == "bool") {
    return Type::getInt1Ty(TheContext);
  } else if (type == "int") {
    return Type::getInt32Ty(TheContext);
  } else if (type == "float") {
    return Type::getFloatTy(TheContext);
  }

  return Type::getVoidTy(TheContext);
}

std::string ptrToStringType(Type* type) {
  if (type == Type::getInt1Ty(TheContext)) {
    return "bool";
  } else if (type == Type::getInt32Ty(TheContext)) {
    return "int";
  } else if (type == Type::getFloatTy(TheContext)) {
    return "float";
  }

  return "void";
}

// Assign ranks to types: float > 32 bit int > 1 bit int
int getTypeRank(Type* type) {
  if (type->isFloatTy())
    return 3;
  if (type->isIntegerTy(32))
    return 2;
  if (type->isIntegerTy(1))
    return 1;
  if (type->isVoidTy())
    return 0;
  return -1; // Unknown or unsupported type
};

Constant* getDefaultConst(Type* type) {
  int rank = getTypeRank(type);
  if (rank == 3) {
    return ConstantFP::get(TheContext, APFloat(0.0f));
  }
  if (rank == 2) {
    return ConstantInt::get(TheContext, APInt(32, 0, true));
  }
  if (rank == 1) {
    return ConstantInt::get(TheContext, APInt(1, 0, false));
  }
  return nullptr;
}

bool compareTypes(Type* type1, Type* type2) {

  // Compare the ranks of the types
  return getTypeRank(type1) >= getTypeRank(type2);
}

static AllocaInst* CreateEntryBlockAlloca(Function* TheFunction, const std::string& VarName, Type* type) {
  IRBuilder<> TmpB(&TheFunction->getEntryBlock(), TheFunction->getEntryBlock().begin());
  return TmpB.CreateAlloca(type, 0, VarName.c_str());
}

// widens left to right
// returns the widest type out of both values
Value* widenLtoR(Value* leftVal, Type* rightType) {

  Type* leftType = leftVal->getType();
  // widen as much as needed first
  // bool = int = 13 < int = 13 < float = 2

  if (leftType->isFloatTy()) {
    // no widening to be done
    return leftVal;
  }

  if (rightType->isFloatTy()) {
    Value* newVal = Builder.CreateSIToFP(leftVal, Type::getFloatTy(TheContext));
    return newVal;
  } else {
    // check the bit width of the integers we are dealing with
    // if they are not the same, then we need to widen the smaller one
    IntegerType* intLeft = cast<IntegerType>(leftVal->getType());
    unsigned widthLeft = intLeft->getIntegerBitWidth();

    IntegerType* intRight = cast<IntegerType>(rightType);
    unsigned widthRight = intRight->getIntegerBitWidth();

    if (widthRight > widthLeft) {
      Value* newVal = Builder.CreateZExt(leftVal, Type::getInt32Ty(TheContext));
      return newVal;
    }

    return leftVal;
  }
}

// return widest type
Value* narrowLtoR(Value* leftVal, Type* rightType) {

  Type* leftType = leftVal->getType();
  // widen as much as needed first
  // bool = int = 13 < int = 13 < float = 2

  if (rightType->isFloatTy()) {
    return leftVal;
  } else {
    Value* newVal;
    if (leftType->isFloatTy()) {
      newVal = Builder.CreateFPToSI(leftVal, Type::getInt32Ty(TheContext));
    } else {
      newVal = leftVal;
    }
    // check the bit width of the integers we are dealing with
    // if they are not the same, then we need to widen the smaller one

    IntegerType* intLeft = cast<IntegerType>(newVal->getType());
    unsigned widthLeft = intLeft->getIntegerBitWidth();

    IntegerType* intRight = cast<IntegerType>(rightType);
    unsigned widthRight = intRight->getIntegerBitWidth();

    if (widthLeft > widthRight) {
      //if new val is not equal to 0, then we want 1. otherwise we want 0. perfect.
      Value* boolVal = Builder.CreateICmpNE(newVal, getDefaultConst(Type::getInt32Ty(TheContext)));
      return boolVal;
    }
    return newVal;
  }
}

Value* trueValue = ConstantInt::get(Type::getInt1Ty(TheContext), 1, false);

//-- codegen shit --//

/// ASTNode - Base class for all AST nodes.
class ASTNode {
public:
  // destructor
  TOKEN token;
  virtual ~ASTNode() = default;
  virtual Value* codegen() = 0;
  virtual std::string to_string(int d) const { return ""; };
};

class ExprAST : public ASTNode {};

class NegationAST : public ExprAST {
public:
  std::unique_ptr<ExprAST> child;
  std::string symbol;
  NegationAST(std::string symbol, ptrVec<ASTNode>&& child) : symbol(symbol) { castToDerived<ASTNode, ExprAST>(child, this->child); };

  virtual Value* codegen() override {
    Value* childVal = child->codegen();
    //  if integer/float, and we have a !, cast to bool
    if (symbol == "!") {
      // first make sure we cast to bool if needed
      Value* narrowedValue = narrowLtoR(childVal, Type::getInt1Ty(TheContext));
      // flipit
      return Builder.CreateXor(narrowedValue, trueValue);
    }
    if (symbol == "-") {
      Value* widestValue = widenLtoR(childVal, Type::getInt32Ty(TheContext));
      if (widestValue->getType()->isFloatTy()) {
        return Builder.CreateFNeg(widestValue);
      }
      return Builder.CreateSub(getDefaultConst(Type::getInt32Ty(TheContext)), widestValue);
    }

    return nullptr;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";

    addIndents(d, str);
    str += "<Negation symbol='" + symbol + "'>\n";
    str += child->to_string(d + 1);
    addIndents(d, str);
    str += "</Negation>\n";
    return str;
  };
};

class PrimaryAST : public ExprAST {
public:
  virtual Value* codegen() override { return nullptr; };
};

class StorageAST : public ASTNode {

public:
  std::string value;
  StorageAST(std::string value) : value(value){};
  virtual Value* codegen() override { return nullptr; };
};

/// IntASTNode - Class for integer literals like 1, 2, 10,
class IntAST : public PrimaryAST {
  int Val;

public:
  IntAST(ptrVec<ASTNode>&& value) {
    std::unique_ptr<StorageAST> valueStorage;

    castToDerived<ASTNode, StorageAST>(value, valueStorage);
    this->Val = std::stoi(valueStorage->value);
  };
  virtual Value* codegen() override { return ConstantInt::get(TheContext, APInt(32, Val, true)); };
  virtual std::string to_string(int d) const override {
    std::string str = "";
    str += "<Int val='" + std::to_string(Val) + "'/>\n";
    return str;
  };
};

class FloatAST : public PrimaryAST {
  float Val;

public:
  FloatAST(ptrVec<ASTNode>&& value) {
    std::unique_ptr<StorageAST> valueStorage;

    castToDerived<ASTNode, StorageAST>(value, valueStorage);
    this->Val = std::stof(valueStorage->value);
  };

  virtual Value* codegen() override { return ConstantFP::get(TheContext, APFloat(Val)); };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    str += "<Float val='" + std::to_string(Val) + "'/>\n";
    return str;
  };
};

class BoolAST : public PrimaryAST {
  bool Val;

public:
  BoolAST(ptrVec<ASTNode>&& value) {
    std::unique_ptr<StorageAST> valueStorage;

    castToDerived<ASTNode, StorageAST>(value, valueStorage);
    if (valueStorage->value == "false") {
      Val = false;
    } else {
      Val = true;
    }
  };
  virtual Value* codegen() override { return ConstantInt::get(TheContext, APInt(1, Val, false)); };
  virtual std::string to_string(int d) const override {
    std::string str = "";
    str += "<Bool val='" + std::to_string(Val) + "'/>\n";
    return str;
  };
};

class FuncCallAST : public PrimaryAST {
  std::string name;
  std::vector<std::unique_ptr<ExprAST>> args;

public:
  FuncCallAST(ptrVec<ASTNode>&& name, ptrVec<ASTNode>&& args) {
    castToDerived<ASTNode, ExprAST>(args, this->args);

    std::unique_ptr<StorageAST> nameStorage;
    castToDerived<ASTNode, StorageAST>(name, nameStorage);
    this->name = nameStorage->value;
  };

  virtual Value* codegen() override {
    // Look up the name in the global module table.
    Function* CalleeF = TheModule->getFunction(name);

    if (!CalleeF) {
      throwCodegenError("Function " + name + " not declared", token);
    }

    if (CalleeF->arg_size() != args.size()) {
      throwCodegenError("Function " + name + " called with too many arguments. Got: " + to_string(args.size()) + ". Expected: " + to_string(CalleeF->arg_size()), token);
    }

    std::vector<Value*> ArgsV;

    // allow type widening, disallow type narrowing
    int i = 0;
    for (auto& Arg : CalleeF->args()) {
      Value* argCode = args[i]->codegen();

      if (compareTypes(Arg.getType(), argCode->getType())) {
        // if the parameter type is greater than or equal to the arg we codegen, then we can widen
        ArgsV.push_back(widenLtoR(argCode, Arg.getType()));
      } else {
        throwCodegenError("Attempted to pass argument of type " + ptrToStringType(argCode->getType()) + " to parameter of type " + ptrToStringType(Arg.getType()) +
                              " when calling function " + name,
                          token);
      }

      i++;
    }

    return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    str += "<FuncCall name='" + name + "'>";
    for (auto& arg : args) {
      str += arg->to_string(d + 1);
    }
    str += "</FuncCall>\n";
    return str;
  };
};

class VarCallAST : public PrimaryAST {
public:
  std::string name;
  VarCallAST(ptrVec<ASTNode> name) {
    std::unique_ptr<StorageAST> nameStorage;

    castToDerived<ASTNode, StorageAST>(name, nameStorage);
    this->name = nameStorage->value;
  };

  virtual Value* codegen() override {
    for (int i = tables.size() - 1; i >= 0; i--) {
      if (tables[i].find(name) != tables[i].end()) {
        return Builder.CreateLoad(tables[i][name]->getAllocatedType(), tables[i][name], name);
      }
    }

    if (globalTable.find(name) != globalTable.end()) {
      return Builder.CreateLoad(globalTable[name]->getValueType(), globalTable[name], name);
    }

    throwCodegenError("Variable " + name + " has not been declared or assigned.", token);
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    str += "<VarCall name='" + name + "' />\n";
    return str;
  };
};

class DeclAST : public ASTNode {

public:
  std::string type;
  std::string name;

  DeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) {

    std::unique_ptr<StorageAST> typeStorage;
    std::unique_ptr<StorageAST> nameStorage;

    castToDerived<ASTNode, StorageAST>(type, typeStorage);
    castToDerived<ASTNode, StorageAST>(name, nameStorage);
    this->type = typeStorage->value;
    this->name = nameStorage->value;
  };

  DeclAST(){};
};

class BinOpAST : public ExprAST {
public:
  std::string op;
  std::shared_ptr<ASTNode> left;
  std::shared_ptr<ASTNode> right;
  std::shared_ptr<BinOpAST> leftmostChild;

  BinOpAST(std::string op, ptrVec<ASTNode>&& left, ptrVec<ASTNode>&& right) : op(op) {
    this->left = std::move(left[0]);
    this->right = std::move(right[0]);
  };

  BinOpAST(std::string op, ptrVec<ASTNode>&& right) : op(op) { this->right = std::move(right[0]); };

  virtual Value* codegen() override {
    Function* TheFunction = Builder.GetInsertBlock()->getParent();

    if (op == "&&") {
      Value* leftVal = this->left->codegen();
      Value* narrowedValueLeft = narrowLtoR(leftVal, Type::getInt1Ty(TheContext));

      BasicBlock* leftFalseBB = BasicBlock::Create(TheContext, "leftTrue", TheFunction);
      BasicBlock* evalRightBB = BasicBlock::Create(TheContext, "evalRight", TheFunction);
      BasicBlock* mergeBB = BasicBlock::Create(TheContext, "merge", TheFunction);

      Value* leftCond = Builder.CreateICmpNE(narrowedValueLeft, Builder.getInt1(false));

      Builder.CreateCondBr(leftCond, evalRightBB, leftFalseBB);

      Builder.SetInsertPoint(leftFalseBB);
      Builder.CreateBr(mergeBB);

      Builder.SetInsertPoint(evalRightBB);
      Value* rightVal = this->right->codegen();
      Value* narrowedValueRight = narrowLtoR(rightVal, Type::getInt1Ty(TheContext));

      Builder.SetInsertPoint(evalRightBB);
      Builder.CreateBr(mergeBB);

      Builder.SetInsertPoint(mergeBB);
      PHINode* phi = Builder.CreatePHI(Builder.getInt1Ty(), 2);
      phi->addIncoming(Builder.getInt1(false), leftFalseBB);
      phi->addIncoming(narrowedValueRight, evalRightBB);

      return phi;
    } else if (op == "||") {
      Value* leftVal = this->left->codegen();
      Value* narrowedValueLeft = narrowLtoR(leftVal, Type::getInt1Ty(TheContext));

      BasicBlock* leftTrueBB = BasicBlock::Create(TheContext, "leftTrue", TheFunction);
      BasicBlock* evalRightBB = BasicBlock::Create(TheContext, "evalRight", TheFunction);
      BasicBlock* mergeBB = BasicBlock::Create(TheContext, "merge", TheFunction);

      Value* leftCond = Builder.CreateICmpNE(narrowedValueLeft, Builder.getInt1(false));

      Builder.CreateCondBr(leftCond, leftTrueBB, evalRightBB);

      Builder.SetInsertPoint(leftTrueBB);
      Builder.CreateBr(mergeBB);

      Builder.SetInsertPoint(evalRightBB);
      Value* rightVal = this->right->codegen();
      Value* narrowedValueRight = narrowLtoR(rightVal, Type::getInt1Ty(TheContext));

      Builder.SetInsertPoint(evalRightBB);
      Builder.CreateBr(mergeBB);

      Builder.SetInsertPoint(mergeBB);
      PHINode* phi = Builder.CreatePHI(Builder.getInt1Ty(), 2);
      phi->addIncoming(Builder.getInt1(true), leftTrueBB);
      phi->addIncoming(narrowedValueRight, evalRightBB);

      return phi;
    }

    Value* leftVal = this->left->codegen();
    Value* rightVal = this->right->codegen();

    Value* widestValueLeft = widenLtoR(leftVal, rightVal->getType());
    Value* widestValueRight = widenLtoR(rightVal, leftVal->getType());

    if (op == "*") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFMul(widestValueLeft, widestValueRight);
      }
      return Builder.CreateMul(widestValueLeft, widestValueRight);
    } else if (op == "/") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFDiv(widestValueLeft, widestValueRight);
      }
      return Builder.CreateSDiv(widestValueLeft, widestValueRight);

    } else if (op == "%") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFRem(widestValueLeft, widestValueRight);
      }
      return Builder.CreateSRem(widestValueLeft, widestValueRight);

    } else if (op == "+") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFAdd(widestValueLeft, widestValueRight);
      }
      return Builder.CreateAdd(widestValueLeft, widestValueRight);

    } else if (op == "-") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFSub(widestValueLeft, widestValueRight);
      }
      return Builder.CreateSub(widestValueLeft, widestValueRight);
    } else if (op == "==") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpUEQ(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpEQ(widestValueLeft, widestValueRight);
    } else if (op == ">=") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpUGE(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpSGE(widestValueLeft, widestValueRight);
    } else if (op == "<=") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpULE(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpSLE(widestValueLeft, widestValueRight);
    } else if (op == "!=") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpONE(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpNE(widestValueLeft, widestValueRight);
    } else if (op == ">") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpUGT(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpSGT(widestValueLeft, widestValueRight);
    } else if (op == "<") {
      if (widestValueLeft->getType()->isFloatTy()) {
        return Builder.CreateFCmpULT(widestValueLeft, widestValueRight);
      }
      return Builder.CreateICmpSLT(widestValueLeft, widestValueRight);
    }
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<BinOp op='" + op + "'>\n";
    str += left->to_string(d + 1);
    str += right->to_string(d + 1);
    addIndents(d, str);
    str += "</BinOp>\n";
    return str;
  };
};

class VarDeclAST : public DeclAST {
public:
  VarDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : DeclAST(std::move(type), std::move(name)){};

  virtual Value* codegen() override {
    // create alloca, add to symbol table, return value
    Type* typePtr = stringToPtrType(type);

    // get the last symbol table, push to that one (this is the nested block we are in)
    // if tables.size() is 0, then we are declaring a global variable
    if (tables.size() == 0) {
      GlobalVariable* gvar = new GlobalVariable(*(TheModule.get()), typePtr, false, GlobalValue::CommonLinkage, nullptr);
      gvar->setAlignment(MaybeAlign(4));
      gvar->setInitializer(getDefaultConst(typePtr));
      globalTable[name] = gvar;
      return gvar;
    } else {
      // check we are not redeclaring the same variable in the same scope
      if (tables[tables.size() - 1].find(name) != tables[tables.size() - 1].end()) {
        throwCodegenError("Found re-declaration of variable " + name, token);
      }

      typePtr->print(llvm::outs());
      AllocaInst* alloca = CreateEntryBlockAlloca(Builder.GetInsertBlock()->getParent(), name, typePtr);
      // alloca->setAlignment(Align(4));
      Builder.CreateStore(getDefaultConst(typePtr), alloca);
      tables[tables.size() - 1][name] = alloca;
      return alloca;
    }
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<VarDecl type='" + type + "' name='" + name + "'>";
    str += "</VarDecl>\n";
    return str;
  };
};

class ParamAST : public VarDeclAST {
public:
  ParamAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : VarDeclAST(std::move(type), std::move(name)){};
  virtual Value* codegen() override { return nullptr; };
  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<Param type='" + type + "' name='" + name + "'>";
    str += "</Param>\n";
    return str;
  };
};

class VarAssignAST : public ExprAST {
public:
  std::string name;
  std::unique_ptr<ExprAST> expression;

  VarAssignAST(ptrVec<ASTNode>&& name, ptrVec<ASTNode>&& expression) {
    castToDerived<ASTNode, ExprAST>(expression, this->expression);

    std::unique_ptr<StorageAST> nameStorage;
    castToDerived<ASTNode, StorageAST>(name, nameStorage);
    this->name = nameStorage->value;
  };

  virtual Value* codegen() override {
    Value* expressionVal = expression->codegen();

    for (int i = tables.size() - 1; i >= 0; i--) {
      if (tables[i].find(name) != tables[i].end()) {
        // need to widen/narrow as required
        Value* widestValue = widenLtoR(expressionVal, tables[i][name]->getAllocatedType());
        Value* narrowedValue = narrowLtoR(widestValue, tables[i][name]->getAllocatedType());
        Builder.CreateStore(narrowedValue, tables[i][name]);
        return narrowedValue;
      }
    }

    if (globalTable.find(name) != globalTable.end()) {
      Builder.CreateStore(expressionVal, globalTable[name]);
      return expressionVal;
    }

    throwCodegenError("Variable " + name + " has not been declared.", token);
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<VarAssign name='" + name + "'>\n";
    str += expression->to_string(d + 1);
    addIndents(d, str);
    str += "</VarAssign>\n";
    return str;
  };
};

class StmtAST : public ASTNode {};

class ExprStmtAST : public StmtAST {
public:
  std::unique_ptr<ExprAST> expression;

  ExprStmtAST(ptrVec<ASTNode>&& expression) { castToDerived<ASTNode, ExprAST>(expression, this->expression); };
  ExprStmtAST(){};

  virtual Value* codegen() override { return expression->codegen(); };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<ExprStmt>\n";
    str += expression->to_string(d + 1);
    addIndents(d, str);
    str += "</ExprStmt>\n";
    return str;
  };
};

class ReturnAST : public StmtAST {
public:
  std::unique_ptr<ExprAST> expression;

  ReturnAST(ptrVec<ASTNode>&& expression) { castToDerived<ASTNode, ExprAST>(expression, this->expression); };
  ReturnAST(){};

  virtual Value* codegen() override {
    // create return instruction, widen if needed
    Function* TheFunction = Builder.GetInsertBlock()->getParent();

    // if void return
    if (!expression) {
      Builder.CreateRetVoid();
      return nullptr;
    } else {
      Value* RetVal = expression->codegen();
      if (compareTypes(TheFunction->getReturnType(), RetVal->getType())) {
        // if the function type is larger or equal than the return value type we can widen
        Value* widestValue = widenLtoR(RetVal, TheFunction->getReturnType());
        Builder.CreateRet(widestValue);
        return RetVal;

      } else {
        throwCodegenError("Function of type " + ptrToStringType(TheFunction->getReturnType()) + " tries to return value of type " + ptrToStringType(RetVal->getType()), token);
      }
    }
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<Return>\n";

    if (expression) {
      str += expression->to_string(d + 1);
    }
    addIndents(d, str);
    str += "</Return>\n";
    return str;
  };
};

class BlockAST : public StmtAST {
  ptrVec<VarDeclAST> localDecls;
  ptrVec<StmtAST> stmts;

public:
  BlockAST(ptrVec<ASTNode>&& localDecls, ptrVec<ASTNode>&& stmts) {
    castToDerived<ASTNode, VarDeclAST>(localDecls, this->localDecls);
    castToDerived<ASTNode, StmtAST>(stmts, this->stmts);
  }

  virtual Value* codegen() override {
    Value* returnVal = nullptr;
    // push new symbol table for this block if we arent in an immediate function block
    if (!isFunctionBlock) {
      tables.push_back(SymbolTable());
    }
    isFunctionBlock = false;

    for (auto& local : localDecls) {
      local->codegen();
    }

    for (auto& stmt : stmts) {
      if (dynamic_cast<ReturnAST*>(stmt.get())) {
        // found return stmt
        stmt->codegen();
        hasCreatedReturn = true;
        // stop any other codegen (stmts should be in order)
        break;
      } else {
        stmt->codegen();
      }
    }
    printTables(tables);
    // pop the symbol table - we are done codegening everything inside this block, ie. we are now leaving the scope
    tables.pop_back();

    return returnVal;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<Block>\n";
    for (auto& local : localDecls) {
      str += local->to_string(d + 1);
    }
    for (auto& s : stmts) {
      str += s->to_string(d + 1);
    }
    addIndents(d, str);
    str += "</Block>\n";
    return str;
  };
};

class IfAST : public StmtAST {
public:
  std::unique_ptr<ExprAST> expression;
  std::unique_ptr<BlockAST> body;
  std::unique_ptr<BlockAST> elseBody;

  IfAST(ptrVec<ASTNode>&& expression, ptrVec<ASTNode>&& body, ptrVec<ASTNode>&& elseBody) {
    castToDerived<ASTNode, ExprAST>(expression, this->expression);
    castToDerived<ASTNode, BlockAST>(body, this->body);
    castToDerived<ASTNode, BlockAST>(elseBody, this->elseBody);
  };

  virtual Value* codegen() override {
    Function* TheFunction = Builder.GetInsertBlock()->getParent();
    BasicBlock* ifBlock = BasicBlock::Create(TheContext, "if", TheFunction);

    BasicBlock* elseBlock;
    if (elseBody) {
      elseBlock = BasicBlock::Create(TheContext, "else", TheFunction);
    }
    BasicBlock* end = BasicBlock::Create(TheContext, "end", TheFunction);

    Value* cond = expression->codegen();
    Value* comp = Builder.CreateICmpNE(cond, Builder.getInt1(false));

    if (elseBody) {
      Builder.CreateCondBr(comp, ifBlock, elseBlock);

    } else {
      Builder.CreateCondBr(comp, ifBlock, end);
    }

    Builder.SetInsertPoint(ifBlock);
    body->codegen();

    if (!hasCreatedReturn) {
      // dont add branch statement otherwise
      Builder.CreateBr(end);
    } else {
      hasCreatedReturn = false;
    }

    if (elseBody) {
      Builder.SetInsertPoint(elseBlock);

      elseBody->codegen();

      if (!hasCreatedReturn) {
        // dont add branch statement otherwise
        Builder.CreateBr(end);
      } else {
        hasCreatedReturn = false;
      }
    }

    Builder.SetInsertPoint(end);

    return nullptr;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<If>\n";
    str += expression->to_string(d + 1);
    str += body->to_string(d + 1);
    str += elseBody->to_string(d + 1);
    addIndents(d, str);
    str += "</If>\n";
    return str;
  };
};

class WhileAST : public StmtAST {
public:
  std::unique_ptr<ExprAST> expression;
  std::unique_ptr<StmtAST> stmt;

  WhileAST(ptrVec<ASTNode>&& expression, ptrVec<ASTNode>&& stmt) {
    castToDerived<ASTNode, ExprAST>(expression, this->expression);
    castToDerived<ASTNode, StmtAST>(stmt, this->stmt);
  };

  virtual Value* codegen() override {
    Function* TheFunction = Builder.GetInsertBlock()->getParent();
    BasicBlock* condBlock = BasicBlock::Create(TheContext, "condition", TheFunction);
    BasicBlock* whileBlock = BasicBlock::Create(TheContext, "while", TheFunction);
    BasicBlock* end = BasicBlock::Create(TheContext, "end", TheFunction);

    Value* cond = expression->codegen();
    Value* comp = Builder.CreateICmpNE(cond, Builder.getInt1(false));

    Builder.CreateBr(condBlock);

    Builder.SetInsertPoint(condBlock);
    cond = expression->codegen();
    comp = Builder.CreateICmpNE(cond, Builder.getInt1(false));

    Builder.CreateCondBr(comp, whileBlock, end);

    Builder.SetInsertPoint(whileBlock);

    stmt->codegen();


    if (!hasCreatedReturn) {
      // dont add branch statement otherwise
      Builder.CreateBr(condBlock);
    }
    else{
      hasCreatedReturn = false;
    }

    Builder.SetInsertPoint(end);

    return nullptr;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<While>";
    str += expression->to_string(d + 1);
    str += stmt->to_string(d + 1);
    addIndents(d, str);
    str += "</While>";
    return str;
  };
};

class ExternAST : public ASTNode {

public:
  std::string type;
  std::string name;
  std::vector<std::unique_ptr<ParamAST>> params;

  ExternAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name, std::vector<std::unique_ptr<ASTNode>>&& params) {
    castToDerived<ASTNode, ParamAST>(params, this->params);

    std::unique_ptr<StorageAST> typeNode;
    std::unique_ptr<StorageAST> identNode;
    castToDerived<ASTNode, StorageAST>(type, typeNode);
    castToDerived<ASTNode, StorageAST>(name, identNode);

    this->name = identNode->value;
    this->type = typeNode->value;
  };

  virtual Value* codegen() override {
    // Make the function type:
    std::vector<Type*> types;
    for (auto& param : params) {
      types.push_back(stringToPtrType(param->type));
    }

    FunctionType* FT = FunctionType::get(stringToPtrType(type), types, false);
    Function* F = Function::Create(FT, Function::ExternalLinkage, name, TheModule.get());
    // Set names for all arguments.
    unsigned i = 0;
    std::unordered_set<std::string> seen;
    for (auto& Arg : F->args()) {
      if (seen.find(params[i]->name) != seen.end()) {
        throwCodegenError("Found duplicate parameter name " + params[i]->name + " in function " + name, token);
      }
      seen.insert(params[i]->name);
      Arg.setName(params[i]->name);
      i++;
    }

    return F;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<Prototype type='" + type + "' name='" + name + "'>\n";
    for (auto& param : params) {
      str += param->to_string(d + 1);
    }
    addIndents(d, str);
    str += "</Prototype>\n";
    return str;
  };
};

class FuncDeclAST : public DeclAST {
public:
  std::unique_ptr<ExternAST> prototype;
  std::unique_ptr<BlockAST> block;

  FuncDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name, ptrVec<ASTNode>&& params, ptrVec<ASTNode>&& block) {
    prototype = std::make_unique<ExternAST>(std::move(type), std::move(name), std::move(params));
    castToDerived<ASTNode, BlockAST>(block, this->block);
  };

  FuncDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : DeclAST(std::move(type), std::move(name)){};

  virtual Value* codegen() override {
    // set num blocks and num returns to 0 again, new function
    Function* TheFunction = TheModule->getFunction(prototype->name);
    if (!TheFunction)
      TheFunction = (Function*)prototype->codegen();
    if (!TheFunction)
      return nullptr;

    BasicBlock* BB = BasicBlock::Create(TheContext, "entry", TheFunction);
    Builder.SetInsertPoint(BB);

    // make a new symbol table, push to tables, record argument names
    SymbolTable newTable;
    for (auto& Arg : TheFunction->args()) {
      AllocaInst* Alloca = CreateEntryBlockAlloca(TheFunction, std::string(Arg.getName()), Arg.getType());
      Builder.CreateStore(&Arg, Alloca);
      newTable[std::string(Arg.getName())] = Alloca;
    }

    tables.push_back(newTable);

    // so that we keep the same scope table when we are codegening the block
    isFunctionBlock = true;

    // codegen the body
    block->codegen();

    // every block will either branch or return apart from this last one POTENTIALLY (if there is nothing after an if/while statement end block)
    if (Builder.GetInsertBlock()->empty()) {
      // we are always allowed to pad the function if its void
      if (TheFunction->getReturnType()->isVoidTy()) {
        Builder.CreateRetVoid();
      } else {
        //im going to return a default value as this is intuitive for the user :)))))))))))
        Builder.CreateRet(getDefaultConst(TheFunction->getReturnType()));
      }
    }

    return TheFunction;
  };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += "<FuncDecl>\n";

    str += prototype->to_string(d + 1);

    str += block->to_string(d + 1);
    addIndents(d, str);
    str += "</FuncDecl>\n";

    return str;
  };
};

class FactorAST : public ExprAST {
public:
  std::unique_ptr<PrimaryAST> expression;
  FactorAST(ptrVec<ASTNode> expression) { castToDerived<ASTNode, PrimaryAST>(expression, this->expression); };

  virtual Value* codegen() override { return expression->codegen(); };

  virtual std::string to_string(int d) const override {
    std::string str = "";
    addIndents(d, str);
    str += expression->to_string(d + 1);

    return str;
  };
};

class PartialFuncDeclAST : public ASTNode {
public:
  ptrVec<ASTNode> params;
  ptrVec<ASTNode> block;

  PartialFuncDeclAST(ptrVec<ASTNode>&& params, ptrVec<ASTNode>&& block) : params(std::move(params)), block(std::move(block)){};

  PartialFuncDeclAST(){};

  virtual Value* codegen() override { return nullptr; };
};

class ProgramAST : public ASTNode {
  std::vector<std::unique_ptr<ExternAST>> externList;
  std::vector<std::unique_ptr<DeclAST>> declList;

public:
  ProgramAST(std::vector<std::unique_ptr<ASTNode>>&& externList, std::vector<std::unique_ptr<ASTNode>>&& declList) {
    castToDerived<ASTNode, ExternAST>(externList, this->externList);
    castToDerived<ASTNode, DeclAST>(declList, this->declList);
  }

  virtual std::string to_string(int d) const override {
    std::string str = "<Program>\n";
    for (auto& externNode : externList) {
      str += externNode->to_string(d + 1);
    }
    for (auto& declNode : declList) {
      str += declNode->to_string(d + 1);
    }
    str += "</Program>";

    return str;
  }

  virtual Value* codegen() override {
    for (auto& externNode : externList) {
      externNode->codegen();
    }
    for (auto& declNode : declList) {
      declNode->codegen();
    }

    return nullptr;
  };
};

std::unordered_map<std::string, std::function<std::vector<std::unique_ptr<ASTNode>>()>> functionMap;
std::unordered_map<int, std::string> typeToString = {
    {TOKEN_TYPE::IDENT, "IDENT"}, {TOKEN_TYPE::INT_LIT, "INT_LIT"}, {TOKEN_TYPE::FLOAT_LIT, "FLOAT_LIT"}, {TOKEN_TYPE::BOOL_LIT, "BOOL_LIT"}};
/* add other AST nodes as nessasary */

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */
void printMap(const std::map<std::string, std::vector<std::unique_ptr<ASTNode>>>& myMap) {
  for (const auto& pair : myMap) {
    const auto& key = pair.first;
    const auto& nodeList = pair.second;

    std::cout << "Key: " << key + " " << nodeList.size() << "\n";
  }
}

using nonTerminalInfo = std::map<std::string, std::vector<std::unique_ptr<ASTNode>>>;

nonTerminalInfo nonterminal(const std::string& name) {
  bool foundMatch = false;
  std::unordered_set<std::string> expected;
  nonTerminalInfo result;
  std::vector<std::string> epsilonRule;

  std::string typeLiteralString = typeToString.find(CurTok.type) != typeToString.end() ? typeToString[CurTok.type] : "";

  if (productions.find(name) != productions.end()) {
    auto& rules = productions[name];

    for (auto& rule : rules) {
      std::string firstSymbol = rule[0];
      expected.insert(firstSets[firstSymbol].begin(), firstSets[firstSymbol].end());

      // incase we need to use follow set n shit
      // this is assuming theres only one epsilon rule to choose (which there should be, most stuff is LL(1))
      if (firstSets[firstSymbol].find("''") != firstSets[firstSymbol].end()) {
        epsilonRule = rule;
      }

      if (firstSets[firstSymbol].find(CurTok.lexeme) != firstSets[firstSymbol].end() || firstSets[firstSymbol].find(typeLiteralString) != firstSets[firstSymbol].end()) {

        // hack to get expr working
        if (name == "expr") {
          // expr ::= IDENT "=" expr
          if (rule.size() > 1) {
            if (peekNext().lexeme != "=") {
              continue;
            }
          }
          // expr ::= rval
          else {
            if (peekNext().lexeme == "=") {
              continue;
            }
          }
        }

        foundMatch = true;
        for (std::string symbol : rule) {
          // shouldn't be any overlap in firstSets (except for when we get to expr)
          // so this should only 'match' one rule
          typeLiteralString = typeToString.find(CurTok.type) != typeToString.end() ? typeToString[CurTok.type] : "";

          std::string symbolNoQuotes = removeCharacter(symbol, '"');
          if (isTerminal(symbol) && (symbolNoQuotes == CurTok.lexeme || symbolNoQuotes == typeLiteralString)) {

            result[symbolNoQuotes].push_back(std::make_unique<StorageAST>(CurTok.lexeme));
            getNextToken();

          } else if (!isTerminal(symbol)) {
            result[symbol] = functionMap[symbol]();
            // add token properties
            for (auto& node : result[symbol]) {
              node->token = CurTok;
            }
          } else {
            // symbol was a terminal but didnt match CurTok
            throwParserError({symbol}, CurTok.lexeme);
          }
        }
      }

      if (foundMatch) {
        break;
      }
    }

    if (!foundMatch) {
      // see if we should use an available epsilon production
      //'using' the production just entails returning an empty result map for this nonterminal
      if (!(!epsilonRule.empty() && (followSets[name].find(CurTok.lexeme) != followSets[name].end() || followSets[name].find(typeLiteralString) != followSets[name].end()))) {
        throwParserError(expected, CurTok.lexeme);
      } else {
      }
    }
  } else {
    std::cout << "Production not found for " + name << std::endl;
    exit(1);
  }

  return result;
}

/* program ::= extern_list decl_list
program ::= decl_list */

ptrVec<ASTNode> program() {
  // first production rule so we need to populate curtok
  getNextToken();
  nonTerminalInfo info = nonterminal("program");

  ptrVec<ASTNode> res;
  res.push_back(std::make_unique<ProgramAST>(std::move(info["extern_list"]), std::move(info["decl_list"])));
  return res;
}

// extern_list ::= extern extern_list'
ptrVec<ASTNode> extern_list() {
  nonTerminalInfo info = nonterminal("extern_list");

  ptrVec<ASTNode> externList = std::move(info["extern_list'"]);

  externList.push_back(std::move(info["extern"][0]));
  return externList;
}

// extern_list' ::= extern extern_list'
// extern_list' ::= ''
// if we don't need to return derived nodes just yet, then don't. More efficient. Otherwise we will be copying nodes
ptrVec<ASTNode> extern_list_prime() {
  nonTerminalInfo info = nonterminal("extern_list'");
  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }
  ptrVec<ASTNode> externList = std::move(info["extern_list'"]);

  externList.push_back(std::move(info["extern"][0]));

  return externList;
}

// extern ::= "extern" type_spec IDENT "(" params ")" ";"
ptrVec<ASTNode> extern_() {

  nonTerminalInfo info = nonterminal("extern");

  ptrVec<ASTNode> res;
  res.push_back(std::make_unique<ExternAST>(std::move(info["type_spec"]), std::move(info["IDENT"]), std::move(info["params"])));

  return res;
}

// decl_list ::= decl decl_list'
ptrVec<ASTNode> decl_list() {
  nonTerminalInfo info = nonterminal("decl_list");

  ptrVec<ASTNode> declList = std::move(info["decl_list'"]);

  declList.push_back(std::move(info["decl"][0]));
  return declList;
}

// decl_list' ::= decl decl_list'
// decl_list' ::= ''
ptrVec<ASTNode> decl_list_prime() {
  nonTerminalInfo info = nonterminal("decl_list'");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> declList = std::move(info["decl_list'"]);

  declList.push_back(std::move(info["decl"][0]));

  return declList;
}

// decl ::= var_type IDENT decl'
// decl ::= "void" IDENT "(" params ")" block
ptrVec<ASTNode> decl() {

  nonTerminalInfo info = nonterminal("decl");

  ptrVec<ASTNode> type;
  ptrVec<ASTNode>& identifier = info["IDENT"];
  ptrVec<ASTNode> res;

  // get type
  if (info.find("var_type") != info.end()) {
    // var declaration
    type = std::move(info["var_type"]);
  } else {
    type.push_back(std::make_unique<StorageAST>("void"));
  }

  // fill in params and block if a function declaration

  if (info.find("decl'") != info.end()) {
    std::unique_ptr<PartialFuncDeclAST> halfBakedFuncDecl;

    castToDerived<ASTNode, PartialFuncDeclAST>(info["decl'"], halfBakedFuncDecl);

    if (halfBakedFuncDecl->block.empty()) {
      // variable declaration
      res.push_back(std::make_unique<VarDeclAST>(std::move(type), std::move(identifier)));
    } else {
      // half baked from decl' with params and block
      // now add type and identifier
      res.push_back(std::make_unique<FuncDeclAST>(std::move(type), std::move(identifier), std::move(halfBakedFuncDecl->params), std::move(halfBakedFuncDecl->block)));
    }

  } else if (info.find("params") != info.end()) {
    // build a whole new func decl AST here
    res.push_back(std::make_unique<FuncDeclAST>(std::move(type), std::move(identifier), std::move(info["params"]), std::move(info["block"])));
  }

  return res;
}

// decl' ::= "(" params ")" block
// decl' ::= ";"
ptrVec<ASTNode> decl_prime() {
  nonTerminalInfo info = nonterminal("decl'");
  ptrVec<ASTNode> res;

  if (info.find(";") != info.end()) {
    // variable decl, push an empty func decl ast to signal this
    res.push_back(std::make_unique<PartialFuncDeclAST>());
  } else {
    // pass a half baked func decl back up
    res.push_back(std::make_unique<PartialFuncDeclAST>(std::move(info["params"]), std::move(info["block"])));
  }

  return res;
}

ptrVec<ASTNode> type_spec() {
  nonTerminalInfo info = nonterminal("type_spec");

  if (info.find("var_type") != info.end()) {
    return std::move(info["var_type"]);
  } else {
    return std::move(info["void"]);
  }
}

ptrVec<ASTNode> var_type() {
  nonTerminalInfo info = nonterminal("var_type");
  auto it = info.begin();
  return std::move(it->second);
}

ptrVec<ASTNode> params() {
  nonTerminalInfo info = nonterminal("params");

  // in minic, no parameters and 'void' mean the same thing
  if (info.size() == 0 || info.find("void") != info.end()) {
    return ptrVec<ASTNode>{};
  } else {
    return std::move(info["param_list"]);
  }
}

ptrVec<ASTNode> param_list() {
  nonTerminalInfo info = nonterminal("param_list");

  ptrVec<ASTNode> paramList = std::move(info["param_list'"]);

  paramList.push_back(std::move(info["param"][0]));

  return paramList;
}

ptrVec<ASTNode> param_list_prime() {
  nonTerminalInfo info = nonterminal("param_list'");
  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }
  ptrVec<ASTNode> paramList = std::move(info["param_list'"]);

  paramList.push_back(std::move(info["param"][0]));

  return paramList;
}

ptrVec<ASTNode> param() {
  nonTerminalInfo info = nonterminal("param");
  ptrVec<ASTNode> temp;
  temp.push_back(std::make_unique<ParamAST>(std::move(info["var_type"]), std::move(info["IDENT"])));
  return temp;
}

ptrVec<ASTNode> block() {
  nonTerminalInfo info = nonterminal("block");

  ptrVec<ASTNode> temp;
  temp.push_back(std::make_unique<BlockAST>(std::move(info["local_decls"]), std::move(info["stmt_list"])));
  return temp;
}

ptrVec<ASTNode> local_decls() {
  nonTerminalInfo info = nonterminal("local_decls");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> localDecls = std::move(info["local_decls"]);

  localDecls.push_back(std::move(info["local_decl"][0]));
  return localDecls;
}

ptrVec<ASTNode> local_decl() {
  nonTerminalInfo info = nonterminal("local_decl");

  ptrVec<ASTNode> temp;
  temp.push_back(std::make_unique<VarDeclAST>(std::move(info["var_type"]), std::move(info["IDENT"])));
  return temp;
}

ptrVec<ASTNode> stmt_list() {
  nonTerminalInfo info = nonterminal("stmt_list");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> stmts = std::move(info["stmt_list'"]);
  stmts.push_back(std::move(info["stmt"][0]));

  return stmts;
}

ptrVec<ASTNode> stmt_list_prime() {
  nonTerminalInfo info = nonterminal("stmt_list'");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> stmtList = std::move(info["stmt_list'"]);

  stmtList.push_back(std::move(info["stmt"][0]));

  return stmtList;
}

ptrVec<ASTNode> stmt() {
  nonTerminalInfo info = nonterminal("stmt");
  auto it = info.begin();

  return std::move(it->second);
}

ptrVec<ASTNode> expr_stmt() {
  nonTerminalInfo info = nonterminal("expr_stmt");

  ptrVec<ASTNode> res;

  if (info.find("expr") != info.end()) {
    res.push_back(std::make_unique<ExprStmtAST>(std::move(info["expr"])));
  } else {
    res.push_back(std::make_unique<ExprStmtAST>());
  }

  return res;
}

ptrVec<ASTNode> while_stmt() {
  nonTerminalInfo info = nonterminal("while_stmt");

  ptrVec<ASTNode> res;
  res.push_back(std::make_unique<WhileAST>(std::move(info["expr"]), std::move(info["stmt"])));

  return res;
}

ptrVec<ASTNode> if_stmt() {
  nonTerminalInfo info = nonterminal("if_stmt");

  ptrVec<ASTNode> res;
  res.push_back(std::make_unique<IfAST>(std::move(info["expr"]), std::move(info["block"]), std::move(info["else_stmt"])));

  return res;
}

ptrVec<ASTNode> else_stmt() {
  nonTerminalInfo info = nonterminal("else_stmt");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  return std::move(info["block"]);
}

ptrVec<ASTNode> return_stmt() {
  nonTerminalInfo info = nonterminal("return_stmt");
  return std::move(info["return_stmt'"]);
}

ptrVec<ASTNode> return_stmt_prime() {
  nonTerminalInfo info = nonterminal("return_stmt'");

  ptrVec<ASTNode> res;
  if (info.find("expr") != info.end()) {
    res.push_back(std::make_unique<ReturnAST>(std::move(info["expr"])));
  } else {
    res.push_back(std::make_unique<ReturnAST>());
  }

  return res;
}

ptrVec<ASTNode> expr() {
  nonTerminalInfo info = nonterminal("expr");

  ptrVec<ASTNode> res;
  if (info.find("IDENT") != info.end()) {
    res.push_back(std::make_unique<VarAssignAST>(std::move(info["IDENT"]), std::move(info["expr"])));
  } else {
    // BinOpExpr node is returned
    res.push_back(std::move(info["rval_or"][0]));
  }

  return res;
}

ptrVec<ASTNode> binOp_expTemplate(std::string prodName, std::string secondTerm) {
  nonTerminalInfo info = nonterminal(prodName);
  ptrVec<ASTNode>& first = info[secondTerm];
  ptrVec<ASTNode>& second = info[prodName + "'"];

  ptrVec<ASTNode> res;

  if (second.empty()) {
    res = std::move(first);
  } else {
    std::unique_ptr<BinOpAST> totalParent;
    castToDerived<ASTNode, BinOpAST>(second, totalParent);

    if (!totalParent->leftmostChild) {
      totalParent->left = std::move(first[0]);
      std::shared_ptr<BinOpAST> derivedLeft = std::static_pointer_cast<BinOpAST>(totalParent->left);
      totalParent->leftmostChild = derivedLeft;
    } else {
      totalParent->leftmostChild->left = std::move(first[0]);
    }

    res.push_back(std::move(totalParent));
  }

  return res;
}

ptrVec<ASTNode> binOp_primeTemplate(std::string prodName, std::string secondTerm) {
  nonTerminalInfo info = nonterminal(prodName);

  // epsilon production
  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> second = std::move(info[secondTerm]);
  info.erase(secondTerm);
  ptrVec<ASTNode> third = std::move(info[prodName]);
  info.erase(prodName);

  // will now be the symbol
  auto symbolPos = info.begin();

  std::unique_ptr<BinOpAST> parent;
  castToDerived<ASTNode, BinOpAST>(third, parent);

  std::unique_ptr<BinOpAST> leftChild = std::make_unique<BinOpAST>(symbolPos->first, std::move(second));

  if (!parent) {
    parent = std::move(leftChild);
  } else {
    if (!parent->leftmostChild) {
      parent->left = std::move(leftChild);
      std::shared_ptr<BinOpAST> derivedLeft = std::static_pointer_cast<BinOpAST>(parent->left);
      parent->leftmostChild = derivedLeft;
    } else {
      parent->leftmostChild->left = std::move(leftChild);
      std::shared_ptr<BinOpAST> derivedLeft = std::static_pointer_cast<BinOpAST>(parent->leftmostChild->left);
      parent->leftmostChild = derivedLeft;
    }
  }

  ptrVec<ASTNode> res;
  // return back up the overall parent
  res.push_back(std::move(parent));

  return res;
}

// rval_or ::= and_exp rval_or'
ptrVec<ASTNode> rval_or() { return binOp_expTemplate("rval_or", "and_exp"); }

// rval_or' ::= "||" and_exp rval_or'
// rval_or' ::= ''
ptrVec<ASTNode> rval_or_prime() { return binOp_primeTemplate("rval_or'", "and_exp"); }

ptrVec<ASTNode> and_exp() { return binOp_expTemplate("and_exp", "equality_exp"); }

ptrVec<ASTNode> and_exp_prime() { return binOp_primeTemplate("and_exp'", "equality_exp"); }

ptrVec<ASTNode> equality_exp() { return binOp_expTemplate("equality_exp", "relational_exp"); }

ptrVec<ASTNode> equality_exp_prime() { return binOp_primeTemplate("equality_exp'", "relational_exp"); }

ptrVec<ASTNode> relational_exp() { return binOp_expTemplate("relational_exp", "additive_exp"); }

ptrVec<ASTNode> relational_exp_prime() { return binOp_primeTemplate("relational_exp'", "additive_exp"); }

ptrVec<ASTNode> additive_exp() { return binOp_expTemplate("additive_exp", "multiplicative_exp"); }

ptrVec<ASTNode> additive_exp_prime() { return binOp_primeTemplate("additive_exp'", "multiplicative_exp"); }

ptrVec<ASTNode> multiplicative_exp() { return binOp_expTemplate("multiplicative_exp", "factor"); }

ptrVec<ASTNode> multiplicative_exp_prime() { return binOp_primeTemplate("multiplicative_exp'", "factor"); }

ptrVec<ASTNode> factor() {
  nonTerminalInfo info = nonterminal("factor");
  ptrVec<ASTNode> res;

  if (info.find("primary") != info.end()) {
    res.push_back(std::make_unique<FactorAST>(std::move(info["primary"])));
  } else {
    ptrVec<ASTNode> factor = std::move(info["factor"]);
    info.erase("factor");

    std::string symbol = info.begin()->first;
    res.push_back(std::make_unique<NegationAST>(symbol, std::move(factor)));
  }

  return res;
}

ptrVec<ASTNode> primary() {
  nonTerminalInfo info = nonterminal("primary");
  ptrVec<ASTNode> res;

  if (info.find("IDENT") != info.end()) {
    ptrVec<ASTNode>& ident = info["IDENT"];
    if (info["primary'"].size() == 0) {
      res.push_back(std::make_unique<VarCallAST>(std::move(ident)));
    } else {
      // pop the last element ')' and move remaniing arguments
      info["primary'"].pop_back();
      res.push_back(std::make_unique<FuncCallAST>(std::move(ident), std::move(info["primary'"])));
    }
  } else if (info.find("INT_LIT") != info.end()) {
    res.push_back(std::make_unique<IntAST>(std::move(info["INT_LIT"])));
  } else if (info.find("FLOAT_LIT") != info.end()) {
    res.push_back(std::make_unique<FloatAST>(std::move(info["FLOAT_LIT"])));
  } else if (info.find("BOOL_LIT") != info.end()) {
    res.push_back(std::make_unique<BoolAST>(std::move(info["BOOL_LIT"])));
  } else if (info.find("expr") != info.end()) {
    res.push_back(std::move(info["expr"][0]));
  }

  return res;
}

ptrVec<ASTNode> primary_prime() {
  nonTerminalInfo info = nonterminal("primary'");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> res;
  // primary prime can actually be empty OR just have no arguments - big difference
  // add the terminal ')' so we can signify a lack of arguments instead of just nothing if no args are present
  res = std::move(info["args"]);
  res.push_back(std::move(info[")"][0]));
  return res;
}

ptrVec<ASTNode> args() {
  nonTerminalInfo info = nonterminal("args");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  return std::move(info["arg_list"]);
}

ptrVec<ASTNode> arg_list() {
  nonTerminalInfo info = nonterminal("arg_list");

  ptrVec<ASTNode> argList = std::move(info["arg_list'"]);
  argList.push_back(std::move(info["expr"][0]));

  return argList;
}

ptrVec<ASTNode> arg_list_prime() {
  nonTerminalInfo info = nonterminal("arg_list'");

  if (info.size() == 0) {
    return ptrVec<ASTNode>{};
  }

  ptrVec<ASTNode> argList = std::move(info["arg_list'"]);
  argList.push_back(std::move(info["expr"][0]));

  return argList;
}

static std::unique_ptr<ASTNode> parser() { return std::move(program()[0]); }

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const ASTNode& ast) {
  os << ast.to_string(0);
  return os;
}

//--------------

static void initialiseFunctionMap() {
  functionMap["extern"] = extern_;
  functionMap["extern_list'"] = extern_list_prime;
  functionMap["extern_list"] = extern_list;
  functionMap["decl_list'"] = decl_list_prime;
  functionMap["decl_list"] = decl_list;
  functionMap["decl'"] = decl_prime;
  functionMap["decl"] = decl;
  functionMap["type_spec"] = type_spec;
  functionMap["var_type"] = var_type;
  functionMap["params"] = params;
  functionMap["param_list'"] = param_list_prime;
  functionMap["param_list"] = param_list;
  functionMap["param"] = param;
  functionMap["block"] = block;
  functionMap["local_decls"] = local_decls;
  functionMap["local_decl"] = local_decl;
  functionMap["stmt_list'"] = stmt_list_prime;
  functionMap["stmt_list"] = stmt_list;
  functionMap["stmt"] = stmt;
  functionMap["expr_stmt"] = expr_stmt;
  functionMap["while_stmt"] = while_stmt;
  functionMap["if_stmt"] = if_stmt;
  functionMap["else_stmt"] = else_stmt;
  functionMap["return_stmt"] = return_stmt;
  functionMap["return_stmt'"] = return_stmt_prime;
  functionMap["expr"] = expr;
  functionMap["rval_or"] = rval_or;
  functionMap["rval_or'"] = rval_or_prime;
  functionMap["and_exp"] = and_exp;
  functionMap["and_exp'"] = and_exp_prime;
  functionMap["equality_exp"] = equality_exp;
  functionMap["equality_exp'"] = equality_exp_prime;
  functionMap["relational_exp"] = relational_exp;
  functionMap["relational_exp'"] = relational_exp_prime;
  functionMap["additive_exp"] = additive_exp;
  functionMap["additive_exp'"] = additive_exp_prime;
  functionMap["factor"] = factor;
  functionMap["multiplicative_exp"] = multiplicative_exp;
  functionMap["multiplicative_exp'"] = multiplicative_exp_prime;
  functionMap["primary"] = primary;
  functionMap["primary'"] = primary_prime;
  functionMap["args"] = args;
  functionMap["arg_list'"] = arg_list_prime;
  functionMap["arg_list"] = arg_list;
};

//---------------

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char** argv) {

  if (argc == 2) {
    pFile = fopen(argv[1], "r");
    if (pFile == NULL)
      perror("Error opening file");
  } else {
    std::cout << "Usage: ./code InputFile\n";
    return 1;
  }

  lineNo = 1;
  columnNo = 1;

  readGrammar();
  computeFirst();
  //printFirst();

  computeFollow();

   //printFollow();
  initialiseFunctionMap();

  fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.

  fprintf(stderr, "Parsing Finished\n");

  std::unique_ptr<ASTNode> programNode = std::move(parser());
  llvm::outs() << *programNode << "\n";
  //********************* Start printing final IR **************************
  //  Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }

  // TheModule->print(errs(), nullptr); // print IR to terminal
  programNode->codegen();
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
