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
  // add error handling?
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

static TOKEN peekNext(int x) {
  populateBuffer();
  if (x == 1) {
    return tok_buffer.front();
  } else {
    return tok_buffer[1];
  }
}

static TOKEN peekNext() {
  populateBuffer();
  return tok_buffer.front();
}

// useless af currently
static void putBackToken(TOKEN tok) { tok_buffer.push_front(tok); }

static void throwError(const std::unordered_set<std::string>& expected, std::string message = "") { throw std::runtime_error("error: " + message); }
//===----------------------------------------------------------------------===//
// AST nodes
//===----------------------------------------------------------------------===//

template <typename T> using ptrVec = std::vector<std::unique_ptr<T>>;

// we also reverse when casting a vector of pointers to another vector due to the way we build up our left recursions backwards
template <typename Base, typename Derived>
void castToDerived(std::vector<std::unique_ptr<Base>>& nodes, std::vector<std::unique_ptr<Derived>>& target) {
  for (int i = nodes.size() - 1; i >= 0; i++) {
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

/// ASTNode - Base class for all AST nodes.
class ASTNode {
public:
  // destructor
  virtual ~ASTNode() = default;
  virtual Value* codegen() = 0;
  virtual std::string to_string() const { return ""; };
};

/// IntASTNode - Class for integer literals like 1, 2, 10,
class IntAST : public ASTNode {
  int Val;
  TOKEN Tok;
  std::string Name;

public:
  IntAST(TOKEN tok, int val) : Val(val), Tok(tok){};
  virtual Value* codegen() override;
  virtual std::string to_string() const override { return std::to_string(Val); };
};

class StorageAST : public ASTNode {

public:
  std::string value;
  StorageAST(std::string value) : value(value){};
  Value* codegen() {}
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

  std::string to_string() const {}
  virtual Value* codegen() {}
};

class VarDeclAST : public DeclAST {
public:
  VarDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : DeclAST(std::move(type), std::move(name)){};
  std::string to_string() const {}
  Value* codegen() {}
};

class ParamAST : public VarDeclAST {
public:
  ParamAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : VarDeclAST(std::move(type), std::move(name)){};
  std::string to_string() const {}
  Value* codegen() {}
};

class StmtAST : public ASTNode {};

class BlockAST : public ASTNode {
  ptrVec<VarDeclAST> localDecls;
  ptrVec<StmtAST> stmts;

public:
  BlockAST(ptrVec<ASTNode>&& localDecls, ptrVec<ASTNode>&& stmts) {
    castToDerived<ASTNode, VarDeclAST>(localDecls, this->localDecls);
    castToDerived<ASTNode, StmtAST>(stmts, this->stmts);
  }
  std::string to_string() const {}
  Value* codegen() {}
};

class ExternAST : public ASTNode {
  std::string type;
  std::string name;
  std::vector<std::unique_ptr<ParamAST>> params;

public:
  ExternAST(std::string type, std::string name, std::vector<std::unique_ptr<ASTNode>>&& params) : type(type), name(name) {
    castToDerived<ASTNode, ParamAST>(params, this->params);
  };

  std::string to_string() const {}
  Value* codegen() {}
};

class FuncDeclAST : public DeclAST {
public:
  std::vector<std::unique_ptr<ParamAST>> params;
  std::unique_ptr<BlockAST> block;

  FuncDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name, ptrVec<ASTNode>&& params, ptrVec<ASTNode>&& block) : DeclAST(std::move(type), std::move(name)) {
    castToDerived<ASTNode, ParamAST>(params, this->params);
    castToDerived<ASTNode, BlockAST>(block, this->block);
  };

   FuncDeclAST(ptrVec<ASTNode>&& type, ptrVec<ASTNode>&& name) : DeclAST(std::move(type), std::move(name)) {
  };


  std::string to_string() const {}
  Value* codegen() {}
};

class PartialFuncDeclAST: public ASTNode {
  public:
    ptrVec<ASTNode> params;
    ptrVec<ASTNode> block;

    PartialFuncDeclAST(ptrVec<ASTNode>&& params, ptrVec<ASTNode>&& block): params(std::move(params)), block(std::move(block)) {
    };

    PartialFuncDeclAST(){};

    Value* codegen() {}
};

class ProgramAST : public ASTNode {
  std::vector<std::unique_ptr<ExternAST>> externList;
  std::vector<std::unique_ptr<DeclAST>> declList;

public:
  ProgramAST(std::vector<std::unique_ptr<ASTNode>>&& externList, std::vector<std::unique_ptr<ASTNode>>&& declList) {
    castToDerived<ASTNode, ExternAST>(externList, this->externList);
    castToDerived<ASTNode, DeclAST>(declList, this->declList);
  }

  virtual std::string to_string() const override {
    std::cout << "program: {" << std::endl;
    for (auto& externNode : externList) {
      externNode->to_string();
    }
    for (auto& declNode : declList) {
      declNode->to_string();
    }
    std::cout << "}" << std::endl;
  }

  Value* codegen() {}
};

std::unordered_map<std::string, std::function<std::vector<std::unique_ptr<ASTNode>>()>> functionMap;
std::unordered_map<int, std::string> typeToString = {
    {TOKEN_TYPE::IDENT, "IDENT"}, {TOKEN_TYPE::INT_LIT, "INT_LIT"}, {TOKEN_TYPE::FLOAT_LIT, "FLOAT_LIT"}, {TOKEN_TYPE::BOOL_LIT, "BOOL_LIT"}};
/* add other AST nodes as nessasary */

//===----------------------------------------------------------------------===//
// Recursive Descent Parser - Function call for each production
//===----------------------------------------------------------------------===//

/* Add function calls for each production */

using nonTerminalInfo = std::map<std::string, std::vector<std::unique_ptr<ASTNode>>>;

nonTerminalInfo nonterminal(const std::string& name) {
  bool foundMatch = false;
  std::unordered_set<std::string> expected;
  nonTerminalInfo result;
  std::vector<std::string> epsilonRule;

  std::string typeLiteralString = typeToString.contains(CurTok.type) ? typeToString[CurTok.type] : "";

  if (productions.contains(name)) {
    auto& rules = productions[name];

    for (auto& rule : rules) {
      std::string firstSymbol = rule[0];
      expected.insert(firstSets[firstSymbol].begin(), firstSets[firstSymbol].end());

      // incase we need to use follow set n shit
      // this is assuming theres only one epsilon rule to choose (which there should be, most stuff is LL(1))
      if (firstSets[firstSymbol].contains("''")) {
        epsilonRule = rule;
      }

      if (firstSets[firstSymbol].contains(CurTok.lexeme) || firstSets[firstSymbol].contains(typeLiteralString)) {
        foundMatch = true;
        for (std::string symbol : rule) {
          // shouldn't be any overlap in firstSets (except for when we get to expr)
          // so this should only 'match' one rule
          if (isTerminal(symbol) && (symbol == CurTok.lexeme || symbol == typeLiteralString)) {

            result[symbol].push_back(std::make_unique<StorageAST>(CurTok.lexeme));

            getNextToken();
            typeLiteralString = typeToString.contains(CurTok.type) ? typeToString[CurTok.type] : "";

          } else if (!isTerminal(symbol)) {
            result[symbol] = functionMap[symbol]();
          } else {
            // symbol was a terminal but didnt match CurTok
            throwError({symbol});
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
      if (!(!epsilonRule.empty() && (followSets[name].contains(CurTok.lexeme) || followSets[name].contains(typeLiteralString)))) {
        throwError(expected);
      }
    }
  } else {
    throwError({}, "Production not found for " + name);
  }

  return result;
}

/* program ::= extern_list decl_list
program ::= decl_list */

std::unique_ptr<ProgramAST> program() {
  // first production rule so we need to populate curtok
  getNextToken();
  nonTerminalInfo info = nonterminal("program");

  return std::make_unique<ProgramAST>(std::move(info["extern_list"]), std::move(info["decl_list"]));
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
// from vector to vector everytime we upcast and downcast. eugh.
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

  ptrVec<StorageAST> typeNode;
  ptrVec<StorageAST> identNode;
  castToDerived<ASTNode, StorageAST>(info["type_spec"], typeNode);
  castToDerived<ASTNode, StorageAST>(info["IDENT"], identNode);

  ptrVec<ASTNode> res;
  res.push_back(std::make_unique<ExternAST>(typeNode[0]->value, identNode[0]->value, std::move(info["params"])));

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
  std::unique_ptr<BlockAST> block;
  ptrVec<ASTNode>& identifier = info["IDENT"];
  ptrVec<ASTNode> res;

  // get type
  if (info.contains("var_type")) {
    // var declaration
    type = std::move(info["var_type"]);
  } else {
    type.push_back(std::make_unique<StorageAST>("void"));
  }

  // fill in params and block if a function declaration

  if (info.contains("decl'")) {
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

  } else if (info.contains("params")) {
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

  if (info.contains(";")) {
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

  if (info.contains("var_type")) {
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
  if (info.size() == 0 || info.contains("void")) {
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

ptrVec<ASTNode> stmt() {}

static void parser() {}

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
static std::unique_ptr<Module> TheModule;

//===----------------------------------------------------------------------===//
// AST Printer
//===----------------------------------------------------------------------===//

inline llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const ASTNode& ast) {
  os << ast.to_string();
  return os;
}

//--------------

static void initialiseFunctionMap() {
  functionMap["extern"] = extern_;
  functionMap["extern_list'"] = extern_list_prime;
  functionMap["extern_list"] = extern_list;
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

  // initialize line number and column numbers to zero
  lineNo = 1;
  columnNo = 1;
  /*  // get the first token
   getNextToken();
   while (CurTok.type != EOF_TOK)
   {
     fprintf(stderr, "Token: %s with type %d\n", CurTok.lexeme.c_str(),
             CurTok.type);
     getNextToken();
   } */

  readGrammar("grammar.txt");

  computeFirst();
  printFirst();
  computeFollow();
  printFollow();

  //initialiseFunctionMap(); 

  return 0;

  fprintf(stderr, "Lexer Finished\n");

  // Make the module, which holds all the code.
  TheModule = std::make_unique<Module>("mini-c", TheContext);

  // Run the parser now.
  parser();
  fprintf(stderr, "Parsing Finished\n");

  //********************* Start printing final IR **************************
  // Print out all of the generated code into a file called output.ll
  auto Filename = "output.ll";
  std::error_code EC;
  raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

  if (EC) {
    errs() << "Could not open file: " << EC.message();
    return 1;
  }
  // TheModule->print(errs(), nullptr); // print IR to terminal
  TheModule->print(dest, nullptr);
  //********************* End printing final IR ****************************

  fclose(pFile); // close the file that contains the code that was parsed
  return 0;
}
