--[[
This module implements Typed Lua parser

CArgs: 
1 - erroinfo table
2 - strictness boolean flag
3 - integer boolean flag (should be true for my purposes)

]]

local tlparser = {}

local lpeg = require "lpeg"
lpeg.locale(lpeg)

local tlast = require "typedlua.tlast"
local tllexer = require "typedlua.tllexer"
local tlst = require "typedlua.tlst"
local tltype = require "typedlua.tltype"

local function chainl1 (pat, sep)
  return lpeg.Cf(pat * lpeg.Cg(sep * pat)^0, tlast.exprBinaryOp)
end

local G = lpeg.P { "TypedLua";
  TypedLua = tllexer.Shebang^-1 * tllexer.Skip * lpeg.V("Chunk") * -1 +
             tllexer.report_error();
  -- type language
  Type = lpeg.V("NilableType");
  NilableType = lpeg.Cp() * lpeg.V("UnionType") * (tllexer.symb("?") * lpeg.Cc(true))^-1 /
                tltype.PUnionNil;
  UnionType = lpeg.Cp() * lpeg.V("PrimaryType") * (lpeg.Cg(tllexer.symb("|") * lpeg.V("PrimaryType"))^0) /
              tltype.PUnion;
  PrimaryType = lpeg.V("LiteralType") +
                lpeg.V("BaseType") +
                lpeg.V("NilType") +
                lpeg.V("ValueType") +
                lpeg.V("AnyType") +
                lpeg.V("SelfType") +
                lpeg.V("FunctionType") +
                lpeg.V("TableType") +
                lpeg.V("VariableType");
               
  LiteralType = lpeg.Cp() * 
                ((tllexer.token("false", "Type") * lpeg.Cc(false)) +
                (tllexer.token("true", "Type") * lpeg.Cc(true)) +
                tllexer.token(tllexer.Number, "Type") +
                tllexer.token(tllexer.String, "Type")) /
                tltype.PLiteral;
  BaseType = lpeg.Cp() * tllexer.token("boolean", "Type") / tltype.PBoolean +
             lpeg.Cp() * tllexer.token("number", "Type") / tltype.PNumber +
             lpeg.Cp() * tllexer.token("string", "Type") / tltype.PString +
             lpeg.Cp() * tllexer.token("integer", "Type") * lpeg.Carg(3) / tltype.PInteger;
  NilType = lpeg.Cp() * tllexer.token("nil", "Type") / tltype.PNil;
  ValueType = lpeg.Cp() * tllexer.token("value", "Type") / tltype.PValue;
  AnyType = lpeg.Cp() * tllexer.token("any", "Type") / tltype.PAny;
  SelfType = lpeg.Cp() * tllexer.token("self", "Type") / tltype.PSelf;
  FunctionType = lpeg.Cp() * (lpeg.V("InvTypeParams") + lpeg.Cc({})) * lpeg.V("InputType") * tllexer.symb("->") * lpeg.V("NilableTuple") /
                 tltype.PFunction;
  MethodType = lpeg.Cp() * lpeg.Cc({}) * lpeg.V("InputType") * tllexer.symb("=>") * lpeg.V("NilableTuple") *
               lpeg.Cc(true) / tltype.PFunction;
  InputType = lpeg.Cp() * tllexer.symb("(") * (lpeg.V("TupleType") + lpeg.Cc(nil)) * tllexer.symb(")") *
              lpeg.Carg(2) /
              tltype.PinputTuple;
  NilableTuple = lpeg.Cp() * lpeg.V("UnionlistType") * (tllexer.symb("?") * lpeg.Carg(2))^-1 /
                 tltype.PUnionlistNil;
  UnionlistType = lpeg.Cp() * lpeg.V("OutputType") * (lpeg.Cg(tllexer.symb("|") * lpeg.V("OutputType"))^0) /
                  tltype.PUnionlist;
  OutputType = lpeg.Cp() * tllexer.symb("(") * (lpeg.V("TupleType") + lpeg.Cc(nil)) * tllexer.symb(")") *
               lpeg.Carg(2) /
               tltype.PoutputTuple;
  TupleType = lpeg.Cp() * lpeg.Ct(lpeg.V("Type") * (tllexer.symb(",") * lpeg.V("Type"))^0) *
              (tllexer.symb("*") * lpeg.Cc(true))^-1 /
              tltype.PTuple;
  TableType = lpeg.Cp() * tllexer.symb("{") * lpeg.V("TableTypeBody") * tllexer.symb("}") /
              tltype.PTable;
  TableTypeBody = lpeg.V("RecordType") +
                  lpeg.V("HashType") +
                  lpeg.V("ArrayType") +
                  lpeg.Cc(nil);
  RecordType = lpeg.V("RecordField") * (tllexer.symb(",") * lpeg.V("RecordField"))^0 *
               (tllexer.symb(",") * (lpeg.V("HashType") + lpeg.V("ArrayType")))^-1;
  RecordField = ((tllexer.kw("const") * lpeg.Cc(true)) + lpeg.Cc(false)) *
                lpeg.V("LiteralType") * tllexer.symb(":") * lpeg.V("Type") /
                tltype.Field;
  HashType = lpeg.Cc(false) * lpeg.V("KeyType") * tllexer.symb(":") * lpeg.V("FieldType") /
             tltype.Field;
  ArrayType = lpeg.Carg(3) * lpeg.V("FieldType") / tltype.ArrayField;
  KeyType = lpeg.V("BaseType") + lpeg.V("ValueType") + lpeg.V("AnyType");
  FieldType = lpeg.Cp() * lpeg.V("Type") * lpeg.Cc(tltype.Nil()) / tltype.PUnion;
  TypeArgs = lpeg.Ct(tllexer.symb('<') * lpeg.V("Type") * (tllexer.symb(",") * lpeg.V("Type"))^0 * 
                     tllexer.symb('>'));
  TypeId = lpeg.Cp() * tllexer.token(tllexer.TypeName, "TypeId") / tlast.typeIdent;
  VariableType = lpeg.Cp() * tllexer.token(tllexer.TypeName, "Type") * 
                 (lpeg.V("TypeArgs") + lpeg.Cc({})) / tltype.PSymbol;
  RetType = lpeg.V("NilableTuple") +
            (lpeg.Cp() * lpeg.V("Type") * lpeg.Carg(2) / tltype.PretType);
  Id = lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.ident;
  TypeDecId = (tllexer.kw("const") * lpeg.V("Id") / tlast.setConst) +
              lpeg.V("Id");
  IdList = lpeg.Cp() * lpeg.V("TypeDecId") * (tllexer.symb(",") * lpeg.V("TypeDecId"))^0 /
           tlast.namelist;
  IdDec = lpeg.V("IdList") * tllexer.symb(":") *
          (lpeg.V("Type") + lpeg.V("MethodType")) / tltype.fieldlist;
  IdDecList = (lpeg.V("IdDec")^1 + lpeg.Cc(nil)) / tltype.Table;
  TypeDec = tllexer.token(tllexer.Name, "Name") * lpeg.V("IdDecList") * tllexer.kw("end");
  
  ClassValueLookup = lpeg.Cp() * tllexer.kw("class") * 
                     tllexer.symb('(') * lpeg.V("TypeId") * tllexer.symb(')') / tlast.classValueLookup; 
  
  ClassConcreteFieldDef = lpeg.Cp() *
                          (tllexer.kw("const") * lpeg.Cc(true) + lpeg.Cc(false)) * 
                          lpeg.V("Id") * tllexer.symb(":") * 
                          lpeg.V("Type") / tlast.classElementConcreteField;
  
  ClassAbstractFieldDef = lpeg.Cp() * tllexer.kw("abstract") * tllexer.kw("field") *
                          lpeg.V("Id") * tllexer.symb(":") * lpeg.V("Type") /
                          tlast.classElementAbstractField;
                          
  ClassConstructor = lpeg.Cp() * tllexer.kw("constructor") * lpeg.V("Id") *
                     tllexer.symb("(") * 
                     lpeg.V("ParList") * tllexer.symb(")") * 
                     (tllexer.kw("super") * tllexer.symb(".") * lpeg.V("Id") * 
                      tllexer.symb("(") * lpeg.V("ExpList") * tllexer.symb(")") +
                      lpeg.Cc("NoSuperCall") * lpeg.Cc("NoSuperCall")) *
                     lpeg.V("Block") * tllexer.kw("end") / tlast.classElementConstructor;
  
  ClassFinalizer = lpeg.Cp() * tllexer.kw("finalizer") *
                   lpeg.V("Block") * tllexer.kw("end") / tlast.classElementFinalizer;
  
  ClassAbstractMethodDef = lpeg.Cp() * tllexer.kw("abstract") * tllexer.kw("method") *
                        lpeg.V("Id") * tllexer.symb(":") *
                        (lpeg.V("InvTypeParams") + lpeg.Cc({})) * 
                        lpeg.V("MethodType") / tlast.classElementAbstractMethod;
  
  InterfaceElement = lpeg.Cp() * tllexer.kw("method") * lpeg.V("Id") * tllexer.symb(":") * 
                     (lpeg.V("InvTypeParams") + lpeg.Cc({})) * lpeg.V("MethodType") 
                     / tlast.classElementAbstractMethod;
  
  ClassConcreteMethodDef =  lpeg.Cp() * tllexer.kw("method") *
                         lpeg.V("Id") * (lpeg.V("InvTypeParams") + lpeg.Cc({})) * 
                         tllexer.symb("(") * lpeg.V("ParList") * tllexer.symb(")") *
                         tllexer.symb(":") * lpeg.V("RetType") * 
                         lpeg.V("Block") * tllexer.kw("end") / 
                         tlast.classElementConcreteMethod;
  
  ClassElement = lpeg.V("ClassConcreteFieldDef") + lpeg.V("ClassAbstractFieldDef") + 
                 lpeg.V("ClassConstructor") + lpeg.V("ClassFinalizer") + 
                 lpeg.V("ClassAbstractMethodDef") + lpeg.V("ClassConcreteMethodDef");
    
  TypeVariance = (tllexer.symb("+") * lpeg.Cc("Covariant")) +
                 (tllexer.symb("-") * lpeg.Cc("Contravariant")) +
                 lpeg.Cc("Invariant");
    
  TypeParam = lpeg.Cp() * lpeg.V("TypeVariance") * tllexer.token(tllexer.Name, "Name") * 
              (tllexer.symb("<:") * lpeg.V("Type"))^-1 / tlast.tpar;  
  
  InvTypeParam = lpeg.Cp() * lpeg.Cc("Invariant") * tllexer.token(tllexer.Name, "Name") *
                 (tllexer.symb("<:") * lpeg.V("Type"))^-1 / tlast.tpar;
  
  TypeParams = tllexer.symb("<") * 
               lpeg.Ct( lpeg.V("TypeParam") * (tllexer.symb(",") * lpeg.V("TypeParam"))^0 ) * 
               tllexer.symb(">");
                  
  InvTypeParams = tllexer.symb("<") * 
                  lpeg.Ct( lpeg.V("InvTypeParam") * (tllexer.symb(",") * lpeg.V("InvTypeParam"))^0 ) * 
                  tllexer.symb(">");
  
  TypeDefinition = lpeg.V("ClassDefStat") + lpeg.V("StructuralTypedef") + lpeg.V("InterfaceDefStat") +
                   lpeg.V("ShapeDefStat");
  
  TypeBundle = lpeg.Ct(lpeg.V("TypeDefinition") * 
                         (tllexer.kw("and") * lpeg.V("TypeDefinition"))^0) / tlast.statTypeBundle;
              
  ClassDefStat = lpeg.Cp() * 
                 (tllexer.kw("abstract") * lpeg.Cc(true) + lpeg.Cc(false)) * 
                 tllexer.kw("class") * lpeg.V("Id") * (lpeg.V("TypeParams") + lpeg.Cc({})) * 
                 (tllexer.kw("extends") * 
                  lpeg.V("Type") + 
                  lpeg.Cc("NoParent")) *
                  lpeg.Ct(
                    (tllexer.kw("implements") * 
                     lpeg.V("Type") * (tllexer.symb(",") * lpeg.V("Type"))^0)^-1
                  ) *
                 lpeg.Ct(lpeg.V("ClassElement")^0) * tllexer.kw("end") / tlast.statClass;
  
  StructuralTypedef = lpeg.Cp() * tllexer.kw("typedef") * lpeg.V("TypeDec") /
                      tlast.statTypedef +
                      lpeg.Cp() * tllexer.kw("typedef") * 
                      lpeg.V("Id") * tllexer.symb("=") * lpeg.V("Type") /
                      tlast.statTypedef;
  
  InterfaceDefStat = lpeg.Cp() * tllexer.kw("interface") * lpeg.V("Id") *
                     (lpeg.V("TypeParams") + lpeg.Cc({})) *
                     lpeg.Ct(lpeg.V("InterfaceElement")^0) *
                     tllexer.kw("end") / tlast.statInterface;
                     
  ShapeDefStat = lpeg.Cp() * tllexer.kw("shape") * lpeg.V("Id") *
                 (lpeg.V("TypeParams") + lpeg.Cc({})) *
                 lpeg.Ct(lpeg.V("InterfaceElement")^0) *
                 tllexer.kw("end") / tlast.statShape;
                     
  ImplementsStat = lpeg.Cp() * lpeg.V("Type") * 
                   tllexer.kw("implements") * lpeg.V("Type") / tlast.statImplements;
  
  -- parser
  Chunk = lpeg.V("Block");
  StatList = (tllexer.symb(";") + lpeg.V("Stat"))^0;
  Var = lpeg.V("Id");
  TypedId = lpeg.Cp() * tllexer.token(tllexer.Name, "Name") * (tllexer.symb(":") *
            lpeg.V("Type"))^-1 / tlast.ident;
  FunctionDef = tllexer.kw("function") * lpeg.V("FuncBody");
  FieldSep = tllexer.symb(",") + tllexer.symb(";");
  Field = lpeg.Cp() *
          ((tllexer.symb("[") * lpeg.V("Expr") * tllexer.symb("]")) +
          (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.exprString)) *
          tllexer.symb("=") * lpeg.V("Expr") / tlast.fieldPair +
          lpeg.V("Expr");
  TField = (tllexer.kw("const") * lpeg.V("Field") / tlast.setConst) +
           lpeg.V("Field");
  FieldList = (lpeg.V("TField") * (lpeg.V("FieldSep") * lpeg.V("TField"))^0 *
              lpeg.V("FieldSep")^-1)^-1;
  Constructor = lpeg.Cp() * tllexer.symb("{") * lpeg.V("FieldList") * tllexer.symb("}") / tlast.exprTable;
  NameList = lpeg.Cp() * lpeg.V("TypedId") * (tllexer.symb(",") * lpeg.V("TypedId"))^0 /
             tlast.namelist;
  ExpList = lpeg.Cp() * lpeg.V("Expr") * (tllexer.symb(",") * lpeg.V("Expr"))^0 /
            tlast.explist;
  FuncArgs = tllexer.symb("(") *
             (lpeg.V("Expr") * (tllexer.symb(",") * lpeg.V("Expr"))^0)^-1 *
             tllexer.symb(")") +
             lpeg.V("Constructor") +
             lpeg.Cp() * tllexer.token(tllexer.String, "String") / tlast.exprString;
  OrOp = tllexer.kw("or") / "or";
  AndOp = tllexer.kw("and") / "and";
  RelOp = tllexer.symb("~=") / "ne" +
          tllexer.symb("==") / "eq" +
          tllexer.symb("<=") / "le" +
          tllexer.symb(">=") / "ge" +
          tllexer.symb("<") / "lt" +
          tllexer.symb(">") / "gt";
  BOrOp = tllexer.symb("|") / "bor";
  BXorOp = tllexer.symb("~") / "bxor";
  BAndOp = tllexer.symb("&") / "band";
  ShiftOp = tllexer.symb("<<") / "shl" +
            tllexer.symb(">>") / "shr";
  ConOp = tllexer.symb("..") / "concat";
  AddOp = tllexer.symb("+") / "add" +
          tllexer.symb("-") / "sub";
  MulOp = tllexer.symb("*") / "mul" +
          tllexer.symb("//") / "idiv" +
          tllexer.symb("/") / "div" +
          tllexer.symb("%") / "mod";
  UnOp = tllexer.kw("not") / "not" +
         tllexer.symb("-") / "unm" +
         tllexer.symb("~") / "bnot" +
         tllexer.symb("#") / "len";
  PowOp = tllexer.symb("^") / "pow";
  Expr = lpeg.V("SubExpr_1");
  SubExpr_1 = chainl1(lpeg.V("SubExpr_2"), lpeg.V("OrOp"));
  SubExpr_2 = chainl1(lpeg.V("SubExpr_3"), lpeg.V("AndOp"));
  SubExpr_3 = chainl1(lpeg.V("SubExpr_4"), lpeg.V("RelOp"));
  SubExpr_4 = chainl1(lpeg.V("SubExpr_5"), lpeg.V("BOrOp"));
  SubExpr_5 = chainl1(lpeg.V("SubExpr_6"), lpeg.V("BXorOp"));
  SubExpr_6 = chainl1(lpeg.V("SubExpr_7"), lpeg.V("BAndOp"));
  SubExpr_7 = chainl1(lpeg.V("SubExpr_8"), lpeg.V("ShiftOp"));
  SubExpr_8 = lpeg.V("SubExpr_9") * lpeg.V("ConOp") * lpeg.V("SubExpr_8") /
              tlast.exprBinaryOp +
              lpeg.V("SubExpr_9");
  SubExpr_9 = chainl1(lpeg.V("SubExpr_10"), lpeg.V("AddOp"));
  SubExpr_10 = chainl1(lpeg.V("SubExpr_11"), lpeg.V("MulOp"));
  SubExpr_11 = lpeg.V("UnOp") * lpeg.V("SubExpr_11") / tlast.exprUnaryOp +
               lpeg.V("SubExpr_12");
  SubExpr_12 = lpeg.V("SimpleExp") * (lpeg.V("PowOp") * lpeg.V("SubExpr_11"))^-1 /
               tlast.exprBinaryOp;
  SimpleExp = lpeg.Cp() * tllexer.token(tllexer.Number, "Number") / tlast.exprNumber +
              lpeg.Cp() * tllexer.token(tllexer.String, "String") / tlast.exprString +
              lpeg.Cp() * tllexer.kw("nil") / tlast.exprNil +
              lpeg.Cp() * tllexer.kw("false") / tlast.exprFalse +
              lpeg.Cp() * tllexer.kw("true") / tlast.exprTrue +
              lpeg.Cp() * tllexer.symb("...") / tlast.exprDots +
              lpeg.V("FunctionDef") +
              lpeg.V("Constructor") +
              lpeg.V("SuffixedExp") +
              lpeg.V("SuperInvoke");
  SuffixedExp = lpeg.Cf(lpeg.V("PrimaryExp") * (
                (lpeg.Cp() * tllexer.symb(".") *
                  (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.exprString)) /
                  tlast.exprIndex +
                (lpeg.Cp() * tllexer.symb("[") * lpeg.V("Expr") * tllexer.symb("]")) /
                tlast.exprIndex +
                (lpeg.Cp() * lpeg.Cg(tllexer.symb(":") *
                   (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.exprString) *
                   lpeg.V("FuncArgs"))) / tlast.invoke +
                (lpeg.Cp() * (lpeg.V("TypeArgs") + lpeg.Cc({})) * 
                              lpeg.V("FuncArgs")) / tlast.call)^0, tlast.exprSuffixed);
  PrimaryExp = lpeg.V("Var") +
               lpeg.V("ClassValueLookup") +
               lpeg.Cp() * tllexer.symb("(") * lpeg.V("Expr") * tllexer.symb(")") / tlast.exprParen;
  SuperInvoke = lpeg.Cp() * tllexer.kw("super") * tllexer.symb(":") * 
                (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.exprString) * 
                lpeg.V("FuncArgs") / tlast.superinvoke;
  Block = lpeg.Cp() * lpeg.V("StatList") * lpeg.V("RetStat")^-1 / tlast.block;
  IfStat = lpeg.Cp() * tllexer.kw("if") * lpeg.V("Expr") * tllexer.kw("then") * lpeg.V("Block") *
           (tllexer.kw("elseif") * lpeg.V("Expr") * tllexer.kw("then") * lpeg.V("Block"))^0 *
           (tllexer.kw("else") * lpeg.V("Block"))^-1 *
           tllexer.kw("end") / tlast.statIf;
  WhileStat = lpeg.Cp() * tllexer.kw("while") * lpeg.V("Expr") *
              tllexer.kw("do") * lpeg.V("Block") * tllexer.kw("end") / tlast.statWhile;
  DoStat = tllexer.kw("do") * lpeg.V("Block") * tllexer.kw("end") / tlast.statDo;
  ForBody = tllexer.kw("do") * lpeg.V("Block");
  ForNum = lpeg.Cp() *
           lpeg.V("Id") * tllexer.symb("=") * lpeg.V("Expr") * tllexer.symb(",") *
           lpeg.V("Expr") * (tllexer.symb(",") * lpeg.V("Expr"))^-1 *
           lpeg.V("ForBody") / tlast.statFornum;
  ForGen = lpeg.Cp() * lpeg.V("NameList") * tllexer.kw("in") *
           lpeg.V("ExpList") * lpeg.V("ForBody") / tlast.statForin;
  ForStat = tllexer.kw("for") * (lpeg.V("ForNum") + lpeg.V("ForGen")) * tllexer.kw("end");
  RepeatStat = lpeg.Cp() * tllexer.kw("repeat") * lpeg.V("Block") *
               tllexer.kw("until") * lpeg.V("Expr") / tlast.statRepeat;
  FuncName = lpeg.Cf(lpeg.V("Id") * (tllexer.symb(".") *
             (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.exprString))^0, tlast.funcName) *
             (tllexer.symb(":") * (lpeg.Cp() * tllexer.token(tllexer.Name, "Name") /
             tlast.exprString) *
               lpeg.Cc(true))^-1 /
             tlast.funcName;
  ParList = lpeg.Cp() * lpeg.V("NameList") * (tllexer.symb(",") * lpeg.V("TypedVarArg"))^-1 /
            tlast.parList2 +
            lpeg.Cp() * lpeg.V("TypedVarArg") / tlast.parList1 +
            lpeg.Cp() / tlast.parList0;
  TypedVarArg = lpeg.Cp() * tllexer.symb("...") * (tllexer.symb(":") * lpeg.V("Type"))^-1 /
                tlast.identDots;
  FuncBody = lpeg.Cp() * (lpeg.V("InvTypeParams") + lpeg.Cc({})) * tllexer.symb("(") * lpeg.V("ParList") * tllexer.symb(")") *
             (tllexer.symb(":") * lpeg.V("RetType") + lpeg.Cc(false)) *
             lpeg.V("Block") * tllexer.kw("end") / tlast.exprFunction;
  FuncStat = lpeg.Cp() * (tllexer.kw("const") * lpeg.Cc(true) + lpeg.Cc(false)) *
             tllexer.kw("function") * lpeg.V("FuncName") * lpeg.V("FuncBody") /
             tlast.statFuncSet;
  LocalFunc = lpeg.Cp() * tllexer.kw("function") *
              lpeg.V("Id") * lpeg.V("FuncBody") / tlast.statLocalrec;
  LocalAssign = lpeg.Cp() * lpeg.V("NameList") *
                ((tllexer.symb("=") * lpeg.V("ExpList")) + lpeg.Ct(lpeg.Cc())) / tlast.statLocal;
  LocalStat = tllexer.kw("local") *
              (lpeg.V("LocalFunc") + lpeg.V("LocalAssign"));
  LabelStat = lpeg.Cp() * tllexer.symb("::") * tllexer.token(tllexer.Name, "Name") * tllexer.symb("::") / tlast.statLabel;
  BreakStat = lpeg.Cp() * tllexer.kw("break") / tlast.statBreak;
  GoToStat = lpeg.Cp() * tllexer.kw("goto") * tllexer.token(tllexer.Name, "Name") / tlast.statGoto;
  RetStat = lpeg.Cp() * tllexer.kw("return") *
            (lpeg.V("Expr") * (tllexer.symb(",") * lpeg.V("Expr"))^0)^-1 *
            tllexer.symb(";")^-1 / tlast.statReturn;
  LVar = (tllexer.kw("const") * lpeg.V("SuffixedExp") / tlast.setConst) +
         lpeg.V("SuffixedExp");
  ExprStat = lpeg.Cmt(
             (lpeg.V("LVar") * (lpeg.Cc(tlast.statSet) * lpeg.V("Assignment"))) +
             (lpeg.V("SuffixedExp") * (lpeg.Cc(tlast.statApply))),
             function (s, i, s1, f, ...) return f(s1, ...) end);
  Assignment = ((tllexer.symb(",") * lpeg.V("LVar"))^1)^-1 * tllexer.symb("=") * lpeg.V("ExpList");
  Stat = lpeg.V("IfStat") + lpeg.V("WhileStat") + lpeg.V("DoStat") + lpeg.V("ForStat") +
         lpeg.V("RepeatStat") + lpeg.V("FuncStat") + lpeg.V("LocalStat") +
         lpeg.V("LabelStat") + lpeg.V("BreakStat") + lpeg.V("GoToStat") +
         lpeg.V("TypeBundle") + lpeg.V("ImplementsStat") + lpeg.V("ExprStat");
}

local traverse_stm, traverse_exp, traverse_var
local traverse_block, traverse_explist, traverse_varlist, traverse_parlist

function traverse_parlist (env, parlist)
  local len = #parlist
  if len > 0 and parlist[len].tag == "Dots" then
    local t = parlist[len][1] or tltype.Any(parlist.pos)
    tlst.set_vararg(env, t)
    len = len - 1
  end
  for i = 1, len do
    tlst.set_local(env, parlist[i])
  end
  return true
end

local function traverse_function (env, exp)
  tlst.begin_function(env)
  tlst.begin_scope(env)
  local status, msg = traverse_parlist(env, exp[1])
  if not status then return status, msg end
  status, msg = traverse_block(env, exp[3])
  if not status then return status, msg end
  tlst.end_scope(env)
  tlst.end_function(env)
  return true
end

local function traverse_op (env, exp)
  local status, msg = traverse_exp(env, exp[2])
  if not status then return status, msg end
  if exp[3] then
    status, msg = traverse_exp(env, exp[3])
    if not status then return status, msg end
  end
  return true
end

local function traverse_paren (env, exp)
  local status, msg = traverse_exp(env, exp[1])
  if not status then return status, msg end
  return true
end

local function traverse_table (env, fieldlist)
  for k, v in ipairs(fieldlist) do
    local tag = v.tag
    if tag == "Pair" or tag == "Const" then
      local status, msg = traverse_exp(env, v[1])
      if not status then return status, msg end
      status, msg = traverse_exp(env, v[2])
      if not status then return status, msg end
    else
      local status, msg = traverse_exp(env, v)
      if not status then return status, msg end
    end
  end
  return true
end

local function traverse_vararg (env, exp)
  if not tlst.is_vararg(env) then
    local msg = "cannot use '...' outside a vararg function"
    return nil, tllexer.syntaxerror(env.subject, exp.pos, env.filename, msg)
  end
  return true
end

local function traverse_call (env, call)
  local status, msg = traverse_exp(env, call[1])
  if not status then return status, msg end
  for i=3, #call do
    status, msg = traverse_exp(env, call[i])
    if not status then return status, msg end
  end
  return true
end

local function traverse_invoke (env, invoke)
  local status, msg = traverse_exp(env, invoke[1])
  if not status then return status, msg end
  for i=3, #invoke do
    status, msg = traverse_exp(env, invoke[i])
    if not status then return status, msg end
  end
  return true
end

local function traverse_superinvoke(env, superinvoke)
  local status, msg = traverse_exp(env, superinvoke[1])
  if not status then return status, msg end
  for i=2, #superinvoke do
    status, msg = traverse_exp(env, superinvoke[i])
    if not status then return status, msg end
  end
  return true  
end

local function traverse_assignment (env, stm)
  local status, msg = traverse_varlist(env, stm[1])
  if not status then return status, msg end
  status, msg = traverse_explist(env, stm[2])
  if not status then return status, msg end
  return true
end

local function traverse_const_assignment (env, stm)
  local status, msg = traverse_var(env, stm[1])
  if not status then return status, msg end
  status, msg = traverse_exp(env, stm[2])
  if not status then return status, msg end
  return true
end

local function traverse_break (env, stm)
  if not tlst.insideloop(env) then
    local msg = "<break> not inside a loop"
    return nil, tllexer.syntaxerror(env.subject, stm.pos, env.filename, msg)
  end
  return true
end

local function traverse_forin (env, stm)
  local status, msg = traverse_explist(env, stm[2])
  if not status then return status, msg end
  tlst.begin_loop(env)
  tlst.begin_scope(env)
  for _, v in ipairs(stm[1]) do
    tlst.set_local(env, v)
  end
  status, msg = traverse_block(env, stm[3])
  if not status then return status, msg end
  tlst.end_scope(env)
  tlst.end_loop(env)
  return true
end

local function traverse_fornum (env, stm)
  local status, msg
  status, msg = traverse_exp(env, stm[2])
  if not status then return status, msg end
  status, msg = traverse_exp(env, stm[3])
  if not status then return status, msg end
  local block
  if stm[5] then
    status, msg = traverse_exp(env, stm[4])
    if not status then return status, msg end
    block = stm[5]
  else
    block = stm[4]
  end
  tlst.begin_loop(env)
  tlst.begin_scope(env)
  tlst.set_local(env, stm[1])
  status, msg = traverse_block(env, block)
  if not status then return status, msg end
  tlst.end_scope(env)
  tlst.end_loop(env)
  return true
end

local function traverse_goto (env, stm)
  tlst.set_pending_goto(env, stm)
  return true
end

local function traverse_if (env, stm)
  local len = #stm
  if len % 2 == 0 then
    for i=1, len, 2 do
      local status, msg = traverse_exp(env, stm[i])
      if not status then return status, msg end
      status, msg = traverse_block(env, stm[i+1])
      if not status then return status, msg end
    end
  else
    for i=1, len-1, 2 do
      local status, msg = traverse_exp(env, stm[i])
      if not status then return status, msg end
      status, msg = traverse_block(env, stm[i+1])
      if not status then return status, msg end
    end
    local status, msg = traverse_block(env, stm[len])
    if not status then return status, msg end
  end
  return true
end

local function traverse_label (env, stm)
  if not tlst.set_label(env, stm[1]) then
    local msg = string.format("label '%s' already defined", stm[1])
    return nil, tllexer.syntaxerror(env.subject, stm.pos, env.filename, msg)
  else
    return true
  end
end

local function traverse_local (env, stm)
  local status, msg = traverse_explist(env, stm[2])
  if not status then return status, msg end
  for k, v in ipairs(stm[1]) do
    tlst.set_local(env, v)
  end
  return true
end

local function traverse_localrec (env, stm)
  tlst.set_local(env, stm[1][1])
  local status, msg = traverse_exp(env, stm[2][1])
  if not status then return status, msg end
  return true
end

local function traverse_repeat (env, stm)
  tlst.begin_loop(env)
  local status, msg = traverse_block(env, stm[1])
  if not status then return status, msg end
  status, msg = traverse_exp(env, stm[2])
  if not status then return status, msg end
  tlst.end_loop(env)
  return true
end

local function traverse_return (env, stm)
  local status, msg = traverse_explist(env, stm)
  if not status then return status, msg end
  return true
end

local function traverse_while (env, stm)
  tlst.begin_loop(env)
  local status, msg = traverse_exp(env, stm[1])
  if not status then return status, msg end
  status, msg = traverse_block(env, stm[2])
  if not status then return status, msg end
  tlst.end_loop(env)
  return true
end

function traverse_var (env, var)
  local tag = var.tag
  if tag == "Id" then
    if not tlst.get_local(env, var[1]) then
      local e1 = tlast.ident(var.pos, "_ENV")
      local e2 = tlast.exprString(var.pos, var[1])
      var.tag = "Index"
      var[1] = e1
      var[2] = e2
    end
    return true
  elseif tag == "Index" then
    local status, msg = traverse_exp(env, var[1])
    if not status then return status, msg end
    status, msg = traverse_exp(env, var[2])
    if not status then return status, msg end
    return true
  else
    error("trying to traverse a variable, but got a " .. tag)
  end
end

function traverse_varlist (env, varlist)
  for k, v in ipairs(varlist) do
    local status, msg = traverse_var(env, v)
    if not status then return status, msg end
  end
  return true
end

function traverse_exp (env, exp)
  local tag = exp.tag
  if tag == "Nil" or
     tag == "True" or
     tag == "False" or
     tag == "Number" or
     tag == "String" or
     tag == "ClassValueLookup" then
    return true
  elseif tag == "Dots" then
    return traverse_vararg(env, exp)
  elseif tag == "Function" then
    return traverse_function(env, exp)
  elseif tag == "Table" then
    return traverse_table(env, exp)
  elseif tag == "Op" then
    return traverse_op(env, exp)
  elseif tag == "Paren" then
    return traverse_paren(env, exp)
  elseif tag == "Call" then
    return traverse_call(env, exp)
  elseif tag == "Invoke" then
    return traverse_invoke(env, exp)
  elseif tag == "SuperInvoke" then
    return traverse_superinvoke(env, exp)
  elseif tag == "Id" or
         tag == "Index" then
    return traverse_var(env, exp)
  else
    error("trying to traverse an expression, but got a " .. tag)
  end
end

function traverse_explist (env, explist)
  for k, v in ipairs(explist) do
    local status, msg = traverse_exp(env, v)
    if not status then return status, msg end
  end
  return true
end

local function traverse_concrete_class_method (env, method)
  tlst.begin_function(env)
  tlst.begin_scope(env)
  local status,msg = traverse_parlist(env,method[2])
  if not status then return status, msg end
  tlst.set_local(env,{ tag = "Id", "self"})
  status, msg = traverse_block(env,method[4])
  if not status then return status, msg end
  tlst.end_scope(env)
  tlst.end_function(env)
    
  return true
end

local function traverse_constructor (env, constructor)
  tlst.begin_function(env)
  tlst.begin_scope(env)
  local status,msg = traverse_parlist(env,constructor[2])
  if not status then return status, msg end
  if constructor[4] ~= "NoSuperCall" then
    status, msg = traverse_explist(env,constructor[4])
  end
  if not status then return status,msg end
  tlst.set_local(env,{ tag = "Id", "self" })
  status, msg = traverse_block(env,constructor[5])
  if not status then return status,msg end
  tlst.end_scope(env)
  tlst.end_function(env)
    
  return true
end

local function traverse_class (env, def)
  --iterate through methods, descending into constructors, 
  --finalizers, and concrete methods with 'self' added to environment
  for _,v in ipairs(def[3]) do
    if v.tag == "ConcreteClassField" or 
       v.tag == "AbstractClassField" or 
       v.tag == "AbstractClassMethod" then
      --nothing to do here
    elseif v.tag == "ConcreteClassMethod" then
      local status, msg = traverse_concrete_class_method(env,v)
      if not status then return status,msg end
    elseif v.tag == "ClassConstructor" then
      local status, msg = traverse_constructor(env,v)
      if not status then return status,msg end      
    end
  end
  
  return true 
end

local function traverse_interface (env, def)
  return true
end

local function traverse_typedef (env, def)
  return true
end

local function traverse_implements (env, def)
  return true
end

local function traverse_typedefs (env, stat)
  for _,def in ipairs(stat[1]) do
    tlst.set_local(env, def[1])
  end
  
  for _,def in ipairs(stat[1]) do
    local tag = def.tag
    if tag == "Typedef" then
      return traverse_typedef(env,def)
    elseif tag == "Class" then
      return traverse_class(env,def)
    elseif tag == "Interface" then
      return traverse_interface(env, def)
    else
      assert(false)
    end
  end
end

function traverse_stm (env, stm)
  local tag = stm.tag
  if tag == "Do" then
    return traverse_block(env, stm)
  elseif tag == "Set" then
    return traverse_assignment(env, stm)
  elseif tag == "ConstSet" then
    return traverse_const_assignment(env, stm)
  elseif tag == "While" then
    return traverse_while(env, stm)
  elseif tag == "Repeat" then
    return traverse_repeat(env, stm)
  elseif tag == "If" then
    return traverse_if(env, stm)
  elseif tag == "Fornum" then
    return traverse_fornum(env, stm)
  elseif tag == "Forin" then
    return traverse_forin(env, stm)
  elseif tag == "Local" then
    return traverse_local(env, stm)
  elseif tag == "Localrec" then
    return traverse_localrec(env, stm)
  elseif tag == "Goto" then
    return traverse_goto(env, stm)
  elseif tag == "Label" then
    return traverse_label(env, stm)
  elseif tag == "Return" then
    return traverse_return(env, stm)
  elseif tag == "Break" then
    return traverse_break(env, stm)
  elseif tag == "Call" then
    return traverse_call(env, stm)
  elseif tag == "Invoke" then
    return traverse_invoke(env, stm)
  elseif tag == "TypeBundle" then
    return traverse_typedefs(env, stm)
  elseif tag == "Implements" then
    return traverse_implements(env, stm)
  else
    error("trying to traverse a statement, but got a " .. tag)
  end
end

function traverse_block (env, block)
  local l = {}
  tlst.begin_scope(env)
  for k, v in ipairs(block) do
    local status, msg = traverse_stm(env, v)
    if not status then return status, msg end
  end
  tlst.end_scope(env)
  return true
end

local function verify_pending_gotos (env)
  for s = tlst.get_maxscope(env), 1, -1 do
    for k, v in ipairs(tlst.get_pending_gotos(env, s)) do
      local l = v[1]
      if not tlst.exist_label(env, s, l) then
        local msg = string.format("no visible label '%s' for <goto>", l)
        return nil, tllexer.syntaxerror(env.subject, v.pos, env.filename, msg)
      end
    end
  end
  return true
end

local function traverse (ast, errorinfo, strict)
  assert(type(ast) == "table")
  assert(type(errorinfo) == "table")
  assert(type(strict) == "boolean")
  local env = tlst.new_env(errorinfo.subject, errorinfo.filename, strict)
  local _env = tlast.ident(0, "_ENV")
  tlst.begin_function(env)
  tlst.set_vararg(env, tltype.String(nil))
  tlst.begin_scope(env)
  tlst.set_local(env, _env)
  for k, v in ipairs(ast) do
    local status, msg = traverse_stm(env, v)
    if not status then return status, msg end
  end
  tlst.end_scope(env)
  tlst.end_function(env)
  status, msg = verify_pending_gotos(env)
  if not status then return status, msg end
  return ast
end

local function lineno (s, i)
  if i == 1 then return 1, 1 end
  local rest, num = s:sub(1,i):gsub("[^\n]*\n", "")
  local r = #rest
  return 1 + num, r ~= 0 and r or 1
end

local function fixup_lin_col(subject, node)
  if node.pos then
    node.l, node.c = lineno(subject, node.pos)
  end
  for _, child in ipairs(node) do
    if type(child) == "table" then
      fixup_lin_col(subject, child)
    end
  end
end

function tlparser.parse (subject, filename, strict, integer)
  local errorinfo = { subject = subject, filename = filename }
  lpeg.setmaxstack(1000)
  if integer and _VERSION ~= "Lua 5.3" then integer = false end
  local ast, error_msg = lpeg.match(G, subject, nil, errorinfo, strict, integer)
  if not ast then return ast, error_msg end
  fixup_lin_col(subject, ast)
  return traverse(ast, errorinfo, strict)
end

return tlparser
