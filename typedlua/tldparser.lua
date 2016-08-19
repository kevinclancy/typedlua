--[[
This module implements the parser for Typed Lua description files.
]]

local tldparser = {}

local lpeg = require "lpeg"
lpeg.locale(lpeg)

local tlast = require "typedlua.tlast"
local tllexer = require "typedlua.tllexer"
local tlst = require "typedlua.tlst"
local tltype = require "typedlua.tltype"

local G = lpeg.P { "TypedLuaDescription";
  TypedLuaDescription = tllexer.Skip * lpeg.V("DescriptionList") * -1 +
                        tllexer.report_error();
  -- type language
  Type = lpeg.V("NilableType");
  NilableType = lpeg.Cp() * lpeg.V("UnionType") * (tllexer.symb("?") * lpeg.Cc(true))^-1 /
                tltype.PUnionNil;
  UnionType = lpeg.Cp() * lpeg.V("PrimaryType") * 
              (lpeg.Cg(tllexer.symb("|") * lpeg.V("PrimaryType"))^0) /
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
  MethodType = lpeg.Cp() * lpeg.Cc({}) * lpeg.V("InputType") * tllexer.symb("=>") * 
               lpeg.V("NilableTuple") * lpeg.Cc(true) / 
               tltype.PFunction;
  InputType = lpeg.Cp() * tllexer.symb("(") * (lpeg.V("TupleType") + lpeg.Cc(nil)) * 
              tllexer.symb(")") * lpeg.Carg(2) /
              tltype.PinputTuple;
  NilableTuple = lpeg.Cp() * lpeg.V("UnionlistType") * (tllexer.symb("?") * lpeg.Carg(2))^-1 /
                 tltype.PUnionlistNil;
  UnionlistType = lpeg.Cp() * lpeg.V("OutputType") * (lpeg.Cg(tllexer.symb("|") * 
                  lpeg.V("OutputType"))^0) / tltype.PUnionlist;
  OutputType = lpeg.Cp() * tllexer.symb("(") * (lpeg.V("TupleType") + 
               lpeg.Cc(nil)) * tllexer.symb(")") * lpeg.Carg(2) / tltype.PoutputTuple;
  TupleType = lpeg.Cp() * lpeg.Ct(lpeg.V("Type") * (tllexer.symb(",") * lpeg.V("Type"))^0) *
              (tllexer.symb("*") * lpeg.Cc(true))^-1 /
              tltype.PTuple;
  TableType = lpeg.Cp() * tllexer.symb("{") * 
              lpeg.V("TableTypeBody") * tllexer.symb(",")^-1 * tllexer.symb("}") /
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
  HashType = lpeg.Cc(false) * lpeg.V("KeyType") * 
             tllexer.symb(":") * lpeg.V("FieldType") / tltype.Field;
  ArrayType = lpeg.Carg(3) * lpeg.V("FieldType") / tltype.ArrayField;
  KeyType = lpeg.V("BaseType") + lpeg.V("ValueType") + lpeg.V("AnyType");
  FieldType = lpeg.Cp() * lpeg.V("Type") * lpeg.Cc(tltype.Nil()) / tltype.PUnion;
  VariableType = lpeg.Cp() * tllexer.token(tllexer.Name, "Type") / tltype.PSymbol;
  RetType = lpeg.V("NilableTuple") +
            (lpeg.Cp() * lpeg.V("Type") * lpeg.Carg(2) / tltype.PretType);
            
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
                  
                  
  Id = lpeg.Cp() * tllexer.token(tllexer.Name, "Name") / tlast.ident;
  TypeDecId = (tllexer.kw("const") * lpeg.V("Id") / tlast.setConst) +
              lpeg.V("Id");
  IdList = lpeg.Cp() * lpeg.V("TypeDecId") * (tllexer.symb(",") * lpeg.V("TypeDecId"))^0 /
           tlast.namelist;
  IdDec = lpeg.V("IdList") * tllexer.symb(":") *
          (lpeg.V("Type") + lpeg.V("MethodType")) / tltype.fieldlist;
  IdDecList = (lpeg.V("IdDec")^1 + lpeg.Cc(nil)) / tltype.Table;
  TypeDec = tllexer.token(tllexer.Name, "Name") * lpeg.V("IdDecList") * tllexer.kw("end");
  StructuralTypedef = lpeg.Cp() * tllexer.kw("typedef") * lpeg.V("TypeDec") /
                      tlast.statInterface +
                      lpeg.Cp() * tllexer.kw("typedef") *
                      tllexer.token(tllexer.Name, "Name") * tllexer.symb("=") * lpeg.V("Type") /
                      tlast.statInterface;
                      
  InterfaceDefStat = lpeg.Cp() * tllexer.kw("interface") * lpeg.V("Id") *
                     (lpeg.V("TypeParams") + lpeg.Cc({})) *
                     lpeg.Ct(lpeg.V("InterfaceElement")^0) *
                     tllexer.kw("end") / tlast.statInterface;
                     
  ShapeDefStat = lpeg.Cp() * tllexer.kw("shape") * lpeg.V("Id") *
                 (lpeg.V("TypeParams") + lpeg.Cc({})) *
                 lpeg.Ct(lpeg.V("InterfaceElement")^0) *
                 tllexer.kw("end") / tlast.statShape;
                 
  InterfaceElement = lpeg.Cp() * tllexer.kw("method") * lpeg.V("Id") * 
                     (lpeg.V("InvTypeParams") + lpeg.Cc({})) * tllexer.symb(":") * 
                     lpeg.V("MethodType") / tlast.classElementAbstractMethod;      
                     
  TypeBundle = lpeg.Ct(lpeg.V("TypeDefinition") * 
               (tllexer.kw("and") * lpeg.V("TypeDefinition"))^0) / tlast.statTypeBundle;
                       
  TypeDefinition = lpeg.V("StructuralTypedef") + lpeg.V("InterfaceDefStat") + lpeg.V("ShapeDefStat");
  
  -- parser
  Userdata = lpeg.Cp() * tllexer.kw("userdata") * lpeg.V("TypeDec") /
             tlast.statUserdata;
  DescriptionList = lpeg.V("DescriptionItem")^1 / function (...) return {...} end;
  DescriptionItem = lpeg.V("TypedId") + lpeg.V("TypeBundle") + lpeg.V("Userdata");
  TypedId = lpeg.Cp() * tllexer.token(tllexer.Name, "Name") *
            tllexer.symb(":") * lpeg.V("Type") / tlast.ident;
}

local function traverse (ast, errorinfo, strict)
  assert(type(ast) == "table")
  assert(type(errorinfo) == "table")
  assert(type(strict) == "boolean")
  local t = tltype.Table()
  for k, v in ipairs(ast) do
    local tag = v.tag
    if tag == "Id" then
      table.insert(t, tltype.Field(v.const, tltype.Literal(v[1]), v[2]))
    elseif tag == "Typedef" then
      local name, t = v[1], v[2]
      local status, msg = tltype.checkTypeDec(name, t)
      if not status then
        return nil, tllexer.syntaxerror(errorinfo.subject, v.pos, errorinfo.filename, msg)
      end
      if tltype.checkRecursive(t, name) then
        v[2] = tltype.Recursive(name, t)
      end
    elseif tag == "Userdata" then
      local name, t = v[1], v[2]
      local status, msg = tltype.checkTypeDec(name, t)
      if not status then
        return nil, tllexer.syntaxerror(errorinfo.subject, v.pos, errorinfo.filename, msg)
      end
      if tltype.checkRecursive(t, name) then
        local msg = string.format("userdata '%s' is recursive", name)
        return nil, tllexer.syntaxerror(errorinfo.subject, v.pos, errorinfo.filename, msg)
      end
    else
      error("trying to traverse a description item, but got a " .. tag)
    end
  end
  local status, msg = tltype.checkTypeDec("nil", t)
  if not status then
    return nil, tllexer.syntaxerror(errorinfo.subject, 1, errorinfo.filename, msg)
  else
    return ast
  end
end

function tldparser.parse (filename, strict, integer)
  local file = assert(io.open(filename, "r"))
  local subject = file:read("*a")
  file:close()
  local errorinfo = { subject = subject, filename = filename }
  lpeg.setmaxstack(1000)
  if integer and _VERSION ~= "Lua 5.3" then integer = false end
  local ast, error_msg = lpeg.match(G, subject, nil, errorinfo, strict, integer)
  if not ast then return ast, error_msg end
  return traverse(ast, errorinfo, strict)
end

return tldparser
