/*******************************************************************\

 Module: Java string library preprocess.
         Test for converting an expression to a string expression.

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>
#include <util/expr.h>
#include <util/std_code.h>
#include <util/namespace.h>
#include <java_bytecode/java_object_factory.h>
#include <java_bytecode/java_bytecode_language.h>
#include <java_bytecode/java_root_class.h>
#include <langapi/language_util.h>
#include <langapi/mode.h>
#include <iostream>

TEST_CASE("Generate string object")
{
  source_locationt loc;
  symbol_tablet symbol_table;
  code_blockt code;
  register_language(new_java_bytecode_language);

  // Add java.lang.Object to symbol table
  symbolt jlo_sym;
  jlo_sym.name="java::java.lang.Object";
  jlo_sym.type=struct_typet();
  jlo_sym.is_type=true;
  java_root_class(jlo_sym);
  bool failed=symbol_table.add(jlo_sym);
  CHECK_RETURN(!failed);

  // Add java.lang.String to symbol table
  java_string_library_preprocesst preprocess;
  preprocess.add_string_type("java.lang.String", symbol_table);
  namespacet ns(symbol_table);

  // Declare a String named arg
  symbol_typet java_string_type("java::java.lang.String");
  symbol_exprt expr("arg", pointer_typet(java_string_type));
  // Generate initialisation code for arg in code
  gen_nondet_string_init(code, expr, loc, symbol_table);

  std::vector<std::string> code_string;
  for(auto op : code.operands())
    code_string.push_back(from_expr(ns, "", op));

  std::vector<std::string> reference_code=
  {
    "struct java.lang.String { struct @java.lang.Object; "
         "int length; char *data; } tmp_object_factory$1;",
    "arg = &tmp_object_factory$1;",
    "tmp_object_factory$1.@java.lang.Object.@class_identifier ="
      " \"java::java.lang.String\";",
    "tmp_object_factory$1.@java.lang.Object.@lock = false;",
    "tmp_object_factory$1.length = NONDET(int);",
    "char tmp_object_factory$2[tmp_object_factory$1.length];",
    "tmp_object_factory$1.data = tmp_object_factory$2;"
  };

  for(std::size_t i=0; i<code_string.size() && i<reference_code.size(); ++i)
    REQUIRE(code_string[i]==reference_code[i]);

  REQUIRE(code_string.size()==reference_code.size());
}
