/*******************************************************************\

 Module: Unit tests for regular expressions to constraint in
   solvers/refinement/regular_expressions.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <solvers/refinement/regular_expression.h>
#include <java_bytecode/java_types.h>
#include <util/symbol_table.h>
#include <iostream>
#include <java_bytecode/java_bytecode_language.h>
#include <langapi/mode.h>

SCENARIO("regexp", "[core][solvers][refinement][regular_expression]")
{
  const flat_patternt regex("a[b-c]*[vx-z]+");
  std::vector<exprt> axioms = regex.generate_constraints(
    symbol_exprt("match", java_int_type()),
    refined_string_exprt(
      symbol_exprt("length", java_int_type()),
      symbol_exprt("data",
                   array_typet(java_char_type(), infinity_exprt(java_int_type())))),
    "i"
  );

  register_language(new_java_bytecode_language);
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  std::cout << "size : " << axioms.size() << std::endl;
  for(auto ax : axioms)
  {
    if(ax.id()==ID_string_constraint)
      std:: cout << from_expr(ns, "", to_string_constraint(ax)) << std::endl;
    else
      std:: cout << from_expr(ns, "", ax) << std::endl;
  }
}