/*******************************************************************\

 Module: Unit tests for union_find_replacet in
   solvers/refinement/string_refinement.cpp

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <solvers/refinement/string_refinement.h>

SCENARIO("union_find_replacea",
  "[core][solvers][refinement][string_refinement]")
{
  union_find_replacet dict;
  pointer_typet char_pointer_type(unsignedbv_typet(16));
  const symbol_exprt a("a", char_pointer_type);
  const symbol_exprt b("b", char_pointer_type);
  const symbol_exprt c("c", char_pointer_type);
  const symbol_exprt d("d", char_pointer_type);
  const symbol_exprt e("e", char_pointer_type);
  const symbol_exprt f("f", char_pointer_type);
  dict.add_symbol(a, b);
  dict.add_symbol(a, c);
  dict.add_symbol(d, b);
  dict.add_symbol(e, f);
  REQUIRE(dict.find_expr(d)==dict.find_expr(c));
  REQUIRE(dict.find_expr(e)!=dict.find_expr(a));
  plus_exprt a_plus_e(a, e);
  plus_exprt c_plus_f(c, f);
  plus_exprt c_plus_d(c, d);
  dict.replace_expr(a_plus_e);
  dict.replace_expr(c_plus_f);
  dict.replace_expr(c_plus_d);
  REQUIRE(a_plus_e==c_plus_f);
  REQUIRE(a_plus_e!=c_plus_d);
  // Checks that introducing cycles does not caus infinite loops or exceptions:
  dict.add_symbol(c, d);
}
