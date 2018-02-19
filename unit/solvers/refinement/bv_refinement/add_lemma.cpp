/*******************************************************************\

 Module: Unit tests for bv refinement

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>

#include <util/arith_tools.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/sat/satcheck.h>
#include <util/symbol_table.h>
#include <java_bytecode/java_types.h>
#include <util/config.h>

SCENARIO("Add lemma to bv_refinementt",
  "[!mayfail][!throws][core][solvers][refinement][bv_refinement]")
{
  // Without this line, the program aborts with:
  // `Reason: pointer must have non-zero width`
  config.set_arch("none");

  GIVEN("A solver")
  {
    satcheck_no_simplifiert sat_check;
    symbol_tablet symbol_table;
    namespacet ns(symbol_table);
    bv_refinementt::infot info;
    info.ns = &ns;
    info.prop = &sat_check;
    info.refine_arithmetic = true;
    info.refine_arrays = true;
    info.max_node_refinement = 5;
    info.ui = ui_message_handlert::uit::PLAIN;
    bv_refinementt solver(info);

    WHEN("We give two contradictory inputs")
    {
      // Arrange
      const symbol_exprt s1("symbol_var1", java_int_type());
      const exprt constant_int = from_integer(99, java_int_type());
      const binary_relation_exprt lemma1(s1, ID_ge, constant_int);
      const not_exprt lemma2(lemma1);

      // Act
      solver << lemma1;
      solver << lemma2;

      // Assert
      THEN("it should be unsatisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_UNSATISFIABLE);
      }
    }

    WHEN("We give an array access")
    {
      // Arrange
      const symbol_exprt s1("symbol_var1", java_int_type());
      const symbol_exprt s2("symbol_var2", array_typet(java_char_type(), s1));
      const exprt constant_int = from_integer(99, java_int_type());
      const exprt constant_char = from_integer('A', java_char_type());
      const index_exprt index_expr(s2, plus_exprt(s1, from_integer(3, java_int_type())));
      const equal_exprt lemma1(index_expr, constant_char);

      // Act
      solver << lemma1;

      // Assert
      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }

    WHEN("We give a conjuction of constraints on arrays")
    {
      // Arrange
      const symbol_exprt length("length1", java_int_type());
      const symbol_exprt array("array1", array_typet(java_char_type(), length));
      const symbol_exprt var("var1", java_int_type());

      exprt::operandst ops;

      // array[1+var] == 'Z'
      ops.push_back(equal_exprt(
          index_exprt(array, plus_exprt(from_integer(1, java_int_type()), var)),
          from_integer('Z', java_char_type())));

      // array[2+var] == 'A'
      ops.push_back(equal_exprt(
          index_exprt(array, plus_exprt(from_integer(2, java_int_type()), var)),
          from_integer('A', java_char_type())));

      // array[3+var] == 'A'
      ops.push_back(equal_exprt(
          index_exprt(array, plus_exprt(from_integer(3, java_int_type()), var)),
          from_integer('A', java_char_type())));

      // array[4+var] == 'C'
      ops.push_back(equal_exprt(
          index_exprt( array,plus_exprt(from_integer(4, java_int_type()), var)),
          from_integer('C', java_char_type())));

      // array[var] = 'C'
      ops.push_back(equal_exprt(
          index_exprt(array, var), from_integer('C', java_char_type())));

      // var <= 83
      ops.push_back(binary_relation_exprt(
          var, ID_ge, from_integer(83, java_int_type())));

      // var >= 87
      ops.push_back(not_exprt(binary_relation_exprt(
          var, ID_ge, from_integer(87, java_int_type()))));

      const exprt lemma1 = conjunction(ops);

      // Act
      solver << lemma1;

      // Assert
      THEN("it should be satisfiable")
      {
        const auto result = solver();
        REQUIRE(result == decision_proceduret::resultt::D_SATISFIABLE);
      }
    }
  }
}
