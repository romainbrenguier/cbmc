/*******************************************************************\

Module: Java trace verification

Author: Jeannie Moulton

\*******************************************************************/

#include "goto_trace.h"
#include <iostream>
#include <util/expr.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <algorithm>
#include <util/format_expr.h>

static bool check_symbol_structure(const exprt &symbol_expr)
{
  if(!expr_try_dynamic_cast<symbol_exprt>(symbol_expr))
    return false;
  if(const auto symbol = expr_try_dynamic_cast<symbol_exprt>(symbol_expr))
  {
    if(symbol->get_identifier() == "")
      return false;
  }
  return true;
}

static optionalt<symbol_exprt> get_inner_symbolexpr(const exprt &expr)
{
  exprt symbol_operand = expr;
  while(symbol_operand.has_operands())
    symbol_operand = symbol_operand.op0();
  if(!check_symbol_structure(symbol_operand))
    return {};
  return *expr_try_dynamic_cast<symbol_exprt>(symbol_operand);
}

static bool check_member_structure(const exprt &member_expr)
{
  if(!expr_try_dynamic_cast<member_exprt>(member_expr))
    return false;
  if(!member_expr.has_operands())
    return false;
  const auto symbol_operand = get_inner_symbolexpr(member_expr);
  if(!symbol_operand)
    return false;
  return true;
}

static void print_error(const std::string &side, const exprt &expr)
{
  std::cerr << "Check trace assumption failure on " + side + " expression:\n"
            << format(expr) << '\n'
            << expr.pretty(0, 0)
            << std::endl;
  UNREACHABLE;
  throw std::runtime_error(
    "Check trace assumption failure on " + side + " expression:\n" +
    expr.pretty(0, 0));
}

static bool check_string_symbol(const exprt &expr)
{
  const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(expr);
  if(!symbol_expr)
    return false;
  if(
    id2string(symbol_expr->get_identifier()).find("java.lang.String.Literal") ==
      std::string::npos &&
    id2string(symbol_expr->get_identifier()).find("cprover_string") ==
      std::string::npos &&
    id2string(symbol_expr->get_identifier()).find("_array") ==
      std::string::npos &&
    !type_try_dynamic_cast<array_typet>(symbol_expr->type()))
  {
    return false;
  }
  return true;
}

static bool valid_lhs_expr_high_level(const exprt &lhs)
{
  return expr_try_dynamic_cast<member_exprt>(lhs) ||
         expr_try_dynamic_cast<symbol_exprt>(lhs) ||
         expr_try_dynamic_cast<index_exprt>(lhs);
}

static bool valid_rhs_expr_high_level(const exprt &rhs)
{
  return expr_try_dynamic_cast<struct_exprt>(rhs) ||
         expr_try_dynamic_cast<array_exprt>(rhs) ||
         expr_try_dynamic_cast<constant_exprt>(rhs) ||
         expr_try_dynamic_cast<address_of_exprt>(rhs) ||
         expr_try_dynamic_cast<symbol_exprt>(rhs);
}

bool valid_lvalue(const exprt &expr)
{
  const exprt lhs = skip_typecast(expr);
  if(!valid_lhs_expr_high_level(lhs))
    return false;
  // check member lhs structure
  if(const auto member = expr_try_dynamic_cast<member_exprt>(lhs))
  {
    if(!check_member_structure(*member))
      return false;
  }
  // check symbol lhs structure
  if(const auto symbol = expr_try_dynamic_cast<symbol_exprt>(lhs))
  {
    if(!check_symbol_structure(*symbol))
      return false;
  }
  // check index lhs structure
  if(const auto index = expr_try_dynamic_cast<index_exprt>(lhs))
  {
    if(index->operands().size() != 2)
      return false;
    if(!check_symbol_structure(index->op0()))
    {
      std::cerr << "Warning: unsupported LHS " << format(*index)
                << std::endl;
      return false;
    }
    if(!expr_try_dynamic_cast<constant_exprt>(index->op1()))
      return false;
  }
  return true;
}

void check_trace_assumptions(const goto_tracet &trace)
{
  for(const auto &step : trace.steps)
  {
    if(!step.is_assignment() && !step.is_decl())
      continue;
    const auto &lhs = skip_typecast(step.full_lhs);
    const auto &rhs = skip_typecast(step.full_lhs_value);
    if(!valid_lvalue(lhs))
      print_error("LHS", lhs);

    if(!valid_rhs_expr_high_level(rhs))
      print_error("RHS", rhs);
    // check address_of rhs structure (String only)
    if(const auto address = expr_try_dynamic_cast<address_of_exprt>(rhs))
    {
      const auto symbol_expr = get_inner_symbolexpr(*address);
      if(!symbol_expr)
        print_error("RHS", rhs);
      if(!check_string_symbol(*symbol_expr))
        print_error("RHS", rhs);
    }
    // check symbol rhs structure (String only)
    if(const auto symbol_expr = expr_try_dynamic_cast<symbol_exprt>(rhs))
    {
      if(!check_symbol_structure(*symbol_expr))
        print_error("RHS", rhs);
      if(!check_string_symbol(*symbol_expr))
        print_error("RHS", rhs);
    }
    // check struct rhs structure
    if(const auto struct_expr = expr_try_dynamic_cast<struct_exprt>(rhs))
    {
      if(!struct_expr->has_operands())
        print_error("RHS", *struct_expr);
      if(
        struct_expr->op0().id() != ID_struct &&
        struct_expr->op0().id() != ID_constant)
      {
        print_error("RHS", *struct_expr);
      }
      if(
        struct_expr->operands().size() > 1 &&
        std::any_of(
          ++struct_expr->operands().begin(),
          struct_expr->operands().end(),
          [&](const exprt &operand) { return operand.id() != ID_constant; }))
      {
        print_error("RHS", *struct_expr);
      }
    }
    // check array rhs structure
    if(const auto array_expr = expr_try_dynamic_cast<array_exprt>(rhs))
    {
      (void)array_expr;
      // seems no check is required.
    }
    // check constant rhs structure
    if(const auto constant_expr = expr_try_dynamic_cast<constant_exprt>(rhs))
    {
      if(constant_expr->has_operands())
      {
        const auto operand = skip_typecast(constant_expr->operands()[0]);
        if(
          operand.id() != ID_constant && operand.id() != ID_address_of &&
          operand.id() != ID_plus)
          print_error("RHS", *constant_expr);
      }
      else if(constant_expr->get_value().empty())
        print_error("RHS", *constant_expr);
    }
  }
  std::cout << "Trace verification successful" << std::endl;
}
