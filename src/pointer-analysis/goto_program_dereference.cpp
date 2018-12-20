/*******************************************************************\

Module: Dereferencing Operations on GOTO Programs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Dereferencing Operations on GOTO Programs

#include "goto_program_dereference.h"

#include <util/expr_util.h>
#include <util/simplify_expr.h>
#include <util/base_type.h>
#include <util/std_code.h>
#include <util/symbol_table.h>
#include <util/guard.h>
#include <util/options.h>

/// \param expr: expression to check
/// \param[out] symbol: symbol which gets assigned the value from the
///   `failed_symbol` comment
/// \return true when `expr` is a symbol, whose type contains a `failed_symbol`
///   comment which exists in the namespace.
bool goto_program_dereferencet::has_failed_symbol(
  const exprt &expr,
  const symbolt *&symbol,
  guard_managert &guard_manager)
{
  if(expr.id()==ID_symbol)
  {
    if(expr.get_bool(ID_C_invalid_object))
      return false;

    const symbolt &ptr_symbol = ns.lookup(to_symbol_expr(expr));

    const irep_idt &failed_symbol = ptr_symbol.type.get(ID_C_failed_symbol);

    if(failed_symbol.empty())
      return false;

    return !ns.lookup(failed_symbol, symbol);
  }

  return false;
}

/// \deprecated
bool goto_program_dereferencet::is_valid_object(
  const irep_idt &identifier)
{
  const symbolt &symbol=ns.lookup(identifier);

  if(symbol.type.id()==ID_code)
    return true;

  if(symbol.is_static_lifetime)
    return true; // global/static

  #if 0
  return valid_local_variables->find(symbol.name)!=
     valid_local_variables->end(); // valid local
  #else
  return true;
  #endif
}

/// Turn subexpression of `expr` of the form `&*p` or `reference_to(*p)` to p
/// and use `dereference` on subexpressions of the form `*p`
/// \param expr: expression in which to remove dereferences
/// \param guard: boolean expression assumed to hold when dereferencing
/// \param mode: unused
void goto_program_dereferencet::dereference_rec(
  exprt &expr,
  guardt &guard,
  const value_set_dereferencet::modet mode,
  guard_managert &guard_manager)
{
  if(!has_subexpr(expr, ID_dereference))
    return;

  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(!expr.is_boolean())
      throw expr.id_string()+" must be Boolean, but got "+
            expr.pretty();

    guardt old_guard = guard;

    for(auto &op : expr.operands())
    {
      if(!op.is_boolean())
        throw expr.id_string()+" takes Boolean operands only, but got "+
              op.pretty();

      if(has_subexpr(op, ID_dereference))
        dereference_rec(
          op,
          guard,
          value_set_dereferencet::modet::READ,
          guard_manager);

      if(expr.id()==ID_or)
        guard.add(boolean_negate(op));
      else
        guard.add(op);
    }

    guard = old_guard;
    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three arguments";

    if(!expr.op0().is_boolean())
    {
      std::string msg=
        "first argument of if must be boolean, but got "
        +expr.op0().pretty();
      throw msg;
    }

    dereference_rec(
      expr.op0(),
      guard,
      value_set_dereferencet::modet::READ,
      guard_manager);

    bool o1 = has_subexpr(expr.op1(), ID_dereference);
    bool o2 = has_subexpr(expr.op2(), ID_dereference);

    if(o1)
    {
      guardt old_guard=guard;
      guard.add(expr.op0());
      dereference_rec(expr.op1(), guard, mode, guard_manager);
      guard=old_guard;
    }

    if(o2)
    {
      guardt old_guard=guard;
      guard.add(boolean_negate(expr.op0()));
      dereference_rec(expr.op2(), guard, mode, guard_manager);
      guard=old_guard;
    }

    return;
  }

  if(expr.id()==ID_address_of ||
     expr.id()=="reference_to")
  {
    // turn &*p to p
    // this has *no* side effect!

    assert(expr.operands().size()==1);

    if(expr.op0().id()==ID_dereference)
    {
      assert(expr.op0().operands().size()==1);

      exprt tmp;
      tmp.swap(expr.op0().op0());

      if(tmp.type()!=expr.type())
        tmp.make_typecast(expr.type());

      expr.swap(tmp);
    }
  }

  Forall_operands(it, expr)dereference_rec(*it, guard, mode, guard_manager);

  if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw "dereference expects one operand";

    dereference_location=expr.find_source_location();

    exprt tmp= dereference.dereference(expr.op0(), guard, mode, guard_manager);

    expr.swap(tmp);
  }
  else if(expr.id()==ID_index)
  {
    // this is old stuff and will go away

    if(expr.operands().size()!=2)
      throw "index expects two operands";

    if(expr.op0().type().id()==ID_pointer)
    {
      dereference_location=expr.find_source_location();

      exprt tmp1(ID_plus, expr.op0().type());
      tmp1.operands().swap(expr.operands());

      exprt tmp2= dereference.dereference(tmp1, guard, mode, guard_manager);
      tmp2.swap(expr);
    }
  }
}

/// Gets the value set corresponding to the current target and
/// expression `expr`.
/// \param expr: an expression
/// \param[out] dest: gets the value set
void goto_program_dereferencet::get_value_set(
  const exprt &expr,
  value_setst::valuest &dest)
{
  value_sets.get_values(current_target, expr, dest);
}

/// Remove dereference expressions contained in `expr`.
/// \param expr: an expression
/// \param checks_only: when true, execute the substitution on a copy of expr
///   so that `expr` stays unchanged. In that case the only observable effect
///   is whether an exception would be thrown.
/// \param mode: unused
void goto_program_dereferencet::dereference_expr(
  exprt &expr,
  const bool checks_only,
  const value_set_dereferencet::modet mode,
  guard_managert &guard_manager)
{
  guardt guard(guard_manager);

  if(checks_only)
  {
    exprt tmp(expr);
    dereference_rec(tmp, guard, mode, guard_manager);
  }
  else
    dereference_rec(expr, guard, mode, guard_manager);
}

void goto_program_dereferencet::dereference_program(
  goto_programt &goto_program,
  bool checks_only,
  guard_managert &manager)
{
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    assertions.clear();
    dereference_instruction(it, checks_only, manager);
  }
}

void goto_program_dereferencet::dereference_program(
  goto_functionst &goto_functions,
  bool checks_only,
  guard_managert &manager)
{
  for(goto_functionst::function_mapt::iterator
      it=goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    dereference_program(it->second.body, checks_only, manager);
}

/// Remove dereference from expressions contained in the instruction at
/// `target`. If `check_only` is true, the dereferencing is performed on copies
/// of the expressions, in that case the only observable effect is whether an
/// exception would be thrown.
void goto_program_dereferencet::dereference_instruction(
  goto_programt::targett target,
  bool checks_only,
  guard_managert &manager)
{
  current_target=target;
  #if 0
  valid_local_variables=&target->local_variables;
  #endif
  goto_programt::instructiont &i=*target;

  // TODO have a version of derefence_expr for guards
  exprt i_guard = i.guard.as_expr();
  dereference_expr(i_guard, checks_only, value_set_dereferencet::modet::READ, manager);
  i.guard.from_expr(i_guard);

  if(i.is_assign())
  {
    if(i.code.operands().size()!=2)
      throw "assignment expects two operands";

    dereference_expr(
      i.code.op0(), checks_only, value_set_dereferencet::modet::WRITE, manager);
    dereference_expr(
      i.code.op1(), checks_only, value_set_dereferencet::modet::READ, manager);
  }
  else if(i.is_function_call())
  {
    code_function_callt &function_call = to_code_function_call(i.code);

    if(function_call.lhs().is_not_nil())
      dereference_expr(
        function_call.lhs(),
        checks_only,
        value_set_dereferencet::modet::WRITE, manager);

    dereference_expr(
      function_call.function(),
      checks_only,
      value_set_dereferencet::modet::READ, manager);
    dereference_expr(
      function_call.op2(), checks_only, value_set_dereferencet::modet::READ, manager);
  }
  else if(i.is_return())
  {
    Forall_operands(it, i.code)
      dereference_expr(*it, checks_only, value_set_dereferencet::modet::READ, manager);
  }
  else if(i.is_other())
  {
    const irep_idt &statement=i.code.get(ID_statement);

    if(statement==ID_expression)
    {
      if(i.code.operands().size()!=1)
        throw "expression expects one operand";

      dereference_expr(
        i.code.op0(), checks_only, value_set_dereferencet::modet::READ, manager);
    }
    else if(statement==ID_printf)
    {
      Forall_operands(it, i.code)
        dereference_expr(
          *it, checks_only, value_set_dereferencet::modet::READ, manager);
    }
  }
}

/// Set the current target to `target` and remove derefence from expr.
void goto_program_dereferencet::dereference_expression(
  goto_programt::const_targett target,
  exprt &expr,
  guard_managert &manager)
{
  current_target=target;
  #if 0
  valid_local_variables=&target->local_variables;
  #endif

  dereference_expr(expr, false, value_set_dereferencet::modet::READ, manager);
}

/// Throw an exception in case removing dereferences from the program would
/// throw an exception.
void goto_program_dereferencet::pointer_checks(
  goto_programt &goto_program,
  guard_managert &manager)
{
  dereference_program(goto_program, true, manager);
}

/// Throw an exception in case removing dereferences from the program would
/// throw an exception.
void goto_program_dereferencet::pointer_checks(
  goto_functionst &goto_functions,
  guard_managert &manager)
{
  dereference_program(goto_functions, true, manager);
}

/// \deprecated
void remove_pointers(
  goto_programt &goto_program,
  symbol_tablet &symbol_table,
  value_setst &value_sets,
  guard_managert &manager)
{
  namespacet ns(symbol_table);

  optionst options;

  goto_program_dereferencet
    goto_program_dereference(ns, symbol_table, options, value_sets);

  goto_program_dereference.dereference_program(
    goto_program,
    false,
    manager);
}

/// Remove dereferences in all expressions contained in the program
/// `goto_model`. `value_sets` is used to determine to what objects the pointers
/// may be pointing to.
void remove_pointers(
  goto_modelt &goto_model,
  value_setst &value_sets,
  guard_managert &manager)
{
  namespacet ns(goto_model.symbol_table);

  optionst options;

  goto_program_dereferencet
    goto_program_dereference(
      ns, goto_model.symbol_table, options, value_sets);

  Forall_goto_functions(it, goto_model.goto_functions)
    goto_program_dereference.dereference_program(
      it->second.body,
      false,
      manager);
}

/// \deprecated
void pointer_checks(
  goto_programt &goto_program,
  symbol_tablet &symbol_table,
  const optionst &options,
  value_setst &value_sets,
  guard_managert &manager)
{
  namespacet ns(symbol_table);
  goto_program_dereferencet
    goto_program_dereference(ns, symbol_table, options, value_sets);
  goto_program_dereference.pointer_checks(goto_program, manager);
}

/// \deprecated
void pointer_checks(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table,
  const optionst &options,
  value_setst &value_sets,
  guard_managert &manager)
{
  namespacet ns(symbol_table);
  goto_program_dereferencet
    goto_program_dereference(ns, symbol_table, options, value_sets);
  goto_program_dereference.pointer_checks(goto_functions, manager);
}

/// Remove dereferences in `expr` using `value_sets` to determine to what
/// objects the pointers may be pointing to.
void dereference(
  goto_programt::const_targett target,
  exprt &expr,
  const namespacet &ns,
  value_setst &value_sets,
  guard_managert &manager)
{
  optionst options;
  symbol_tablet new_symbol_table;
  goto_program_dereferencet
    goto_program_dereference(ns, new_symbol_table, options, value_sets);
  goto_program_dereference.dereference_expression(target, expr, manager);
}
