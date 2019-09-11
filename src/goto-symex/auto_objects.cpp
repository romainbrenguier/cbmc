/*******************************************************************\

Module: Symbolic Execution of ANSI-C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution of ANSI-C

#include "goto_symex.h"
#include "expr_skeleton.h"
#include "symex_assign.h"

#include <util/prefix.h>
#include <util/cprover_prefix.h>
#include <util/symbol_table.h>
#include <util/std_expr.h>

exprt make_auto_object(
  const typet &type, goto_symex_statet &state, unsigned dynamic_counter)
{
  // produce auto-object symbol
  symbolt symbol;

  symbol.base_name="auto_object"+std::to_string(dynamic_counter);
  symbol.name="symex::"+id2string(symbol.base_name);
  symbol.is_lvalue=true;
  symbol.type=type;
  symbol.mode=ID_C;

  state.symbol_table.add(symbol);

  return symbol_exprt(symbol.name, symbol.type);
}

void initialize_auto_object(
  const exprt &expr,
  goto_symex_statet &state,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target,
  unsigned &dynamic_counter)
{
  const typet &type = ns.follow(expr.type());

  if(type.id()==ID_struct)
  {
    const struct_typet &struct_type=to_struct_type(type);

    for(const auto &comp : struct_type.components())
    {
      member_exprt member_expr(expr, comp.get_name(), comp.type());

      initialize_auto_object(
        member_expr, state, ns, symex_config, target, dynamic_counter);
    }
  }
  else if(type.id()==ID_pointer)
  {
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype = pointer_type.subtype();

    // we don't like function pointers and
    // we don't like void *
    if(subtype.id()!=ID_code &&
       subtype.id()!=ID_empty)
    {
      // could be NULL nondeterministically

      address_of_exprt address_of_expr(
        make_auto_object(pointer_type.subtype(), state, ++dynamic_counter),
        pointer_type);

      if_exprt rhs(
        side_effect_expr_nondett(bool_typet(), expr.source_location()),
        null_pointer_exprt(pointer_type),
        address_of_expr);

      code_assignt assignment(expr, rhs);

      exprt::operandst lhs_if_then_else_conditions;
      symex_assignt{
        state, symex_targett::assignment_typet::STATE, ns, symex_config, target}
        .assign_rec(expr, expr_skeletont{}, rhs, lhs_if_then_else_conditions);
    }
  }
}

void trigger_auto_object(
  const exprt &expr,
  goto_symex_statet &state,
  const namespacet &ns,
  const symex_configt &symex_config,
  symex_targett &target,
  unsigned &dynamic_counter)
{
  expr.visit_pre([&](const exprt &e) {
    if(e.id() == ID_symbol && e.get_bool(ID_C_SSA_symbol))
    {
      const ssa_exprt &ssa_expr = to_ssa_expr(e);
      const irep_idt &obj_identifier = ssa_expr.get_object_name();

      if(obj_identifier != goto_symex_statet::guard_identifier())
      {
        const symbolt &symbol = ns.lookup(obj_identifier);

        if(has_prefix(id2string(symbol.base_name), "auto_object"))
        {
          // done already?
          if(!state.get_level2().current_names.has_key(
               ssa_expr.get_identifier()))
          {
            initialize_auto_object(
              e, state, ns, symex_config, target, dynamic_counter);
          }
        }
      }
    }
  });
}
