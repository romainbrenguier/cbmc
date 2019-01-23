/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex_state.h"

#include <cstdlib>
#include <iostream>

#include <util/base_exceptions.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>

static level1t<exprt> get_l1_name(exprt expr);

static void set_l2_indices(
  symex_level0t level0,
  symex_level1t level1,
  symex_level2t level2,
  ssa_exprt &ssa_expr,
  unsigned int thread_nr,
  const namespacet &ns);

goto_symex_statet::goto_symex_statet()
  : depth(0),
    symex_target(nullptr),
    atomic_section_id(0),
    total_vccs(0),
    remaining_vccs(0),
    record_events(true),
    dirty()
{
  threads.resize(1);
  new_frame();
}

goto_symex_statet::~goto_symex_statet()=default;

/// write to a variable
static bool check_renaming(const exprt &expr);

static bool check_renaming(const typet &type)
{
  if(type.id()==ID_array)
    return check_renaming(to_array_type(type).size());
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(check_renaming(c.type()))
        return true;
  }
  else if(type.has_subtype())
    return check_renaming(to_type_with_subtype(type).subtype());

  return false;
}

static bool check_renaming_l1(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(expr.id()==ID_symbol)
  {
    if(!expr.get_bool(ID_C_SSA_symbol))
      return expr.type().id()!=ID_code;
    if(!to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type()!=expr.type())
      return true;
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming_l1(*it))
        return true;
  }

  return false;
}

static bool check_renaming(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_symbol)
  {
    return check_renaming_l1(to_address_of_expr(expr).object());
  }
  else if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_index)
  {
    const auto index_expr = to_index_expr(to_address_of_expr(expr).object());
    return check_renaming_l1(index_expr.array()) ||
           check_renaming(index_expr.index());
  }
  else if(expr.id()==ID_symbol)
  {
    if(!expr.get_bool(ID_C_SSA_symbol))
      return expr.type().id()!=ID_code;
    if(to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type()!=expr.type())
      return true;
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming(*it))
        return true;
  }

  return false;
}

class goto_symex_is_constantt : public is_constantt
{
protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_mult)
    {
      // propagate stuff with sizeof in it
      forall_operands(it, expr)
      {
        if(it->find(ID_C_c_sizeof_type).is_not_nil())
          return true;
        else if(!is_constant(*it))
          return false;
      }

      return true;
    }
    else if(expr.id() == ID_with)
    {
      // this is bad
      /*
      forall_operands(it, expr)
      if(!is_constant(expr.op0()))
      return false;

      return true;
      */
      return false;
    }

    return is_constantt::is_constant(expr);
  }
};

void goto_symex_statet::assignment(
  ssa_exprt &lhs, // L0/L1
  const exprt &rhs,  // L2
  const namespacet &ns,
  bool rhs_is_simplified,
  bool record_value,
  bool allow_pointer_unsoundness)
{
  // identifier should be l0 or l1, make sure it's l1
  lhs = rename_level1_ssa(std::move(lhs), ns).expr;
  irep_idt l1_identifier=lhs.get_identifier();

  // the type might need renaming
  rename(lhs.type(), l1_identifier, ns);
  lhs.update_type();
  if(run_validation_checks)
  {
    DATA_INVARIANT(!check_renaming_l1(lhs), "lhs renaming failed on l1");
  }

#if 0
  PRECONDITION(l1_identifier != get_original_name(l1_identifier)
      || l1_identifier=="goto_symex::\\guard"
      || ns.lookup(l1_identifier).is_shared()
      || has_prefix(id2string(l1_identifier), "symex::invalid_object")
      || has_prefix(id2string(l1_identifier), "symex_dynamic::dynamic_object"));
#endif

  // do the l2 renaming
  const auto level2_it =
    level2.current_names.emplace(l1_identifier, std::make_pair(lhs, 0)).first;
  symex_renaming_levelt::increase_counter(level2_it);
  set_l2_indices(level0, level1, level2, lhs, source.thread_nr, ns);

  // in case we happen to be multi-threaded, record the memory access
  bool is_shared=l2_thread_write_encoding(lhs, ns);

  if(run_validation_checks)
  {
    DATA_INVARIANT(!check_renaming(lhs), "lhs renaming failed on l2");
    DATA_INVARIANT(!check_renaming(rhs), "rhs renaming failed on l2");
  }

  // see #305 on GitHub for a simple example and possible discussion
  if(is_shared && lhs.type().id() == ID_pointer && !allow_pointer_unsoundness)
    throw unsupported_operation_exceptiont(
      "pointer handling for concurrency is unsound");

  // for value propagation -- the RHS is L2

  if(!is_shared && record_value && goto_symex_is_constantt()(rhs))
    propagation[l1_identifier] = rhs;
  else
    propagation.erase(l1_identifier);

  {
    // update value sets
    level1t<exprt> l1_rhs = get_l1_name(rhs);
    level1t<ssa_exprt> l1_lhs = remove_level2(lhs);

    if(run_validation_checks)
    {
      DATA_INVARIANT(
        !check_renaming_l1(l1_lhs.expr), "lhs renaming failed on l1");
      DATA_INVARIANT(
        !check_renaming_l1(l1_rhs.expr), "rhs renaming failed on l1");
    }

    value_set.assign(
      l1_lhs.expr, l1_rhs.expr, ns, rhs_is_simplified, is_shared);
  }

  #if 0
  std::cout << "Assigning " << l1_identifier << '\n';
  value_set.output(ns, std::cout);
  std::cout << "**********************\n";
  #endif
}

static void set_l0_indices(
  symex_level0t level0,
  ssa_exprt &ssa_expr,
  unsigned int thread_nr,
  const namespacet &ns)
{
  level0(ssa_expr, ns, thread_nr);
}

static void set_l1_indices(
  symex_level0t level0,
  symex_level1t level1,
  ssa_exprt &ssa_expr,
  unsigned int thread_nr,
  const namespacet &ns)
{
  if(!ssa_expr.get_level_2().empty())
    return;
  if(!ssa_expr.get_level_1().empty())
    return;
  level0(ssa_expr, ns, thread_nr);
  level1(ssa_expr);
}

static void set_l2_indices(
  symex_level0t level0,
  symex_level1t level1,
  symex_level2t level2,
  ssa_exprt &ssa_expr,
  unsigned int thread_nr,
  const namespacet &ns)
{
  if(!ssa_expr.get_level_2().empty())
    return;
  level0(ssa_expr, ns, thread_nr);
  level1(ssa_expr);
  ssa_expr.set_level_2(level2.current_count(ssa_expr.get_identifier()));
}

/// Fixes the type of `with_exprt`s and `if_exprt`s according to their operands.
/// When the type of the operands of a `with_exprt` or `if_exprt` have been
/// renamed they could end up being different from that of the expression. We
/// fix that by propagating the type of its operands to \p expr.
static void fix_type(exprt &expr)
{
  if(expr.id() == ID_with)
    expr.type() = to_with_expr(expr).old().type();
  else if(expr.id() == ID_if)
  {
    DATA_INVARIANT(
      to_if_expr(expr).true_case().type() ==
        to_if_expr(expr).false_case().type(),
      "true case of to_if_expr should be of same type "
      "as false case");
    expr.type() = to_if_expr(expr).true_case().type();
  }
}

exprt goto_symex_statet::rename_level0(exprt expr, const namespacet &ns)
{
  // rename all the symbols with their last known value
  if(auto ssa = expr_try_dynamic_cast<ssa_exprt>(expr))
  {
    return rename_level0(*ssa, ns).expr;
  }
  else if(expr.id() == ID_symbol)
  {
    // we never rename function symbols
    if(expr.type().id() == ID_code)
    {
      rename(expr.type(), to_symbol_expr(expr).get_identifier(), ns, L0);

      return expr;
    }

    expr = ssa_exprt(expr);
    return rename_level0(expr, ns);
  }
  else if(auto address_of_expr = expr_try_dynamic_cast<address_of_exprt>(expr))
  {
    rename_address(address_of_expr->object(), ns, L0);
    to_pointer_type(expr.type()).subtype() = address_of_expr->object().type();
    return expr;
  }
  else
  {
    // this could go wrong, but we would have to re-typecheck ...
    rename(expr.type(), irep_idt(), ns, L0);

    // do this recursively
    for(auto &op : expr.operands())
      rename_level0(op, ns);

    fix_type(expr);
    return expr;
  }
}

level0t<ssa_exprt>
goto_symex_statet::rename_level0(const symbol_exprt &expr, const namespacet &ns)
{
  ssa_exprt ssa{expr};
  set_l0_indices(level0, ssa, source.thread_nr, ns);
  rename(ssa.type(), ssa.get_identifier(), ns, L0);
  ssa.update_type();
  return level0t<ssa_exprt>{ssa};
}

level1t<ssa_exprt> goto_symex_statet::rename_level1(
  level0t<ssa_exprt> l0_expr,
  const namespacet &ns)
{
  set_l1_indices(level0, level1, l0_expr.expr, source.thread_nr, ns);
  rename(l0_expr.expr.type(), l0_expr.expr.get_identifier(), ns, L1);
  l0_expr.expr.update_type();
  return level1t<ssa_exprt>{l0_expr.expr};
}

level1t<ssa_exprt>
goto_symex_statet::rename_level1_ssa(ssa_exprt ssa, const namespacet &ns)
{
  set_l1_indices(level0, level1, ssa, source.thread_nr, ns);
  rename(ssa.type(), ssa.get_identifier(), ns, L1);
  ssa.update_type();
  return level1t<ssa_exprt>{ssa};
}

level1t<exprt>
goto_symex_statet::rename_level1(exprt expr, const namespacet &ns)
{
  // rename all the symbols with their last known value
  if(auto ssa = expr_try_dynamic_cast<ssa_exprt>(expr))
  {
    expr = rename_level1_ssa(std::move(*ssa), ns).expr;
    return level1t<exprt>{expr};
  }
  else if(auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
  {
    // we never rename function symbols
    if(symbol->type().id() == ID_code)
    {
      rename(symbol->type(), symbol->get_identifier(), ns, L1);
      return level1t<exprt>{std::move(*symbol)};
    }

    return level1t<exprt>{rename_level1_ssa(ssa_exprt{*symbol}, ns).expr};
  }
  else if(auto address_of_expr = expr_try_dynamic_cast<address_of_exprt>(expr))
  {
    rename_address(address_of_expr->object(), ns, L1);
    to_pointer_type(expr.type()).subtype() = address_of_expr->object().type();
    return level1t<exprt>{expr};
  }
  else
  {
    // this could go wrong, but we would have to re-typecheck ...
    rename(expr.type(), irep_idt(), ns, L1);

    // do this recursively
    for(auto &op : expr.operands())
      op = rename_level1(std::move(op), ns).expr;

    fix_type(expr);
    return level1t<exprt>{expr};
  }
}

ssa_exprt
goto_symex_statet::rename_level2_ssa(ssa_exprt ssa, const namespacet &ns)
{
  set_l1_indices(level0, level1, ssa, source.thread_nr, ns);
  rename(ssa.type(), ssa.get_identifier(), ns);
  ssa.update_type();

  if(l2_thread_read_encoding(ssa, ns))
  {
    // renaming taken care of by l2_thread_encoding
  }
  else if(!ssa.get_level_2().empty())
  {
    // already at L2
  }
  else
  {
    // We also consider propagation if we go up to L2.
    // L1 identifiers are used for propagation!
    auto p_it = propagation.find(ssa.get_identifier());

    if(p_it != propagation.end())
      ssa = to_ssa_expr(p_it->second); // already L2
    else
      set_l2_indices(level0, level1, level2, ssa, source.thread_nr, ns);
  }
  return ssa;
}

exprt goto_symex_statet::rename_level2(exprt expr, const namespacet &ns)
{
  // rename all the symbols with their last known value
  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);
    set_l1_indices(level0, level1, ssa, source.thread_nr, ns);
    rename(expr.type(), ssa.get_identifier(), ns);
    ssa.update_type();

    if(l2_thread_read_encoding(ssa, ns))
    {
      // renaming taken care of by l2_thread_encoding
    }
    else if(!ssa.get_level_2().empty())
    {
      // already at L2
    }
    else
    {
      // We also consider propagation if we go up to L2.
      // L1 identifiers are used for propagation!
      auto p_it = propagation.find(ssa.get_identifier());

      if(p_it != propagation.end())
        expr = p_it->second; // already L2
      else
        set_l2_indices(level0, level1, level2, ssa, source.thread_nr, ns);
    }
  }
  else if(expr.id()==ID_symbol)
  {
    // we never rename function symbols
    if(expr.type().id() == ID_code)
    {
      rename(expr.type(), to_symbol_expr(expr).get_identifier(), ns, L2);
    }
    else
    {
      return rename_level2_ssa(ssa_exprt{expr}, ns);
    }
  }
  else if(expr.id()==ID_address_of)
  {
    auto &address_of_expr = to_address_of_expr(expr);
    rename_address(address_of_expr.object(), ns, L2);
    to_pointer_type(expr.type()).subtype() = address_of_expr.object().type();
  }
  else
  {
    // this could go wrong, but we would have to re-typecheck ...
    rename(expr.type(), irep_idt(), ns, L2);

    // do this recursively
    Forall_operands(it, expr)
      *it = rename_level2(std::move(*it), ns);

    fix_type(expr);
  }
  return expr;
}

/// thread encoding
bool goto_symex_statet::l2_thread_read_encoding(
  ssa_exprt &expr,
  const namespacet &ns)
{
  // do we have threads?
  if(threads.size()<=1)
    return false;

  // is it a shared object?
  const irep_idt &obj_identifier=expr.get_object_name();
  if(
    obj_identifier == "goto_symex::\\guard" ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
    return false;

  ssa_exprt ssa_l1=expr;
  ssa_l1.remove_level_2();
  const irep_idt &l1_identifier=ssa_l1.get_identifier();
  const exprt guard_as_expr = guard.as_expr();

  // see whether we are within an atomic section
  if(atomic_section_id!=0)
  {
    guardt write_guard{false_exprt{}};

    const auto a_s_writes = written_in_atomic_section.find(ssa_l1);
    if(a_s_writes!=written_in_atomic_section.end())
    {
      for(const auto &guard_in_list : a_s_writes->second)
      {
        guardt g = guard_in_list;
        g-=guard;
        if(g.is_true())
          // there has already been a write to l1_identifier within
          // this atomic section under the same guard, or a guard
          // that implies the current one
          return false;

        write_guard |= guard_in_list;
      }
    }

    not_exprt no_write(write_guard.as_expr());

    // we cannot determine for sure that there has been a write already
    // so generate a read even if l1_identifier has been written on
    // all branches flowing into this read
    guardt read_guard{false_exprt{}};

    a_s_r_entryt &a_s_read=read_in_atomic_section[ssa_l1];
    for(const auto &a_s_read_guard : a_s_read.second)
    {
      guardt g = a_s_read_guard; // copy
      g-=guard;
      if(g.is_true())
        // there has already been a read l1_identifier within
        // this atomic section under the same guard, or a guard
        // that implies the current one
        return false;

      read_guard |= a_s_read_guard;
    }

    guardt cond = read_guard;
    if(!no_write.op().is_false())
      cond |= guardt{no_write.op()};

    if_exprt tmp(cond.as_expr(), ssa_l1, ssa_l1);
    auto &ssa_true = to_ssa_expr(tmp.true_case());
    set_l2_indices(level0, level1, level2, ssa_true, source.thread_nr, ns);

    if(a_s_read.second.empty())
    {
      auto level2_it =
        level2.current_names.emplace(l1_identifier, std::make_pair(ssa_l1, 0))
          .first;
      symex_renaming_levelt::increase_counter(level2_it);
      a_s_read.first=level2.current_count(l1_identifier);
    }

    to_ssa_expr(tmp.false_case()).set_level_2(a_s_read.first);

    if(cond.is_false())
    {
      exprt t=tmp.false_case();
      t.swap(tmp);
    }

    const bool record_events_bak=record_events;
    record_events=false;
    assignment(ssa_l1, tmp, ns, true, true);
    record_events=record_events_bak;

    symex_target->assignment(
      guard_as_expr,
      ssa_l1,
      ssa_l1,
      ssa_l1.get_original_expr(),
      tmp,
      source,
      symex_targett::assignment_typet::PHI);

    set_l2_indices(level0, level1, level2, ssa_l1, source.thread_nr, ns);
    expr=ssa_l1;

    a_s_read.second.push_back(guard);
    if(!no_write.op().is_false())
      a_s_read.second.back().add(no_write);

    return true;
  }

  const auto level2_it =
    level2.current_names.emplace(l1_identifier, std::make_pair(ssa_l1, 0))
      .first;

  // No event and no fresh index, but avoid constant propagation
  if(!record_events)
  {
    set_l2_indices(level0, level1, level2, ssa_l1, source.thread_nr, ns);
    expr=ssa_l1;
    return true;
  }

  // produce a fresh L2 name
  symex_renaming_levelt::increase_counter(level2_it);
  set_l2_indices(level0, level1, level2, ssa_l1, source.thread_nr, ns);
  expr=ssa_l1;

  // and record that
  INVARIANT_STRUCTURED(
    symex_target!=nullptr, nullptr_exceptiont, "symex_target is null");
  symex_target->shared_read(guard_as_expr, expr, atomic_section_id, source);

  return true;
}

/// thread encoding
bool goto_symex_statet::l2_thread_write_encoding(
  const ssa_exprt &expr,
  const namespacet &ns)
{
  if(!record_events)
    return false;

  // is it a shared object?
  const irep_idt &obj_identifier=expr.get_object_name();
  if(
    obj_identifier == "goto_symex::\\guard" ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
    return false; // not shared

  // see whether we are within an atomic section
  if(atomic_section_id!=0)
  {
    ssa_exprt ssa_l1=expr;
    ssa_l1.remove_level_2();

    written_in_atomic_section[ssa_l1].push_back(guard);
    return false;
  }

  // record a shared write
  symex_target->shared_write(
    guard.as_expr(),
    expr,
    atomic_section_id,
    source);

  // do we have threads?
  return threads.size()>1;
}

void goto_symex_statet::rename_address(
  exprt &expr,
  const namespacet &ns,
  levelt level)
{
  PRECONDITION(level != L0);
  auto rename_expr = [&](exprt &e) {
    if(level == L1)
      e = rename_level1(e, ns).expr;
    else
      rename_level2(e, ns);
  };

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);

    // only do L1!
    set_l1_indices(level0, level1, ssa, source.thread_nr, ns);

    rename(expr.type(), ssa.get_identifier(), ns, level);
    ssa.update_type();
  }
  else if(expr.id()==ID_symbol)
  {
    expr=ssa_exprt(expr);
    rename_address(expr, ns, level);
  }
  else
  {
    if(expr.id()==ID_index)
    {
      index_exprt &index_expr=to_index_expr(expr);

      rename_address(index_expr.array(), ns, level);
      PRECONDITION(index_expr.array().type().id() == ID_array);
      expr.type() = to_array_type(index_expr.array().type()).subtype();

      // the index is not an address
      rename_expr(index_expr.index());
    }
    else if(expr.id()==ID_if)
    {
      // the condition is not an address
      if_exprt &if_expr=to_if_expr(expr);
      rename_expr(if_expr.cond());
      rename_address(if_expr.true_case(), ns, level);
      rename_address(if_expr.false_case(), ns, level);

      if_expr.type()=if_expr.true_case().type();
    }
    else if(expr.id()==ID_member)
    {
      member_exprt &member_expr=to_member_expr(expr);

      rename_address(member_expr.struct_op(), ns, level);

      // type might not have been renamed in case of nesting of
      // structs and pointers/arrays
      if(
        member_expr.struct_op().type().id() != ID_symbol_type &&
        member_expr.struct_op().type().id() != ID_struct_tag &&
        member_expr.struct_op().type().id() != ID_union_tag)
      {
        const struct_union_typet &su_type=
          to_struct_union_type(member_expr.struct_op().type());
        const struct_union_typet::componentt &comp=
          su_type.get_component(member_expr.get_component_name());
        PRECONDITION(comp.is_not_nil());
        expr.type()=comp.type();
      }
      else
        rename(expr.type(), irep_idt(), ns, level);
    }
    else
    {
      // this could go wrong, but we would have to re-typecheck ...
      rename(expr.type(), irep_idt(), ns, level);

      // do this recursively; we assume here
      // that all the operands are addresses
      Forall_operands(it, expr)
        rename_address(*it, ns, level);
    }
  }
}

/// Return the type corresponding to a symbol or tag. Empty optional if \p type
/// is neither a symbol or a tag.
static optionalt<typet>
type_of_symbol_or_tag(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_symbol_type)
    return ns.lookup(to_symbol_type(type)).type;
  if(type.id() == ID_union_tag)
    return ns.lookup(to_union_tag_type(type)).type;
  if(type.id() == ID_struct_tag)
    return ns.lookup(to_struct_tag_type(type)).type;
  return {};
}

void goto_symex_statet::rename(
  typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns,
  levelt level)
{
  auto rename_expr = [&](exprt &e) {
    if(level == L0)
      e = rename_level0(std::move(e), ns);
    if(level == L1)
      e = rename_level1(e, ns).expr;
    else
      rename_level2(e, ns);
  };

  // rename all the symbols with their last known value
  // to the given level

  std::pair<l1_typest::iterator, bool> l1_type_entry;
  if(level==L2 &&
     !l1_identifier.empty())
  {
    l1_type_entry=l1_types.insert(std::make_pair(l1_identifier, type));

    if(!l1_type_entry.second) // was already in map
    {
      // do not change a complete array type to an incomplete one

      const typet &type_prev=l1_type_entry.first->second;

      if(type.id()!=ID_array ||
         type_prev.id()!=ID_array ||
         to_array_type(type).is_incomplete() ||
         to_array_type(type_prev).is_complete())
      {
        type=l1_type_entry.first->second;
        return;
      }
    }
  }

  if(const auto &array_type = type_try_dynamic_cast<array_typet>(type))
  {
    rename(array_type->subtype(), irep_idt(), ns, level);
    rename_expr(array_type->size());
  }
  else if(
    const auto &s_u_type = type_try_dynamic_cast<struct_union_typet>(type))
  {
    for(auto &component : s_u_type->components())
    {
      // be careful, or it might get cyclic
      if(component.type().id() == ID_array)
        rename_expr(to_array_type(component.type()).size());
      else if(component.type().id() != ID_pointer)
        rename(component.type(), irep_idt(), ns, level);
    }
  }
  else if(type.id()==ID_pointer)
  {
    rename(to_pointer_type(type).subtype(), irep_idt(), ns, level);
  }
  else if(const auto &followed_type = type_of_symbol_or_tag(type, ns))
  {
    type = *followed_type;
    rename(type, l1_identifier, ns, level);
  }

  if(level==L2 &&
     !l1_identifier.empty())
    l1_type_entry.first->second=type;
}

void goto_symex_statet::get_original_name(exprt &expr) const
{
  get_original_name(expr.type());

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
    expr=to_ssa_expr(expr).get_original_expr();
  else
    Forall_operands(it, expr)
      get_original_name(*it);
}

void goto_symex_statet::get_original_name(typet &type) const
{
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    get_original_name(array_type.subtype());
    get_original_name(array_type.size());
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    struct_union_typet &s_u_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=s_u_type.components();

    for(auto &component : components)
      get_original_name(component.type());
  }
  else if(type.id()==ID_pointer)
  {
    get_original_name(to_pointer_type(type).subtype());
  }
}

static level1t<exprt> get_l1_name(exprt expr)
{
  // do not reset the type !
  if(auto ssa = expr_try_dynamic_cast<ssa_exprt>(expr))
    return level1t<exprt>{remove_level2(std::move(*ssa)).expr};
  Forall_operands(it, expr)
    *it = get_l1_name(std::move(*it)).expr;
  return level1t<exprt>{expr};
}

/// Dumps the current state of symex, printing the function name and location
/// number for each stack frame in the currently active thread.
/// This is for use from the debugger or in debug code; please don't delete it
/// just because it isn't called at present.
/// \param out: stream to write to
void goto_symex_statet::print_backtrace(std::ostream &out) const
{
  if(threads[source.thread_nr].call_stack.empty())
  {
    out << "No stack!\n";
    return;
  }

  out << source.function_id << " " << source.pc->location_number << "\n";

  for(auto stackit = threads[source.thread_nr].call_stack.rbegin(),
           stackend = threads[source.thread_nr].call_stack.rend();
      stackit != stackend;
      ++stackit)
  {
    const auto &frame = *stackit;
    if(frame.calling_location.is_set)
    {
      out << frame.calling_location.function_id << " "
          << frame.calling_location.pc->location_number << "\n";
    }
  }
}

/// Print the constant propagation map in a human-friendly format.
/// This is primarily for use from the debugger; please don't delete me just
/// because there aren't any current callers.
void goto_symex_statet::output_propagation_map(std::ostream &out)
{
  for(const auto &name_value : propagation)
  {
    out << name_value.first << " <- " << format(name_value.second) << "\n";
  }
}
