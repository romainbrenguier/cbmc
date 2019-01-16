/*******************************************************************\

Module: Guard Data Structure

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Implementation of guards using BDDs

#include "guard_bdd.h"

#include <ostream>

#include "expr_util.h"
#include "invariant.h"
#include "make_unique.h"
#include "namespace.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "symbol_table.h"
#include <algorithm>
#include <cplusplus/cuddObj.hh>
#include <cudd/cudd.h>
#include <set>

#include "range.h"

static std::size_t var_of_expr(guard_bdd_managert &manager, const exprt &expr)
{
  auto entry = manager.expr_to_var.insert(
    std::make_pair(expr, manager.var_to_expr.size()));
  if(entry.second)
    manager.var_to_expr.push_back(expr);
  return entry.first->second;
}

/// Convert an expression to a bddt
static bddt bdd_from_expr(const exprt &expr, guard_bdd_managert &manager)
{
  PRECONDITION(expr.type().id() == ID_bool);
  if(expr.is_constant())
  {
    return expr.is_false() ? manager.bdd_manager.bdd_false()
                           : manager.bdd_manager.bdd_true();
  }
  if(expr.id() == ID_not)
    return bdd_from_expr(to_not_expr(expr).op(), manager).bdd_not();

  if(expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_xor)
  {
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions have at least two operands");
    const exprt bin_expr = make_binary(expr);
    bddt op0 = bdd_from_expr(bin_expr.op0(), manager);
    bddt op1 = bdd_from_expr(bin_expr.op1(), manager);
    if(expr.id() == ID_and)
    {
      if(op0.is_false() || op1.is_false())
        return manager.bdd_manager.bdd_false();
      // Is this necessary?
      if(op0.is_true())
        return op1;
      if(op1.is_true())
        return op0;
      return op0.bdd_and(op1);
    }
    if(expr.id() == ID_or)
    {
      if(op0.is_true() || op1.is_true())
        return manager.bdd_manager.bdd_true();
      if(op0.is_false())
        return op1;
      if(op1.is_false())
        return op0;
      return op0.bdd_or(op1);
    }
    return op0.bdd_xor(op1);
  }

  if(expr.id() == ID_implies)
  {
    const implies_exprt &imp_expr = to_implies_expr(expr);
    const bddt op0 = bdd_from_expr(imp_expr.op0(), manager);
    const bddt op1 = bdd_from_expr(imp_expr.op1(), manager);
    return op1.bdd_or(op0.bdd_not());
  }
  if(
    expr.id() == ID_equal && expr.operands().size() == 2 &&
    expr.op0().type().id() == ID_bool)
  {
    const equal_exprt &eq_expr = to_equal_expr(expr);
    const bddt op0 = bdd_from_expr(eq_expr.op0(), manager);
    const bddt op1 = bdd_from_expr(eq_expr.op1(), manager);
    return op0.bdd_xor(op1).bdd_not();
  }
  if(expr.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);
    bddt i = bdd_from_expr(if_expr.cond(), manager);
    const bddt t = bdd_from_expr(if_expr.true_case(), manager);
    const bddt e = bdd_from_expr(if_expr.false_case(), manager);

    // This case seems to cause segfault in Cudd_bddIte
    if(t.is_true() && e.is_false())
      return i;

    return bddt::bdd_ite(i, t, e);
  }

  return manager.bdd_manager.bdd_variable(var_of_expr(manager, expr));
}

guard_bddt::guard_bddt(const exprt &e, guard_bdd_managert &manager)
  : manager(manager), bdd(bdd_from_expr(e, manager))
{
}

guard_bddt &guard_bddt::operator=(const guard_bddt &other)
{
  PRECONDITION(&manager == &other.manager);
  bdd = other.bdd;
  return *this;
}

guard_bddt &guard_bddt::operator=(guard_bddt &&other) noexcept
{
  PRECONDITION(&manager == &other.manager);
  std::swap(bdd, other.bdd);
  return *this;
}

void guard_bddt::guard_expr(exprt &dest) const
{
  if(is_true())
  {
    // do nothing
  }
  else
  {
    if(dest.is_false())
    {
      dest = boolean_negate(as_expr());
    }
    else
    {
      implies_exprt tmp;
      tmp.op0() = as_expr();
      tmp.op1().swap(dest);
      dest.swap(tmp);
    }
  }
}

guard_bddt &guard_bddt::append(const guard_bddt &guard)
{
  bdd = bdd.bdd_and(guard.bdd);
  return *this;
}

guard_bddt &guard_bddt::add(const exprt &expr)
{
  bdd = bdd.bdd_and(bdd_from_expr(expr, manager));
  return *this;
}

guard_bddt &operator-=(guard_bddt &g1, const guard_bddt &g2)
{
  g1.bdd = g1.bdd.constrain(g2.bdd.bdd_or(g1.bdd));
  return g1;
}

guard_bddt &operator|=(guard_bddt &g1, const guard_bddt &g2)
{
  g1.bdd = g1.bdd.bdd_or(g2.bdd);
  return g1;
}

static and_exprt make_and(exprt e1, exprt e2)
{
  if(const auto &and_expr = expr_try_dynamic_cast<and_exprt>(e1))
  {
    and_expr->operands().push_back(std::move(e2));
    return *and_expr;
  }
  if(const auto &and_expr = expr_try_dynamic_cast<and_exprt>(e2))
  {
    and_expr->operands().push_back(std::move(e1));
    return *and_expr;
  }
  return and_exprt(std::move(e1), std::move(e2));
}

static or_exprt make_or(exprt e1, exprt e2)
{
  if(const auto &or_expr = expr_try_dynamic_cast<or_exprt>(e1))
  {
    or_expr->operands().push_back(std::move(e2));
    return *or_expr;
  }
  if(const auto &or_expr = expr_try_dynamic_cast<or_exprt>(e2))
  {
    or_expr->operands().push_back(std::move(e1));
    return *or_expr;
  }
  return or_exprt(std::move(e1), std::move(e2));
}

/// \param r: node to convert
/// \param manager: guard manager corresponding to the guard from which \p r
///   was obtained
/// \param is_complement: whether we want the negation of thet expression
///   represented by r
/// \param cache: map of already computed values
static exprt node_as_expr(
  const bdd_nodet &r,
  const guard_bdd_managert &manager,
  bool is_complement,
  std::unordered_map<long, exprt> &cache)
{
  if(r.is_constant())
  {
    // != is used for logical xor
    return r.is_complement() != is_complement ? (exprt)(false_exprt())
                                              : true_exprt();
  }

  // Look-up cache for already computed value
  auto insert_result = cache.emplace(r.id(), nil_exprt());
  if(insert_result.second)
  {
    insert_result.first->second = [&]() -> exprt {
      if(r.then_branch().is_constant())
      {
        if(r.else_branch().is_constant())
        {
          // 3 negations are equivalent to one
          if(
            (is_complement != r.is_complement()) != r.then_branch().is_complement())
            return not_exprt(manager.var_to_expr[r.index()]);
          return manager.var_to_expr[r.index()];
        }
        if((is_complement != r.is_complement()) != r.then_branch().is_complement())
        {
          return make_and(
            not_exprt(manager.var_to_expr[r.index()]),
            node_as_expr(
              r.else_branch(),
              manager,
              r.is_complement() != is_complement,
              cache));
        }
        return make_or(
          manager.var_to_expr[r.index()],
          node_as_expr(
            r.else_branch(),
            manager,
            r.is_complement() != is_complement,
            cache));
      }

      if(r.else_branch().is_constant())
      {
        // 3 negations are equivalent to one.
        if((is_complement != r.is_complement()) != r.else_branch().is_complement())
        {
          // else branch is false.
          return make_and(
            manager.var_to_expr[r.index()],
            node_as_expr(
              r.then_branch(),
              manager,
              r.is_complement() != is_complement,
              cache));
        }
        return make_or(
          not_exprt(manager.var_to_expr[r.index()]),
          node_as_expr(
            r.then_branch(),
            manager,
            r.is_complement() != is_complement,
            cache));
      }

      return if_exprt(
        manager.var_to_expr[r.index()],
        node_as_expr(
          r.then_branch(), manager, r.is_complement() != is_complement, cache),
        node_as_expr(
          r.else_branch(), manager, r.is_complement() != is_complement, cache));
    }();
  }
  return insert_result.first->second;
}

exprt guard_bddt::as_expr() const
{
  std::unordered_map<long, exprt> cache;
  return node_as_expr(bdd.node(), manager, false, cache);
}
