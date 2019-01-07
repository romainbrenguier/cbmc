/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "guard.h"

#include <ostream>

#include "namespace.h"
#include "expr_util.h"
#include "invariant.h"
#include "simplify_utils.h"
#include "std_expr.h"
#include "symbol_table.h"
#include "make_unique.h"
#include <cudd/cudd.h>
#include <cplusplus/cuddObj.hh>
#include <set>
#include <algorithm>

#include "profiler.h"
#include "format_expr.h"
#include "range.h"

static std::size_t var_of_expr(guard_managert &manager, const exprt &expr)
{
  auto entry = manager.expr_to_var
    .insert(std::make_pair(expr, manager.var_to_expr.size()));
  if(entry.second)
    manager.var_to_expr.push_back(expr);
  return entry.first->second;
}

guardt::guardt(guard_managert &manager)
  : bdd(manager.bdd_manager.bddOne()),
    manager(manager)
{
}


/// Assign dest to `bdd => dest` unless bdd or dest are trivial.
/// Warning: Assigning dest to `!bdd || dest` breaks correctness of CBMC
void guardt::guard_expr(exprt &dest) const
{
  if(is_true())
    return;
  if(dest.is_false())
  {
    dest = boolean_negate(as_expr());
    return;
  }
  implies_exprt tmp;
  tmp.op0()=as_expr();
  tmp.op1().swap(dest);
  dest.swap(tmp);
}

guardt &guardt::append(const guardt &guard)
{
  bdd = bdd.And(guard.bdd);
  return *this;
}

guardt guardt::implies(const guardt &guard)
{
  auto implies_guard = guardt(manager);
  implies_guard.bdd = guard.bdd.Or(!bdd);
  return implies_guard;
}

guardt &guardt::set_to_true()
{
  bdd = manager.bdd_manager.bddOne();
  return *this;
}

/// Convert an expression to a BDD
static BDD bdd_from_expr(const exprt &expr, guard_managert &manager)
{
  PROFILER_BREAKPOINT;
  auto result =[&]{
      PRECONDITION(expr.type().id() == ID_bool);
  if(expr.is_constant())
    return expr.is_false() ? manager.bdd_manager.bddZero()
                           : manager.bdd_manager.bddOne();
  if(expr.id()==ID_not)
    return !bdd_from_expr(to_not_expr(expr).op(), manager);

  if(expr.id()==ID_and || expr.id()==ID_or || expr.id()==ID_xor)
  {
    DATA_INVARIANT(
      expr.operands().size() >= 2,
      "logical and, or, and xor expressions have at least two operands");
    const exprt bin_expr = make_binary(expr);
    const BDD op0 = bdd_from_expr(bin_expr.op0(), manager);
    const BDD op1 = bdd_from_expr(bin_expr.op1(), manager);
    if(expr.id() == ID_and)
    {
      if(op0.IsZero() || op1.IsZero())
        return manager.bdd_manager.bddZero();
      // Is this necessary?
      if(op0.IsOne())
        return op1;
      if(op1.IsOne())
        return op0;
      return op0.And(op1);
    }
    if(expr.id() == ID_or)
    {
      if(op0.IsOne() || op1.IsOne())
        return manager.bdd_manager.bddOne();
      if(op0.IsZero())
        return op1;
      if(op1.IsZero())
        return op0;
      return op0.Or(op1);
    }
    return op0.Xor(op1);
  }

  if(expr.id()==ID_implies)
  {
    const implies_exprt &imp_expr=to_implies_expr(expr);
    const BDD op0 = bdd_from_expr(imp_expr.op0(), manager);
    const BDD op1 = bdd_from_expr(imp_expr.op1(), manager);
    return op1.Or(!op0);
  }
  if(expr.id()==ID_equal &&
     expr.operands().size()==2 &&
     expr.op0().type().id()==ID_bool)
  {
    const equal_exprt &eq_expr=to_equal_expr(expr);
    const BDD op0=bdd_from_expr(eq_expr.op0(), manager);
    const BDD op1=bdd_from_expr(eq_expr.op1(), manager);
    return !(op0.Xor(op1));
  }
  if(expr.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(expr);
    const BDD i = bdd_from_expr(if_expr.cond(), manager);
    const BDD t = bdd_from_expr(if_expr.true_case(), manager);
    const BDD e = bdd_from_expr(if_expr.false_case(), manager);

    // This case seems to cause segfault in Cudd_bddIte
    if(t.IsOne() && e.IsZero())
      return i;

    return i.Ite(t, e);
  }

  return manager.bdd_manager.bddVar(var_of_expr(manager, expr));
  }();
  PROFILER_BREAKPOINT;
  return result;
}

guardt &guardt::from_expr(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);
  bdd = bdd_from_expr(expr, manager);
  return *this;
}

guardt &guardt::add(const exprt &expr)
{
  bdd = bdd.And(bdd_from_expr(expr, manager));
  return *this;
}

bool guardt::is_true() const
{
  return bdd.IsOne();
}

bool guardt::is_false() const
{
  return bdd.IsZero();
}

guardt& guardt::operator|=(const exprt &e)
{
  BDD bdd_e = bdd_from_expr(e, manager);
  bdd = bdd.Or(bdd_e);
  return *this;
}

void guardt::replace_expr(std::function<exprt(const exprt &)> f)
{
  exprt e = as_expr();
  from_expr(f(e));
}

void guardt::replace_expr(std::function<void(exprt &)> f)
{
  exprt e = as_expr();
  f(e);
  from_expr(e);
}

bool guardt::any_expr(std::function<bool(const exprt &)> pred) const
{
  std::set<DdNode*> visited;
  std::set<int> variables;
  std::vector<DdNode*> to_visit(1, bdd.getNode());
  while(!to_visit.empty())
  {
    const auto current = to_visit.back();
    to_visit.pop_back();
    if(!Cudd_IsConstant(current))
    {
      variables.insert(Cudd_NodeReadIndex(current));
      if(visited.insert(Cudd_T(current)).second)
        to_visit.push_back(Cudd_T(current));
      if(visited.insert(Cudd_E(current)).second)
        to_visit.push_back(Cudd_E(current));
    }
  }

  auto range = make_range(variables)
    .map([&](int i){ return manager.var_to_expr[i];})
    .filter(pred);
  return range.begin() != range.end();
}

/// Simplify the guard \p g1 assuming \p g2 holds.
/// The function transforms \p g1 into \c g1' and returns a reference to it such
/// that `g1' & g2` is logically equivalent to `g1 & g2`.
guardt &operator -= (guardt &g1, const guardt &g2)
{
  // Craig interpolation, gives `f` such that `g1 => f => (g1 || !g2)`
  g1.bdd = g1.bdd.Interpolate(g1.bdd.Or(!g2.bdd));
  return g1;
}

guardt &operator |= (guardt &g1, const guardt &g2)
{
  g1.bdd = g1.bdd.Or(g2.bdd);
  return g1;
}

optionalt<exprt> guardt::as_simple_expr() const
{
  DdNode * r = bdd.getNode();
  if(!Cudd_IsConstant(Cudd_T(r)) || !Cudd_IsConstant (Cudd_E(r)))
    return {};
  if(Cudd_IsComplement(r) ^ Cudd_IsComplement(Cudd_T(r)))
    return manager.var_to_expr[Cudd_NodeReadIndex(r)];
  return not_exprt(manager.var_to_expr[Cudd_NodeReadIndex(r)]);
}

/// \param r: node to convert
/// \param manager: guard manager corresponding to the guard from which \p r
///   was obtained
/// \param is_complement: whether we want the negation of thet expression
///   represented by r
/// \param cache:
static exprt node_as_expr(
  DdNode *r,
  const guard_managert &manager,
  bool is_complement,
  std::unordered_map<long, exprt> &cache)
{
  if(Cudd_IsConstant(r))
  {
    return Cudd_IsComplement(r) ^ is_complement ? (exprt)(false_exprt())
                                                : true_exprt();
  }

  // Look-up cache for already computed value
  auto insert_result = cache.emplace((long)r, nil_exprt());
  if(insert_result.second)
  {
    insert_result.first->second = [&]() -> exprt {
      // Not sure this is necessary
      if(Cudd_IsConstant(Cudd_T(r)))
      {
        // 3 negations are equivalent to one
        if(Cudd_IsConstant(Cudd_E(r)))
        {
          // 3 negations are equivalent to one
          if(is_complement ^ Cudd_IsComplement(r) ^ Cudd_IsComplement(Cudd_T(r)))
            return not_exprt(manager.var_to_expr[Cudd_NodeReadIndex(r)]);
          return manager.var_to_expr[Cudd_NodeReadIndex(r)];
        }
        if(is_complement ^ Cudd_IsComplement(r) ^ Cudd_IsComplement(Cudd_T(r)))
          return and_exprt(
            not_exprt(manager.var_to_expr[Cudd_NodeReadIndex(r)]),
            node_as_expr(Cudd_E(r), manager, Cudd_IsComplement(r)^is_complement, cache));

        return or_exprt(
          manager.var_to_expr[Cudd_NodeReadIndex(r)],
          node_as_expr(Cudd_E(r), manager, Cudd_IsComplement(r)^is_complement, cache));
      }

      if(Cudd_IsConstant(Cudd_E(r)))
      {
        // 3 negations are equivalent to one
        if(is_complement ^ Cudd_IsComplement(r) ^ Cudd_IsComplement(Cudd_E(r)))
          return and_exprt(
            manager.var_to_expr[Cudd_NodeReadIndex(r)],
            node_as_expr(Cudd_T(r), manager, Cudd_IsComplement(r)^is_complement, cache));
        return and_exprt(
          not_exprt(manager.var_to_expr[Cudd_NodeReadIndex(r)]),
          node_as_expr(Cudd_T(r), manager, Cudd_IsComplement(r)^is_complement, cache));
      }

      return if_exprt(
        manager.var_to_expr[Cudd_NodeReadIndex(r)],
        node_as_expr(Cudd_T(r), manager, Cudd_IsComplement(r)^is_complement, cache),
        node_as_expr(Cudd_E(r), manager, Cudd_IsComplement(r)^is_complement, cache));
    }();
  }
  return insert_result.first->second;
}

exprt guardt::as_expr() const
{
  PROFILER_BREAKPOINT;
  std::unordered_map<long, exprt> cache;
  auto result = node_as_expr(bdd.getNode(), manager, false, cache);
  PROFILER_BREAKPOINT;
//  std::cout << "result : " << format(result) << std::endl;
  return result;
}
