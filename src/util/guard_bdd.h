/*******************************************************************\

Module: Guard Data Structure

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Guard Data Structure
/// Implementation using BDDs

#ifndef CPROVER_UTIL_GUARD_BDD_H
#define CPROVER_UTIL_GUARD_BDD_H

#include <iosfwd>
#include <memory>

// #ifdef HAS_CUDD
#if 0
#include "bdd.h"
#else
#include "bdd_mini.h"
#endif

#include "make_unique.h"
#include "std_expr.h"

struct guard_bdd_managert
{
  bdd_managert bdd_manager;
  std::unordered_map<exprt, std::size_t, irep_hash> expr_to_var;
  std::vector<exprt> var_to_expr;

  guard_bdd_managert() = default;
  guard_bdd_managert(const bdd_managert &) = delete;
};

class guard_bddt
{
public:
  guard_bddt(const exprt &e, guard_bdd_managert &manager);
  guard_bddt(const guard_bddt &other) : manager(other.manager), bdd(other.bdd)
  {
  }

  guard_bddt &operator=(const guard_bddt &other);
  guard_bddt &operator=(guard_bddt &&other) noexcept;
  guard_bddt &add(const exprt &expr);
  guard_bddt &append(const guard_bddt &guard);
  exprt as_expr() const;

  /// Assign dest to `guard => dest` unless guard or dest are trivial.
  void guard_expr(exprt &dest) const;

  bool is_true() const
  {
    return bdd.is_true();
  }

  bool is_false() const
  {
    return bdd.is_false();
  }

  /// Transforms \p g1 into \c g1' such that `g1' & g2 => g1 => g1'`
  /// and returns a reference to g1.
  friend guard_bddt &operator-=(guard_bddt &g1, const guard_bddt &g2);

  friend guard_bddt &operator|=(guard_bddt &g1, const guard_bddt &g2);

  guard_bddt operator!() const
  {
    return guard_bddt(manager, bdd.bdd_not());
  }

  guard_bdd_managert &manager;

private:
  bddt bdd;

  guard_bddt(guard_bdd_managert &manager, bddt bdd)
    : manager(manager), bdd(std::move(bdd))
  {
  }
};

#endif // CPROVER_UTIL_GUARD_BDD_H
