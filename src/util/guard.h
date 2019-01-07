/*******************************************************************\

Module: Guard Data Structure

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Guard Data Structure

#ifndef CPROVER_UTIL_GUARD_H
#define CPROVER_UTIL_GUARD_H

#include <iosfwd>

#include <memory>

#include "std_expr.h"
//#include <cudd/cudd.h>
//#include <cplusplus/cuddObj.hh>
#include "make_unique.h"
#include "../../cudd-3.0.0/cplusplus/cuddObj.hh"

struct guard_managert
{
  Cudd bdd_manager;
  std::unordered_map<exprt, std::size_t, irep_hash> expr_to_var;
  std::vector<exprt> var_to_expr;
};

class guardt
{
public:
  explicit guardt(guard_managert &manager);
  guardt(const guardt &other) : bdd(other.bdd), manager(other.manager)
  {
  }

  guardt& operator=(const guardt &other)
  {
    bdd = other.bdd;
    manager = other.manager;
    return *this;
  }

  guardt& operator=(guardt &&other)
  {
    std::swap(bdd, other.bdd);
    manager = other.manager;
    return *this;
  }

  guardt &add(const exprt &expr);

  guardt &append(const guardt &guard);

  guardt implies(const guardt &);

  guardt &from_expr(const exprt &expr);
  guardt &set_to_true();

  exprt as_expr() const;

  /// Return a expression equivalent to the guard with no boolean operators if
  /// possible.
  optionalt<exprt> as_simple_expr() const;

  void guard_expr(exprt &dest) const;

  friend guardt &operator -= (guardt &g1, const guardt &g2);
  friend guardt &operator |= (guardt &g1, const guardt &g2);

  bool is_true() const;
  bool is_false() const;
  guardt &negate(){ bdd = !bdd; return *this; }
  guardt operator!() const
  { guardt result(*this); result.negate(); return result;};
  bool operator==(const guardt &other) const { return bdd == other.bdd; }
  guardt &operator |=(const exprt &e);

  bool any_expr(std::function<bool(const exprt &)> pred) const;
  void replace_expr(std::function<exprt(const exprt &)> f);
  void replace_expr(std::function<void(exprt &)> f);

  BDD bdd;
  guard_managert &manager;
private:
};

inline bool is_false(const guardt &g)
{
  return g.is_false();
}

#endif // CPROVER_UTIL_GUARD_H
