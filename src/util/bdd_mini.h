/*******************************************************************\

Module: Binary Decision Diagrams

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Interface to miniBDD functions that are used in CBMC
/// To ensure we can easily switch to other BDD libraries if needed,
/// the BDD functions should only be accessed from this header file.

#ifndef CPROVER_UTIL_BDD_MINI_H
#define CPROVER_UTIL_BDD_MINI_H

#include "unordered_map"

#include <solvers/miniBDD/miniBDD.h>

class bdd_managert;
class bddt;
class bdd_nodet;

static std::unordered_map<unsigned int, unsigned int> bdd_var_to_index;

/// Low level access to the structure of the BDD, read-only.
class bdd_nodet
{
public:
  bool is_constant() const
  {
    return node->node_number <= 1;
  }

  bool is_complement() const
  {
    return node->node_number == 0;
  }

  unsigned int index() const
  {
    return bdd_var_to_index.at(node->var);
  }

  bdd_nodet then_branch() const
  {
    return bdd_nodet(node->high.node);
  }

  bdd_nodet else_branch() const
  {
    return bdd_nodet(node->low.node);
  }

  long id() const
  {
    return (long)node;
  }

private:
  mini_bdd_nodet *node;
  explicit bdd_nodet(mini_bdd_nodet *node) : node(node)
  {
  }

  friend class bddt;
};

/// Logical operations on BDDs
class bddt : private mini_bddt
{
public:
  bdd_nodet node() const
  {
    return bdd_nodet(mini_bddt::node);
  }

  bool equals(const bddt &other) const
  {
    return node().id() == other.node().id();
  }

  bool is_true() const
  {
    return mini_bddt::is_true();
  }

  bool is_false() const
  {
    return mini_bddt::is_false();
  }

  bddt bdd_not() const
  {
    return bddt(!(*this));
  }

  bddt bdd_or(const bddt &other) const
  {
    return bddt((*this)|(other));
  }

  bddt bdd_and(const bddt &other) const
  {
    return bddt((*this)&(other));
  }

  bddt bdd_xor(const bddt &other) const
  {
    return bddt((*this)^(other));
  }

  static bddt bdd_ite(const bddt &i, const bddt &t, const bddt &e)
  {
    return i.bdd_and(t).bdd_or(i.bdd_not().bdd_and(e));
  }

  bddt constrain(const bddt &other)
  {
    // This is correct, though not very useful
    return bddt(mini_bddt::constrain(other));
  }

  bddt &operator=(const bddt &other)
  {
    if(this != &other)
      mini_bddt::operator=(other);
    return *this;
  }

private:
  friend class bdd_managert;
  explicit bddt(const mini_bddt &bdd) : mini_bddt(bdd)
  {
  }
};

/// Manager for BDD creation
class bdd_managert : private mini_bdd_mgrt
{
public:
  bddt bdd_true()
  {
    return bddt(True());
  }

  bddt bdd_false()
  {
    return bddt(False());
  }

  bddt bdd_variable(unsigned int index)
  {
    auto it = index_to_bdd.find(index);
    if(it != index_to_bdd.end())
      return it->second;
    auto var = Var(std::to_string(index));
    auto emplace_result =
      index_to_bdd.emplace(index, bddt(var));
    bdd_var_to_index[var.var()] = index;
    return emplace_result.first->second;
  }

private:
  std::unordered_map<unsigned int, bddt> index_to_bdd;
};

#endif // CPROVER_UTIL_BDD_MINI_H
