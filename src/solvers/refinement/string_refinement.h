/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
        The procedure is described in the PASS paper at HVC'13:
        "PASS: String Solving with Parameterized Array and Interval Automaton"
        by Guodong Li and Indradeep Ghosh

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

/// \file
/// String support via creating string constraints and progressively
///   instantiating the universal constraints as needed. The procedure is
///   described in the PASS paper at HVC'13: "PASS: String Solving with
///   Parameterized Array and Interval Automaton" by Guodong Li and Indradeep
///   Ghosh

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H

#include <util/string_expr.h>
#include <util/replace_expr.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_constraint_generator.h>
#include <solvers/refinement/string_refinement_invariant.h>

#define MAX_NB_REFINEMENT 100
#define CHARACTER_FOR_UNKNOWN '?'

/// Similar interface to union-find for expressions, with a function for
/// replacing sub-expressions by their result for find.
class union_find_replacet
{
public:
  /// return true if unmodified
  bool replace_expr(exprt &expr) const
  {
    bool unchanged=::replace_expr(map_, expr);
    while(!unchanged && !::replace_expr(map_, expr))
      continue;
    return unchanged;
  }

  exprt find_expr(exprt expr) const
  {
    replace_expr(expr);
    return expr;
  }

  exprt add_symbol(const exprt &expr, const exprt &dst);

  std::vector<std::pair<exprt, exprt>> to_vector()
  {
    std::vector<std::pair<exprt, exprt>> equations;
    for(const auto &pair : map_)
      equations.emplace_back(pair.first, find_expr(pair.second));
    return equations;
  }

private:
  replace_mapt map_;
};

class string_refinementt: public bv_refinementt
{
public:
  /// string_refinementt constructor arguments
  struct infot
  {
    const namespacet *ns=nullptr;
    propt *prop=nullptr;
    language_uit::uit ui=language_uit::uit::PLAIN;
    unsigned refinement_bound=0;
    size_t string_max_length=std::numeric_limits<size_t>::max();
    /// Make non-deterministic character arrays have at least one character
    bool string_non_empty=false;
    /// Concretize strings after solver is finished
    bool trace=false;
    /// Make non-deterministic characters printable
    bool string_printable=false;
    unsigned max_node_refinement=5;
    bool refine_arrays=false;
    bool refine_arithmetic=false;
    bool use_counter_example=false;
  };

  explicit string_refinementt(const infot &);


  virtual std::string decision_procedure_text() const override
  {
    return "string refinement loop with "+prop.solver_text();
  }

  exprt get(const exprt &expr) const override;

protected:
  decision_proceduret::resultt dec_solve() override;

private:
  const bool use_counter_example;
  const bool do_concretizing;
  // Base class
  typedef bv_refinementt supert;

  string_refinementt(const infot &, bool);
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);

  unsigned initial_loop_bound;

  string_constraint_generatort generator;

  const bool non_empty_string;
  std::set<exprt> nondet_arrays;

  // Simple constraints that have been given to the solver
  std::set<exprt> seen_instances;

  std::vector<string_constraintt> universal_axioms;

  std::vector<string_not_contains_constraintt> not_contains_axioms;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> cur;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions
  std::map<exprt, std::vector<exprt>> current_index_set_;
  std::map<exprt, std::set<exprt>> index_set_;
  union_find_replacet symbol_resolve;

  std::vector<equal_exprt> equations_;
  std::list<std::pair<exprt, bool>> non_string_axioms;

  // Length of char arrays found during concretization
  std::map<exprt, exprt> found_length;
  // Content of char arrays found during concretization
  std::map<exprt, array_exprt> found_content;

  // Map pointers to array symbols
  std::map<exprt, symbol_exprt> pointer_map;

  void add_equivalence(const irep_idt & lhs, const exprt & rhs);

  void display_index_set();

  void add_lemma(const exprt &lemma,
                 bool simplify=true,
                 bool add_to_index_set=true);

  exprt substitute_function_applications(exprt expr);
  typet substitute_java_string_types(typet type);
  exprt substitute_java_strings(exprt expr);
  exprt substitute_array_with_expr(const exprt &expr, const exprt &index) const;
  void substitute_array_access(exprt &expr) const;
  bool add_axioms_for_string_assigns(const exprt &lhs, const exprt &rhs);
  void set_to(const exprt &expr, bool value) override;

  void add_instantiations();
  void debug_model();
  bool check_axioms();
  bool is_axiom_sat(
    const exprt &axiom, const symbol_exprt& var, exprt &witness);

  void set_char_array_equality(const exprt &lhs, const exprt &rhs);
  void update_index_set(const exprt &formula);
  void update_index_set(const std::vector<exprt> &cur);
  void initial_index_set(const string_constraintt &axiom);
  void initial_index_set(const std::vector<string_constraintt> &string_axioms);
  void add_to_index_set(const exprt &s, exprt i);

  exprt instantiate(
    const string_constraintt &axiom, const exprt &str, const exprt &val);

  std::vector<exprt> instantiate_not_contains(
    const string_not_contains_constraintt &axiom);

  exprt compute_inverse_function(
    const exprt &qvar, const exprt &val, const exprt &f);

  std::map<exprt, int> map_representation_of_sum(const exprt &f) const;
  exprt sum_over_map(
    std::map<exprt, int> &m, const typet &type, bool negated=false) const;

  bool is_valid_string_constraint(const string_constraintt &expr);

  exprt simplify_sum(const exprt &f) const;

  void concretize_string(const exprt &expr);
  void concretize_results();
  void concretize_lengths();

  exprt get_array(const exprt &arr) const;
  exprt get_char_array_in_model(exprt arr) const;
  exprt get_char_pointer_in_model(const exprt &ptr) const;

  std::string string_of_array(const array_exprt &arr) const;
};

exprt substitute_array_lists(exprt expr, size_t string_max_length);

exprt concretize_arrays_in_expression(
  exprt expr, std::size_t string_max_length);

bool is_char_array_type(const typet &type, const namespacet &ns);

/// Convert index-value map to a vector of values. If a value for an
/// index is not defined, set it to the value referenced by the next higher
/// index. The length of the resulting vector is the key of the map's
/// last element + 1
/// \param index_value: map containing values of specific vector cells
/// \return Vector containing values as described in the map
template <typename T>
std::vector<T> fill_in_map_as_vector(
  const std::map<std::size_t, T> &index_value)
{
  std::vector<T> result;
  if(!index_value.empty())
  {
    result.resize(index_value.rbegin()->first+1);
    for(auto it=index_value.rbegin(); it!=index_value.rend(); ++it)
    {
      const std::size_t index=it->first;
      const T value=it->second;
      const auto next=std::next(it);
      const std::size_t leftmost_index_to_pad=
        next!=index_value.rend()
        ? next->first+1
        : 0;
      for(std::size_t j=leftmost_index_to_pad; j<=index; j++)
        result[j]=value;
    }
  }
  return result;
}
#endif
