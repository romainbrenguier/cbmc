/*******************************************************************\

Module: String support via creating string constraints and progressively
        instantiating the universal constraints as needed.
	The procedure is described in the PASS paper at HVC'13.

Author: Alberto Griggio, alberto.griggio@gmail.com

\*******************************************************************/

#ifndef CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H
#define CPROVER_SOLVERS_REFINEMENT_STRING_REFINEMENT_H

#include <langapi/language_ui.h>

#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/string_constraint.h>
#include <solvers/refinement/string_expr.h>
#include <solvers/refinement/string_constraint_generator.h>

class string_refinementt: public bv_refinementt
{
public:
  string_refinementt(const namespacet &_ns, propt &_prop);

  // Determine which language should be used
  void set_mode();

  // Should we use counter examples at each iteration?
  bool use_counter_example;

  // Number of time we refine the index set before actually launching the solver
  int initial_loop_bound;

  virtual std::string decision_procedure_text() const
  { return "string refinement loop with "+prop.solver_text(); }

  static exprt is_positive(const exprt & x);

private:
  // Base class
  typedef bv_refinementt supert;

protected:
  typedef std::set<exprt> expr_sett;

  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_function_application
  (const function_application_exprt &expr);

  decision_proceduret::resultt dec_solve();

  // fills as many 0 as necessary in the bit vectors to have the right width
  bvt convert_bool_bv(const exprt &boole, const exprt &orig);


private:
  string_constraint_generatort generator;

  // Simple constraints that have been given to the solver
  expr_sett seen_instances;

  std::vector<string_constraintt> universal_axioms;

  std::vector<string_not_contains_constraintt> not_contains_axioms;

  int nb_sat_iteration;

  // Unquantified lemmas that have newly been added
  std::vector<exprt> cur;

  // See the definition in the PASS article
  // Warning: this is indexed by array_expressions and not string expressions
  std::map<exprt, expr_sett> current_index_set;
  std::map<exprt, expr_sett> index_set;

  // for debugging
  void display_index_set();

  // Tells if there is a index in the index set where the same variable occurs
  // several times.
  bool variable_with_multiple_occurence_in_index;

  // Natural number expression corresponding to a constant integer
  constant_exprt constant_of_nat(int i, typet t);

  void add_lemma(const exprt &lemma, bool add_to_index_set=true);

  bool boolbv_set_equality_to_true(const equal_exprt &expr);

  literalt convert_rest(const exprt &expr);

  // Instantiate forall constraints with index from the index set
  void add_instantiations();

  // Return true if the current model satisfies all the axioms
  bool check_axioms();

  // Add to the index set all the indices that appear in the formula
  void update_index_set(const exprt &formula);
  void update_index_set(const std::vector<exprt> &cur);
  void initial_index_set(const string_constraintt &axiom);
  void initial_index_set(const std::vector<string_constraintt> &string_axioms);

  exprt instantiate
  (const string_constraintt &axiom, const exprt &str, const exprt &val);

  void instantiate_not_contains(
    const string_not_contains_constraintt &axiom,
    std::vector<exprt> & new_lemmas);

  exprt compute_inverse_function(const exprt &qvar, const exprt &val, const exprt &f);

  // Rewrite a sum in a simple form: sum m_i * expr_i
  std::map<exprt, int> map_representation_of_sum(const exprt &f);
  exprt sum_over_map(std::map<exprt, int> &m, bool negated=false);

  // Simplify a sum (an expression with only plus and minus expr)
  exprt simplify_sum(const exprt &f);

  // Gets a model of an array and put it in a certain form
  exprt get_array(const exprt &arr, const exprt &size);

  // Convert the content of a string to a more readable representation.
  // This should only be used for debbuging.
  std::string string_of_array(const exprt &arr, const exprt &size);
};

#endif
