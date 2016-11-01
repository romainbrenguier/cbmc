/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13 and chapter 7 on arrays of ???)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#ifndef CPROVER_SOLVER_STRING_CONSTRAINT_H
#define CPROVER_SOLVER_STRING_CONSTRAINT_H

#include <langapi/language_ui.h>
#include <solvers/refinement/bv_refinement.h>
#include <solvers/refinement/refined_string_type.h>

class index_guardt
{
private:
  exprt guard;

public:
  index_guardt() : guard(true_exprt()) {};
  index_guardt(const symbol_exprt & index, const irep_idt & id, const exprt & bound) :
    guard(binary_relation_exprt(index,id,bound)) {};

  index_guardt(const symbol_exprt & index, const exprt & bound_inf, const exprt & bound_sup);
  index_guardt(const symbol_exprt & index, const exprt & bound_sup) :
    index_guardt(index,refined_string_typet::index_zero(),bound_sup) { }


  index_guardt operator&&(const index_guardt & ig);
  index_guardt operator||(const index_guardt & ig);
  std::vector<exprt> index_bounds(const symbol_exprt & index) const;
  inline exprt to_expr() const { return guard; } 
};


class string_constraintt
{
public: 
  // String constraints are of the form
  // forall quantified_variables. index_guard => character_formula
  std::vector<symbol_exprt> quantified_variables;
  index_guardt index_guard;
  exprt character_formula;

  // Axiom with no quantification: prem => bod
  // WARNING: the premise should not contain strings
  string_constraintt(index_guardt prem, exprt bod)  : index_guard(prem), character_formula(bod) {}

  // Axiom with no quantification, and no premise
  string_constraintt(exprt bod) : string_constraintt(index_guardt(),bod) {}

  // True axiom
  string_constraintt() : string_constraintt(true_exprt()) {}

  // Add an universal quantifier
  //string_constraintt forall(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup);
  // Default bound inferior is 0
  //inline string_constraintt forall(const symbol_exprt & univ, const exprt & bound_sup) { return forall(univ,refined_string_typet::index_zero(),bound_sup); }

  
  // Bound a variable that is existentially quantified
  string_constraintt exists(const symbol_exprt & exist, const exprt & bound_inf, const exprt & bound_sup);
  // Default bound inferior is 0
  inline string_constraintt exists(const symbol_exprt & exist, const exprt & bound_sup)
  {return exists(exist,refined_string_typet::index_zero(),bound_sup);}
  
  //  static string_constraintt not_contains  (exprt univ_lower_bound, exprt univ_bound_sup, exprt premise,    exprt exists_bound_inf, exprt exists_bound_sup, exprt s0, exprt s1);

  inline bool is_simple() const { return (quantified_variables.empty()); };
  inline bool is_univ_quant() const { return (!quantified_variables.empty()); };

  inline exprt get_simple_formula() {assert(is_simple()); return implies_exprt(index_guard.to_expr(),character_formula);}
};


class string_forallt : public string_constraintt
{
public: 
  string_forallt(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup, const index_guardt &  prem, const exprt & bod);
  string_forallt(const symbol_exprt & univ, const exprt & bound_sup, const index_guardt &  prem, const exprt & bod);
  string_forallt(const symbol_exprt & univ, const exprt & bound_sup, const exprt & bod);
  
};
    
  // NOTE: not contains formulas of the form:
  // forall x in [lb,ub[. p(x) => exists y in [lb,ub[. s1[x+y] != s2[y]
  // should be encoded with a table that associate y(x)
  //// Only for NOT_CONTAINS constraints (represent s1 and s2)
  //std::vector<exprt> compared_strings;
  // used to store information about witnesses for not_contains constraints
  //  symbol_exprt witness;
  //inline exprt s0() const { assert(is_not_contains()); return compared_strings[0];}
  //inline exprt s1() const { assert(is_not_contains()); return compared_strings[1];}

  /*
  inline symbol_exprt get_univ_var() const { assert(form==UNIV_QUANT); return quantified_variable;}
  inline exprt univ_bound_inf() const { return bounds[0]; }
  inline exprt univ_bound_sup() const { return bounds[1]; }
  inline exprt univ_within_bounds() const 
  { return and_exprt(binary_relation_exprt(bounds[0],ID_le,get_univ_var()),
		     binary_relation_exprt(bounds[1],ID_gt,get_univ_var())); }
  inline exprt exists_bound_inf() const { return bounds[2]; }
  inline exprt exists_bound_sup() const { return bounds[3]; }

  inline exprt witness_of(const exprt & univ_val) const { return index_exprt(witness, univ_val); }
  */




#endif
