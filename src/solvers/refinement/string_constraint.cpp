/** -*- C++ -*- *****************************************************\

Module: String constraints
        (see the PASS paper at HVC'13)

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

#include <solvers/refinement/string_constraint.h>


index_guardt index_guardt::operator&&(const index_guardt & ig)
{
  index_guardt conj;
  conj.guard = and_exprt(guard,ig.guard);
  return conj;
  }

index_guardt index_guardt::operator||(const index_guardt & ig)
{
  index_guardt disj;
  disj.guard = or_exprt(guard,ig.guard);
  return disj;
}


std::vector<exprt> index_guardt::index_bounds(const symbol_exprt & index) const
{
  std::vector<exprt> bounds;
  std::vector<exprt> to_process;
  to_process.push_back(guard);
  while (!to_process.empty())
    {
      exprt cur = to_process.back();
      to_process.pop_back();
      if (cur.id() == ID_and || cur.id() == ID_or)
	for(int i; i < cur.operands().size(); i++)
	  to_process.push_back(cur.operands()[i]);
      else
	if(cur.op0() == index)
	  bounds.push_back(cur.op1());

    }
  return bounds;
}

index_guardt::index_guardt
(const symbol_exprt & index, const exprt & bound_inf, const exprt & bound_sup)
{
  binary_relation_exprt inf(index,ID_ge,bound_inf);
  binary_relation_exprt sup(index,ID_lt,bound_sup);
  guard = and_exprt(inf,sup);
}



string_constraintt string_constraintt::exists
(const symbol_exprt & exist, const exprt & bound_inf, const exprt & bound_sup)
{
  string_constraintt sc(*this);
  sc.character_formula = and_exprt(sc.character_formula, index_guardt(exist,bound_inf,bound_sup).to_expr());
  return sc;
}

string_forallt::string_forallt(const symbol_exprt & univ, const exprt & bound_inf, const exprt & bound_sup, const index_guardt & prem, const exprt & bod):string_constraintt(prem,bod)
{
  quantified_variables.push_back(univ);
  index_guard = index_guard && index_guardt(univ,bound_inf,bound_sup);
}

string_forallt::string_forallt
(const symbol_exprt & univ, const exprt & bound_sup, const index_guardt & prem, const exprt & bod)
  : string_forallt(univ,refined_string_typet::index_zero(),bound_sup,index_guardt(),bod) {}


string_forallt::string_forallt(const symbol_exprt & univ, const exprt & bound_sup, const exprt & bod)
  : string_forallt(univ,bound_sup,index_guardt(),bod) {}


/*
string_constraintt string_constraintt::not_contains(exprt univ_bound_inf, exprt univ_bound_sup, 
				 exprt premise, exprt exists_bound_inf, 
				 exprt exists_bound_sup, exprt s0, exprt s1)
{

  string_constraintt sc(premise);
  sc.form = NOT_CONTAINS;
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_inf);
  sc.bounds.push_back(univ_bound_sup);
  sc.bounds.push_back(exists_bound_inf);
  sc.bounds.push_back(exists_bound_sup);
  sc.compared_strings.push_back(s0);
  sc.compared_strings.push_back(s1);
  return sc;
}
*/
