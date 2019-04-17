/*******************************************************************\

Module: String solver

Author: Romain Brenguier, romain.brenguier@diffblue.com

\*******************************************************************/

/// \file
/// Associates arrays and length to pointers, so that the string refinement can
/// transform builtin function calls with pointer arguments to formulas over
/// arrays.

#ifndef CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H
#define CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H

#include <set>
#include <util/std_expr.h>
#include <util/string_expr.h>

/// Generation of fresh symbols of a given type
class symbol_generatort final
{
public:
  /// Generate a new symbol expression of the given \p type with some \p prefix
  /// \return a symbol of type \p type whose name starts with
  ///   "string_refinement#" followed by \p prefix
  symbol_exprt
  operator()(const irep_idt &prefix, const typet &type = bool_typet());

private:
  unsigned symbol_count = 0;

#ifdef DEBUG
public:
  /// Keep track of created symbols, for debugging purposes.
  std::vector<symbol_exprt> created_symbols;
#endif
};

struct array_length_pairt
{
  array_string_exprt array;
  exprt length_value;

  exprt operator[](exprt index) const
  {
    return index_exprt{array, std::move(index)};
  }

  exprt operator[](const mp_integer &index) const
  {
    return array[from_integer(index, length_value.type())];
  }

  const exprt &length() const
  {
    return length_value;
  }
};

/// Correspondance between arrays and pointers string representations
class array_poolt final
{
public:
  explicit array_poolt(symbol_generatort &symbol_generator)
    : fresh_symbol(symbol_generator)
  {
  }

  const std::unordered_map<exprt, array_string_exprt, irep_hash> &
  get_arrays_of_pointers() const
  {
    return arrays_of_pointers;
  }

  /// Associate an actual finite length to infinite arrays
  /// \param s: array expression representing a string
  /// \return expression for the length of `s`
  exprt get_length(const array_string_exprt &s) const;

  void insert(const exprt &pointer_expr, array_string_exprt &array);

  /// Creates a new array if the pointer is not pointing to an array
  array_length_pairt find(const exprt &pointer, const exprt &length);

  const std::set<array_string_exprt> &created_strings() const;

  /// Construct a string expression whose length and content are new variables
  /// \param index_type: type used to index characters of the strings
  /// \param char_type: type of characters
  /// \return a string expression
  array_length_pairt
  fresh_string(const typet &index_type, const typet &char_type);

private:
  /// Associate arrays to char pointers
  std::unordered_map<exprt, array_string_exprt, irep_hash> arrays_of_pointers;

  /// Associate length to arrays of infinite size
  std::unordered_map<array_string_exprt, symbol_exprt, irep_hash>
    length_of_array;

  /// Generate fresh symbols
  symbol_generatort &fresh_symbol;

  /// Strings created in the pool
  std::set<array_string_exprt> created_strings_value;

  array_string_exprt make_char_array_for_char_pointer(
    const exprt &char_pointer,
    const typet &char_array_type);
};

/// Converts a struct containing a length and pointer to an array.
/// This allows to get a string expression from arguments of a string
/// builtion function, because string arguments in these function calls
/// are given as a struct containing a length and pointer to an array.
DEPRECATED("use array_pool.find(arg.op1(), arg.op0()) instead")
array_string_exprt of_argument(array_poolt &array_pool, const exprt &arg);

/// casts an expression to a string expression, or fetches the actual
/// string_exprt in the case of a symbol.
/// \param pool: pool of arrays representing strings
/// \param expr: an expression of refined string type
/// \return a pair of expressions, the first represents the length of the string
///   and the second is an array representing its content
array_length_pairt get_string_expr(array_poolt &pool, const exprt &expr);

#endif // CPROVER_SOLVERS_STRINGS_ARRAY_POOL_H
