//
// Created by romain on 08/03/19.
//

#ifndef TEST_GEN_SUPERBUILD_DECORATED_SYMBOL_EXPR_H
#define TEST_GEN_SUPERBUILD_DECORATED_SYMBOL_EXPR_H

/// Expression to hold a symbol (variable) with extra accessors to
/// ID_c_static_lifetime and ID_C_thread_local
class decorated_symbol_exprt:public symbol_exprt
{
public:
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  decorated_symbol_exprt()
  {
  }

  /// \param identifier: Name of symbol
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  explicit decorated_symbol_exprt(const irep_idt &identifier):
    symbol_exprt(identifier)
  {
  }

  /// \param type: Type of symbol
  DEPRECATED("use decorated_symbol_exprt(identifier, type) instead")
  explicit decorated_symbol_exprt(const typet &type):
    symbol_exprt(type)
  {
  }

  /// \param identifier: Name of symbol
  /// \param type: Type of symbol
  decorated_symbol_exprt(
    const irep_idt &identifier,
    const typet &type):symbol_exprt(identifier, type)
  {
  }

  bool is_static_lifetime() const
  {
    return get_bool(ID_C_static_lifetime);
  }

  void set_static_lifetime()
  {
    return set(ID_C_static_lifetime, true);
  }

  void clear_static_lifetime()
  {
    remove(ID_C_static_lifetime);
  }

  bool is_thread_local() const
  {
    return get_bool(ID_C_thread_local);
  }

  void set_thread_local()
  {
    return set(ID_C_thread_local, true);
  }

  void clear_thread_local()
  {
    remove(ID_C_thread_local);
  }
};

#endif //TEST_GEN_SUPERBUILD_DECORATED_SYMBOL_EXPR_H
