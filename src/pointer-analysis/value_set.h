/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_POINTER_ANALYSIS_VALUE_SET_H
#define CPROVER_POINTER_ANALYSIS_VALUE_SET_H

#include <set>

#include <util/mp_arith.h>
#include <util/reference_counting.h>

#include "object_numbering.h"
#include "value_sets.h"

class namespacet;

// An access path entry, indicating that an external object was accessed using e.g.
// member-x--of-dereference (represented "->x") at function f location (instruction offset) z.

class access_path_entry_exprt : public exprt
{
 public:
  inline access_path_entry_exprt():exprt("access-path-entry") {}
  inline access_path_entry_exprt(const irep_idt& label,
                                 const irep_idt& function,
                                 const irep_idt& loc)
    :exprt("access-path-entry")
  {
    set_label(label);
    set("access-path-function", function);
    set("access-path-loc", loc);
  }
  
  inline irep_idt label() const { return get("access-path-label"); }
  inline void set_label(const irep_idt& i) { set("access-path-label", i); }
  inline irep_idt function() const { return get("access-path-function"); }
  inline irep_idt loc() const { return get("access-path-loc"); }
};

static inline access_path_entry_exprt& to_access_path_entry(exprt& e) {
  return static_cast<access_path_entry_exprt&>(e);
}

static inline const access_path_entry_exprt& to_access_path_entry(const exprt& e) {
  return static_cast<const access_path_entry_exprt&>(e);
}

// Represents an external unknown points-to set that can't be directly referenced with a symbol,
// such as "arg1->x"

class external_value_set_exprt : public exprt
{
 public:
  inline external_value_set_exprt():exprt("external-value-set")
  {
    operands().resize(1);
    op0().id(ID_unknown);
  }

  inline external_value_set_exprt(const irep_idt& id):exprt(id)
  {
    operands().resize(1);
    op0().id(ID_unknown);
  }

  inline external_value_set_exprt(const typet &type, const constant_exprt& label):
    exprt("external-value-set",type)
  {
    operands().push_back(label);
  }

  inline external_value_set_exprt(const irep_idt& id, const typet &type,
                                  const constant_exprt& label):exprt(id,type)
  {
    operands().push_back(label);
  }

  inline exprt &label() { return op0(); }
  inline const exprt &label() const { return op0(); }

  inline size_t access_path_size() const { return operands().size()-1; }
  inline access_path_entry_exprt& access_path_entry(size_t index)
  {
    return to_access_path_entry(operands()[index+1]);
  }
  inline const access_path_entry_exprt& access_path_entry(size_t index) const
  {
    return to_access_path_entry(operands()[index+1]);
  }  
  inline void access_path_push_back(const access_path_entry_exprt& newentry)
  {
    copy_to_operands(newentry);
  }
  std::string get_access_path_label() const
  {
    std::string ret=id2string(to_constant_expr(label()).get_value());
    for(size_t i=0,ilim=access_path_size(); i!=ilim; ++i)
      ret+=id2string(access_path_entry(i).label());
    return ret;
  }
    
};

static inline external_value_set_exprt& to_external_value_set(exprt& e) {
  return static_cast<external_value_set_exprt&>(e);
}

static inline const external_value_set_exprt& to_external_value_set(const exprt& e) {
  return static_cast<const external_value_set_exprt&>(e);
}

// Represents the unknown initial *content* of an external value set.
// For example, "arg1->x" would be initialised to the mapping:
// external_val_set("arg1->x") -> { external_val_set_initial_content("arg1->x") }

class external_value_set_initial_content_exprt : public external_value_set_exprt
{
 public:
  inline external_value_set_initial_content_exprt():
    external_value_set_exprt("external-value-set-init") {}
  inline external_value_set_initial_content_exprt(const typet &type, const constant_exprt& label):
    external_value_set_exprt("external-value-set-init",type,label) {}
};

static inline external_value_set_initial_content_exprt&
  to_external_value_set_initial_content(exprt& e) {
  return static_cast<external_value_set_initial_content_exprt&>(e);
}

static inline const external_value_set_initial_content_exprt&
  to_external_value_set_initial_content(const exprt& e) {
  return static_cast<const external_value_set_initial_content_exprt&>(e);
}

class value_sett
{
public:
  value_sett():location_number(0)
  {
  }

  static bool field_sensitive(
    const irep_idt &id,
    const typet &type,
    const namespacet &);

  unsigned location_number;
  static object_numberingt object_numbering;

  typedef irep_idt idt;
  
  class objectt
  {
  public:
    objectt():offset_is_set(false)
    {
    }
  
    explicit objectt(const mp_integer &_offset):
      offset(_offset),
      offset_is_set(true)
    {
    }
  
    mp_integer offset;
    bool offset_is_set;
    bool offset_is_zero() const
    { return offset_is_set && offset.is_zero(); }
  };
  
  class object_map_dt:public std::map<unsigned, objectt>
  {
  public:
    object_map_dt() {}
    const static object_map_dt blank;
  };
  
  exprt to_expr(object_map_dt::const_iterator it) const;
  
  typedef reference_counting<object_map_dt> object_mapt;
  
  void set(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    dest.write()[it->first]=it->second;
  }

  bool insert(object_mapt &dest, object_map_dt::const_iterator it) const
  {
    return insert(dest, it->first, it->second);
  }

  bool insert(object_mapt &dest, const exprt &src) const
  {
    return insert(dest, object_numbering.number(src), objectt());
  }
  
  bool insert(object_mapt &dest, const exprt &src, const mp_integer &offset) const
  {
    return insert(dest, object_numbering.number(src), objectt(offset));
  }
  
  bool insert(object_mapt &dest, unsigned n, const objectt &object) const;
  
  bool insert(object_mapt &dest, const exprt &expr, const objectt &object) const
  {
    return insert(dest, object_numbering.number(expr), object);
  }
  
  struct entryt
  {
    object_mapt object_map;
    idt identifier;
    std::string suffix;
    
    entryt()
    {
    }
    
    entryt(const idt &_identifier, const std::string &_suffix):
      identifier(_identifier),
      suffix(_suffix)
    {
    }
  };
  
  typedef std::set<exprt> expr_sett;

  #ifdef USE_DSTRING   
  typedef std::map<idt, entryt> valuest;
  #else
  typedef hash_map_cont<idt, entryt, string_hash> valuest;
  #endif

  void get_value_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  expr_sett &get(
    const idt &identifier,
    const std::string &suffix);

  void make_any()
  {
    values.clear();
  }
  
  void clear()
  {
    values.clear();
  }
  
  entryt &get_entry(
    const entryt &e, const typet &type,
    const namespacet &);
  
  void output(
    const namespacet &ns,
    std::ostream &out) const;
    
  valuest values;
  
  // true = added s.th. new
  bool make_union(object_mapt &dest, const object_mapt &src) const;

  // true = added s.th. new
  bool make_union(const valuest &new_values);

  // true = added s.th. new
  bool make_union(const value_sett &new_values)
  {
    return make_union(new_values.values);
  }
  
  void guard(
    const exprt &expr,
    const namespacet &ns);
  
  void apply_code(
    const codet &code,
    const namespacet &ns);

  void assign(
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    bool is_simplified,
    bool add_to_sets);

  void do_function_call(
    const irep_idt &function,
    const exprt::operandst &arguments,
    const namespacet &ns);

  // edge back to call site
  void do_end_function(
    const exprt &lhs,
    const namespacet &ns);

  void get_reference_set(
    const exprt &expr,
    value_setst::valuest &dest,
    const namespacet &ns) const;

  bool eval_pointer_offset(
    exprt &expr,
    const namespacet &ns) const;

protected:
  void get_value_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const std::string &suffix,
    const typet &original_type,
    const namespacet &ns) const;

  void get_value_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns,
    bool is_simplified) const;

  void get_reference_set(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const
  {
    get_reference_set_rec(expr, dest, ns);
  }

  void get_reference_set_rec(
    const exprt &expr,
    object_mapt &dest,
    const namespacet &ns) const;

  void dereference_rec(
    const exprt &src,
    exprt &dest) const;

  void assign_rec(
    const exprt &lhs,
    const object_mapt &values_rhs,
    const std::string &suffix,
    const namespacet &ns,
    bool add_to_sets);

  void do_free(
    const exprt &op,
    const namespacet &ns);
    
  exprt make_member(
    const exprt &src, 
    const irep_idt &component_name,
    const namespacet &ns);
};

#endif
