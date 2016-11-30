/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>
#include <ostream>
#include <iostream>

#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/simplify_expr_class.h>
#include <util/expr_util.h>
#include <util/base_type.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/prefix.h>
#include <util/infix.h>
#include <util/suffix.h>
#include <util/std_code.h>
#include <util/arith_tools.h>
#include <util/pointer_offset_size.h>
#include <util/cprover_prefix.h>

#include <ansi-c/c_types.h>

#ifdef DEBUG
#include <langapi/language_util.h>
#include <iostream>
#endif

#include "value_set.h"
#include "add_failed_symbols.h"
#include "external_value_set_expr.h"

const value_sett::object_map_dt value_sett::object_map_dt::blank;
object_numberingt value_sett::object_numbering;
   
/*******************************************************************\

Function: value_sett::field_sensitive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::field_sensitive(
  const irep_idt &id,
  const typet &type,
  const namespacet &ns)
{
  // we always track fields on these
  if(has_prefix(id2string(id), "value_set::dynamic_object") ||
     id=="value_set::return_value" ||
     id=="value_set::memory")
    return true;

  // otherwise it has to be a struct
  return ns.follow(type).id()==ID_struct;
}

/*******************************************************************\

Function: value_sett::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

value_sett::entryt &value_sett::get_entry(
  const entryt &e,
  const typet &type,
  const namespacet &ns)
{
  irep_idt index;

  if(field_sensitive(e.identifier, type, ns))
    index=id2string(e.identifier)+e.suffix;
  else
    index=e.identifier;

  std::pair<valuest::iterator, bool> r=
    values.insert(std::pair<idt, entryt>(index, e));

  return r.first->second;
}

/*******************************************************************\

Function: value_sett::insert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::insert(
  object_mapt &dest,
  unsigned n,
  const objectt &object) const
{
  object_map_dt::const_iterator entry=dest.read().find(n);

  if(entry==dest.read().end())
  {
    // new
    dest.write()[n]=object;
    return true;
  }
  else if(!entry->second.offset_is_set)
    return false; // no change
  else if(object.offset_is_set &&
          entry->second.offset==object.offset)
    return false; // no change
  else
  {
    dest.write()[n].offset_is_set=false;
    return true;
  }
}

/*******************************************************************\

Function: value_sett::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(valuest::const_iterator
      v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    irep_idt identifier, display_name;
    
    const entryt &e=v_it->second;
  
    if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
    {
      display_name=id2string(e.identifier)+e.suffix;
      identifier="";
    }
    else if(e.identifier=="value_set::return_value")
    {
      display_name="RETURN_VALUE"+e.suffix;
      identifier="";
    }
    else
    {
      #if 0
      const symbolt &symbol=ns.lookup(e.identifier);
      display_name=symbol.display_name()+e.suffix;
      identifier=symbol.name;
      #else
      identifier=id2string(e.identifier);
      display_name=id2string(identifier)+e.suffix;
      #endif
    }
    
    out << display_name;

    out << " = { ";

    const object_map_dt &object_map=e.object_map.read();
    
    unsigned width=0;
    
    for(object_map_dt::const_iterator
        o_it=object_map.begin();
        o_it!=object_map.end();
        o_it++)
    {
      const exprt &o=object_numbering[o_it->first];
    
      std::string result;

      if(o.id()==ID_invalid || o.id()==ID_unknown)
        result=from_expr(ns, identifier, o);
      else
      {
        result="<"+from_expr(ns, identifier, o)+", ";
      
        if(o_it->second.offset_is_set)
          result+=integer2string(o_it->second.offset)+"";
        else
          result+='*';

        if(o.type().is_nil())
          result+=", ?";
        else
          result+=", "+from_type(ns, identifier, o.type());
      
        result+='>';
      }

      out << result;

      width+=result.size();
    
      object_map_dt::const_iterator next(o_it);
      next++;

      if(next!=object_map.end())
      {
        out << ", ";
        if(width>=40) out << "\n      ";
      }
    }

    out << " } " << std::endl;
  }
}

/*******************************************************************\

Function: value_sett::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_sett::to_expr(object_map_dt::const_iterator it) const
{
  const exprt &object=object_numbering[it->first];
  
  if(object.id()==ID_invalid ||
     object.id()==ID_unknown)
    return object;

  object_descriptor_exprt od;

  od.object()=object;
  
  if(it->second.offset_is_set)
    od.offset()=from_integer(it->second.offset, index_type());

  od.type()=od.object().type();

  return od;
}

/*******************************************************************\

Function: value_sett::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::make_union(const value_sett::valuest &new_values)
{
  bool result=false;
  
  valuest::iterator v_it=values.begin();

  for(valuest::const_iterator
      it=new_values.begin();
      it!=new_values.end();
      ) // no it++
  {
    if(v_it==values.end() || it->first<v_it->first)
    {
      values.insert(v_it, *it);
      result=true;
      it++;
      continue;
    }
    else if(v_it->first<it->first)
    {
      v_it++;
      continue;
    }
    
    assert(v_it->first==it->first);

    entryt &e=v_it->second;
    const entryt &new_e=it->second;

    if(make_union(e.object_map, new_e.object_map))
      result=true;

    v_it++;
    it++;
  }
  
  return result;
}

void value_sett::make_union_adjusting_evs_types(
  object_mapt& dest,
  const object_mapt& src,
  const typet& new_evs_type) const
{
  for(const auto& num : src.read())
  {
    const auto& e=object_numbering[num.first];
    const exprt* underlying=&e;
    while(underlying->id()==ID_member)
      underlying=&underlying->op0();
    if(underlying->id()=="external-value-set")
    {
      external_value_set_exprt evse_copy=to_external_value_set(*underlying);
      evse_copy.type()=new_evs_type;
      insert(dest,evse_copy,num.second);
    }
    else
    {
      insert(dest,num.first,num.second);
    }
  }
}

/*******************************************************************\

Function: value_sett::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::make_union(object_mapt &dest, const object_mapt &src) const
{
  bool result=false;
  
  for(object_map_dt::const_iterator it=src.read().begin();
      it!=src.read().end();
      it++)
  {
    if(insert(dest, it))
      result=true;
  }
  
  return result;
}

/*******************************************************************\

Function: value_sett::eval_pointer_offset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_sett::eval_pointer_offset(
  exprt &expr,
  const namespacet &ns) const
{
  bool mod=false;

  if(expr.id()==ID_pointer_offset)
  {
    assert(expr.operands().size()==1);

    object_mapt reference_set;
    get_value_set(expr.op0(), reference_set, ns, true);

    exprt new_expr;
    mp_integer previous_offset=0;

    const object_map_dt &object_map=reference_set.read();
    for(object_map_dt::const_iterator
        it=object_map.begin();
        it!=object_map.end();
        it++)
      if(!it->second.offset_is_set)
        return false;
      else
      {
        const exprt &object=object_numbering[it->first];
        mp_integer ptr_offset=compute_pointer_offset(object, ns);

        if(ptr_offset<0)
          return false;

        ptr_offset+=it->second.offset;

        if(mod && ptr_offset!=previous_offset)
          return false;

        new_expr=from_integer(ptr_offset, index_type());
        previous_offset=ptr_offset;
        mod=true;
      }

    if(mod)
      expr.swap(new_expr);
  }
  else
  {
    Forall_operands(it, expr)
      mod=eval_pointer_offset(*it, ns) || mod;
  }

  return mod;
}

/*******************************************************************\

Function: value_sett::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::pair<value_sett::valuest::iterator,bool>
value_sett::init_external_value_set(const external_value_set_exprt& evse)
{

  const auto& apback=evse.access_path_back();
  std::string basename=evse.get_access_path_basename(apback.declared_on_type());
  std::string access_path_suffix=id2string(apback.label());
  std::string entryname=basename+access_path_suffix;
        
  entryt entry(basename,access_path_suffix,apback.declared_on_type());

  auto insert_result=values.insert(std::make_pair(irep_idt(entryname),entry));

  if(insert_result.second)
    insert(insert_result.first->second.object_map,evse);

  return insert_result;

}

void value_sett::get_value_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_value_set(expr, object_map, ns, false);
  
  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(it));

  #if 0
  for(value_setst::valuest::const_iterator it=dest.begin(); it!=dest.end(); it++)
    std::cout << "GET_VALUE_SET: " << from_expr(ns, "", *it) << std::endl;
  #endif
}

/*******************************************************************\

Function: value_sett::get_value_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_value_set(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns,
  bool is_simplified) const
{
  exprt tmp(expr);
  if(!is_simplified)
  {
    simplify_exprt s(ns);
    s.keep_identical_structs=keep_identical_structs;
    s.simplify(tmp);
  }

  get_value_set_rec(tmp, dest, "", tmp.type(), ns);
}

static const typet& type_from_suffix(
  const typet& original_type,
  const std::string& suffix,
  const namespacet& ns,
  typet& parent_type,
  std::string& suffix_without_subtypes)
{
  suffix_without_subtypes=suffix;
  const typet* ret=&original_type;
  size_t next_member=1;
  while(next_member<suffix.size())
  {
    ret=&ns.follow(*ret);
    assert(ret->id()==ID_struct || ret->id()==ID_union);
    // TODO: replace this silly string-chewing with a vector of pending members or similar.
    if(suffix[next_member]=='@')
    {
      // This path is (believed to be, supposed to be) Java-specific.
      if(has_infix(suffix,"@lock",next_member) ||
	 has_infix(suffix,"@class_identifier",next_member))
	return static_cast<const typet&>(get_nil_irep());
      // Otherwise this is the base class. Can't use the method below because it might
      // contain periods.
      const auto& subclass_comp=to_struct_union_type(*ret).components()[0];
      std::string subclass_name=id2string(subclass_comp.get_name());
      assert(has_infix(suffix,subclass_name,next_member));
      ret=&subclass_comp.type();
      next_member+=(subclass_name.size()+1);
      suffix_without_subtypes=suffix.substr(next_member-1);
    }
    else
    {
      size_t member_after=suffix.find('.',next_member);
      if(member_after==std::string::npos)
	member_after=suffix.size();
      size_t derefs=0;
      std::string member=suffix.substr(next_member,member_after-next_member);
      while(has_suffix(member,"[]"))
      {
	member.resize(member.size()-2);
	++derefs;
      }
      parent_type=*ret;
      ret=&to_struct_union_type(*ret).get_component(member).type();
      for(; derefs!=0; --derefs)
      {
	if(ret->id()==ID_pointer)
	  ret=&to_pointer_type(*ret).subtype();
	else if(ret->id()==ID_array)
	  ret=&to_array_type(*ret).subtype();
	else
	  assert(false);
      }
      next_member=member_after+1;
    }
  }
  return *ret;
}

/*******************************************************************\

Function: value_sett::get_value_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_value_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const std::string &suffix,
  const typet &original_type,
  const namespacet &ns) const
{
  #if 0
  std::cout << "GET_VALUE_SET_REC EXPR: " << from_expr(ns, "", expr) << "\n";
  std::cout << "GET_VALUE_SET_REC SUFFIX: " << suffix << std::endl;
  #endif
  
  const typet &expr_type=ns.follow(expr.type());

  if(expr.id()==ID_unknown || expr.id()==ID_invalid)
  {
    insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);

    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_array ||
           type.id()==ID_incomplete_array);
           
    get_value_set_rec(expr.op0(), dest, "[]"+suffix, original_type, ns);
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    const typet &type=ns.follow(expr.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_incomplete_struct ||
           type.id()==ID_incomplete_union);
           
    const std::string &component_name=
      expr.get_string(ID_component_name);
    
    get_value_set_rec(expr.op0(), dest,
      "."+component_name+suffix, original_type, ns);
  }
  else if(expr.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(expr).get_identifier();
    
    // is it a pointer, integer, array or struct?
    if(expr_type.id()==ID_pointer ||
       expr_type.id()==ID_signedbv ||
       expr_type.id()==ID_unsignedbv ||
       expr_type.id()==ID_struct ||
       expr_type.id()==ID_union ||
       expr_type.id()==ID_array)
    {
      // look it up
      valuest::const_iterator v_it=
        values.find(id2string(identifier)+suffix);

      // try first component name as suffix if not yet found
      if(v_it==values.end() &&
          (expr_type.id()==ID_struct ||
           expr_type.id()==ID_union))
      {
        const struct_union_typet &struct_union_type=
          to_struct_union_type(expr_type);

        const std::string first_component_name=
          struct_union_type.components().front().get_string(ID_name);

        v_it=values.find(
            id2string(identifier)+"."+first_component_name+suffix);
      }

      // not found? try without suffix
      if(v_it==values.end())
        v_it=values.find(identifier);
        
      if(v_it!=values.end())
        make_union(dest, v_it->second.object_map);
      else
        insert(dest, exprt(ID_unknown, original_type));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_value_set_rec(expr.op1(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";
      
    get_reference_set(expr.op0(), dest, ns);
  }
  else if(expr.id()==ID_dereference)
  {
    object_mapt reference_set;
    get_reference_set(expr, reference_set, ns);
    const object_map_dt &object_map=reference_set.read();
    
    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it1=object_map.begin();
          it1!=object_map.end();
          it1++)
      {
        const exprt &object=object_numbering[it1->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.id()=="reference_to")
  {
    // old stuff, will go away
    object_mapt reference_set;
    
    get_reference_set(expr, reference_set, ns);
    
    const object_map_dt &object_map=reference_set.read();
 
    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it=object_map.begin();
          it!=object_map.end();
          it++)
      {
        const exprt &object=object_numbering[it->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.is_constant())
  {
    // check if NULL
    if(expr.get(ID_value)==ID_NULL &&
       expr_type.id()==ID_pointer)
    {
      insert(dest, exprt("NULL-object", expr_type.subtype()), 0);
    }
    else if(expr_type.id()==ID_unsignedbv ||
            expr_type.id()==ID_signedbv)
    {
      // an integer constant got turned into a pointer
      insert(dest, exprt(ID_integer_address, unsigned_char_type()));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";
      
    // let's see what gets converted to what
    
    const typet &op_type=ns.follow(expr.op0().type());
    
    if(op_type.id()==ID_pointer)
    {
      // pointer-to-pointer -- we just ignore these
      object_mapt tmp;
      get_value_set_rec(expr.op0(), tmp, suffix, original_type, ns);
      // ...except to fix up the types of external objects as they pass through:      
      make_union_adjusting_evs_types(dest,tmp,expr.type().subtype());
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)
    {
      // integer-to-pointer
      
      if(expr.op0().is_zero())
        insert(dest, exprt("NULL-object", expr_type.subtype()), 0);
      else
      {
        // see if we have something for the integer
        object_mapt tmp;
                
        get_value_set_rec(expr.op0(), tmp, suffix, original_type, ns);

        if(tmp.read().size()==0)
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, unsigned_char_type()));        
        }
        else if(tmp.read().size()==1 &&
                object_numbering[tmp.read().begin()->first].id()==ID_unknown)
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, unsigned_char_type()));        
        }
        else
        {
          // use as is
          dest.write().insert(tmp.read().begin(), tmp.read().end());
        }
      }
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus)
  {
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;
    mp_integer i;
    bool i_is_set=false;

    // special case for pointer+integer

    if(expr.operands().size()==2 &&
       expr_type.id()==ID_pointer)
    {
      exprt ptr_operand;
      
      if(expr.op0().type().id()!=ID_pointer &&
         expr.op0().is_constant())
      {
        i_is_set=!to_integer(expr.op0(), i);
        ptr_operand=expr.op1();
      }
      else
      {
        i_is_set=!to_integer(expr.op1(), i);
        ptr_operand=expr.op0();
      }
        
      if(i_is_set)
      {
        i*=pointer_offset_size(ptr_operand.type().subtype(), ns);

        if(expr.id()==ID_minus) i.negate();
      }

      get_value_set_rec(
        ptr_operand, pointer_expr_set, "", ptr_operand.type(), ns);
    }
    else
    {
      // we get the points-to for all operands, even integers
      forall_operands(it, expr)
      {
        get_value_set_rec(
          *it, pointer_expr_set, "", it->type(), ns);
      }
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      objectt object=it->second;

      // adjust by offset      
      if(object.offset_is_zero() && i_is_set)
        object.offset=i;
      else
        object.offset_is_set=false;
        
      insert(dest, it->first, object);
    }
  }
  else if(expr.id()==ID_mult)
  {
    // this is to do stuff like
    // (int*)((sel*(ulong)&a)+((sel^0x1)*(ulong)&b))
    
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;

    // we get the points-to for all operands, even integers
    forall_operands(it, expr)
    {
      get_value_set_rec(
        *it, pointer_expr_set, "", it->type(), ns);
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      objectt object=it->second;

      // kill any offset
      object.offset_is_set=false;
        
      insert(dest, it->first, object);
    }
  }
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement=expr.get(ID_statement);
    
    if(statement==ID_function_call)
    {
      // these should be gone
      throw "unexpected function_call sideeffect";
    }
    else if(statement==ID_malloc)
    {
      assert(suffix=="");

      if(use_malloc_type)
        assert(expr.type().id()==ID_pointer);
      
      const typet &dynamic_type=
        use_malloc_type ?
        expr.type().subtype() :
        static_cast<const typet &>(expr.find("#type"));

      dynamic_object_exprt dynamic_object(dynamic_type);
      dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else if(statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
    {
      assert(suffix=="");
      assert(expr_type.id()==ID_pointer);

      dynamic_object_exprt dynamic_object(expr_type.subtype());
      dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_struct)
  {
    // a struct constructor, which may contain addresses
    forall_operands(it, expr)
      get_value_set_rec(*it, dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_with)
  {
    assert(expr.operands().size()==3);

    // this is the array/struct
    object_mapt tmp_map0;
    get_value_set_rec(expr.op0(), tmp_map0, suffix, original_type, ns);

    // this is the update value -- note NO SUFFIX
    object_mapt tmp_map2;
    get_value_set_rec(expr.op2(), tmp_map2, "", original_type, ns);

    if(expr_type.id()==ID_struct)
    {
      #if 0
      const object_map_dt &object_map0=tmp_map0.read();
      irep_idt component_name=expr.op1().get(ID_component_name);

      bool insert=true;

      for(object_map_dt::const_iterator
          it=object_map0.begin();
          it!=object_map0.end();
          it++)
      {
        const exprt &e=to_expr(it);

        if(e.id()==ID_member &&
           e.get(ID_component_name)==component_name)
        {
          if(insert)
          {
            dest.write().insert(tmp_map2.read().begin(), tmp_map2.read().end());
            insert=false;
          }
        }
        else
          dest.write().insert(*it);
      }
      #else
      // Should be more precise! We only want "suffix"
      make_union(dest, tmp_map0);
      make_union(dest, tmp_map2);
      #endif
    }
    else
    {
      make_union(dest, tmp_map0);
      make_union(dest, tmp_map2);
    }
  }
  else if(expr.id()==ID_array)
  {
    // an array constructur, possibly containing addresses
    forall_operands(it, expr)
      get_value_set_rec(*it, dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_array_of)
  {
    // an array constructor, possibly containing an address
    assert(expr.operands().size()==1);
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(expr);
      
    const std::string prefix=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value);

    // first try with suffix
    const std::string full_name=prefix+suffix;
  
    // look it up
    valuest::const_iterator v_it=values.find(full_name);
    
    // not found? try without suffix
    if(v_it==values.end())
      v_it=values.find(prefix);

    if(v_it==values.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
      make_union(dest, v_it->second.object_map);
  }
  else if(expr.id()=="external-value-set")
  {
    // This represents an unknown external set of pointer-typed objects.
    // It points to another external value set representing an access path;
    // if it hasn't been initialised yet, do so now.

    typet declared_on_type;
    std::string suffix_without_subtype;
    const typet& field_type=type_from_suffix(expr.type(),suffix,ns,
					     declared_on_type,suffix_without_subtype);
    if(field_type.id()==ID_pointer)
    {

      std::string access_path_suffix=
        suffix_without_subtype == "" ?
        "[]" :
        suffix_without_subtype;
      const auto& extinit=to_external_value_set(expr);
      access_path_entry_exprt newentry(access_path_suffix,function,
				       i2string(location_number),declared_on_type);
      external_value_set_exprt new_ext_set=extinit;
      new_ext_set.extend_access_path(newentry);
      new_ext_set.type()=field_type.subtype();
      
      // TODO: figure out how to do this sort of on-demand-insert
      // without such ugly const hacking:
      auto insert_result=(const_cast<value_sett*>(this))->init_external_value_set(new_ext_set);

      make_union(dest,insert_result.first->second.object_map);
      
    }
    else {
      // Deref-of-external yields a scalar type.
      insert(dest, exprt(ID_unknown, original_type));
    }
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    if(expr.operands().size()!=2)
      throw "byte_extract takes two operands";
      
    bool found=false;

    exprt op1=expr.op1();
    if(eval_pointer_offset(op1, ns))
      simplify(op1, ns);

    mp_integer op1_offset;
    const typet &op0_type=ns.follow(expr.op0().type());
    if(!to_integer(op1, op1_offset) && op0_type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(op0_type);

      for(struct_union_typet::componentst::const_iterator
          c_it=struct_type.components().begin();
          !found && c_it!=struct_type.components().end();
          c_it++)
      {
        const irep_idt &name=c_it->get_name();

        mp_integer comp_offset=member_offset(struct_type, name, ns);

        if(comp_offset>op1_offset)
          break;
        else if(comp_offset!=op1_offset)
          continue;

        found=true;

        member_exprt member(expr.op0(), name, c_it->type());
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }
    
    if(op0_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(op0_type);

      // just collect them all
      for(union_typet::componentst::const_iterator
          c_it=union_type.components().begin();
          c_it!=union_type.components().end(); c_it++)
      {
        const irep_idt &name=c_it->get_name();
        member_exprt member(expr.op0(), name, c_it->type());
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }

    if(!found)
      // we just pass through
      get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    if(expr.operands().size()!=3)
      throw "byte_update takes three operands";
      
    // we just pass through
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);
    
    // we could have checked object size to be more precise
  }
  else
  {
    #if 0
    std::cout << "WARNING: not doing " << expr.id() << std::endl;
    #endif
  }

  #if 0
  std::cout << "GET_VALUE_SET_REC RESULT:\n";
  for(object_map_dt::const_iterator
      it=dest.read().begin();
      it!=dest.read().end();
      it++)
  {
    const exprt &e=to_expr(it);
    std::cout << "  " << from_expr(ns, "", e) << "\n";
  }
  std::cout << "\n";
  #endif
}

/*******************************************************************\

Function: value_sett::dereference_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::dereference_rec(
  const exprt &src,
  exprt &dest) const
{
  // remove pointer typecasts
  if(src.id()==ID_typecast)
  {
    assert(src.type().id()==ID_pointer);

    if(src.operands().size()!=1)
      throw "typecast expects one operand";
    
    dereference_rec(src.op0(), dest);
  }
  else
    dest=src;
}

/*******************************************************************\

Function: value_sett::get_reference_set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::get_reference_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_reference_set(expr, object_map, ns);
  
  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(it));
}

/*******************************************************************\

Function: value_sett::get_reference_set_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void strip_casts(exprt& e, const namespacet& ns, const typet& target_type_raw)
{
  const auto& target_type=ns.follow(target_type_raw);
  while(true)
  {
    if(e.id()==ID_typecast)
      e=e.op0();
    else if(e.id()==ID_member)
    {
      auto& mem=to_member_expr(e);
      const auto& struct_type=to_struct_type(ns.follow(e.op0().type()));
      if(mem.get_component_name()==struct_type.components()[0].get_name())
        e=e.op0();
      else
        return;
    }
    else
      return;
    if(ns.follow(e.type())==target_type)
      return;
  }

}

void value_sett::get_reference_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns) const
{
  #if 0
  std::cout << "GET_REFERENCE_SET_REC EXPR: " << from_expr(ns, "", expr) << std::endl;
  #endif

  if(expr.id()==ID_symbol ||
     expr.id()==ID_dynamic_object ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_array)
  {
    if(expr.type().id()==ID_array &&
       expr.type().subtype().id()==ID_array)
      insert(dest, expr);
    else    
      insert(dest, expr, 0);

    return;
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";

    get_value_set_rec(expr.op0(), dest, "", expr.op0().type(), ns);

    #if 0
    for(expr_sett::const_iterator it=value_set.begin(); it!=value_set.end(); it++)
      std::cout << "VALUE_SET: " << from_expr(ns, "", *it) << std::endl;
    #endif

    return;
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";
  
    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &offset=index_expr.index();
    const typet &array_type=ns.follow(array.type());
    
    assert(array_type.id()==ID_array ||
           array_type.id()==ID_incomplete_array);
    
    object_mapt array_references;
    get_reference_set(array, array_references, ns);
        
    const object_map_dt &object_map=array_references.read();
    
    for(object_map_dt::const_iterator
        a_it=object_map.begin();
        a_it!=object_map.end();
        a_it++)
    {
      const exprt &object=object_numbering[a_it->first];

      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        index_exprt index_expr(expr.type());
        index_expr.array()=object;
        index_expr.index()=gen_zero(index_type());
        
        // adjust type?
        if(ns.follow(object.type())!=array_type)
          index_expr.make_typecast(array.type());
        
        objectt o=a_it->second;
        mp_integer i;

        if(offset.is_zero())
        {
        }
        else if(!to_integer(offset, i) &&
                o.offset_is_zero())
          o.offset=i*pointer_offset_size(array_type.subtype(), ns);
        else
          o.offset_is_set=false;
          
        insert(dest, index_expr, o);
      }
    }
    
    return;
  }
  else if(expr.id()==ID_member)
  {
    const irep_idt &component_name=expr.get(ID_component_name);

    if(expr.operands().size()!=1)
      throw "member expected to have one operand";
  
    const exprt &struct_op=expr.op0();
    
    object_mapt struct_references;
    get_reference_set(struct_op, struct_references, ns);
    
    const object_map_dt &object_map=struct_references.read();

    for(object_map_dt::const_iterator
        it=object_map.begin();
        it!=object_map.end();
        it++)
    {
      const exprt &object=object_numbering[it->first];
      
      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        objectt o=it->second;

        member_exprt member_expr(expr.type());
        member_expr.op0()=object;
        member_expr.set_component_name(component_name);
        
        // We cannot introduce a cast from scalar to non-scalar,
        // thus, we can only adjust the types of structs and unions. 
        
        const typet& final_object_type = ns.follow(object.type());
        
        if(final_object_type.id()==ID_struct ||
           final_object_type.id()==ID_union)
        {
          // adjust type?
          if(ns.follow(struct_op.type())!=final_object_type)
          {
            // Avoid an infinite loop of casting by stripping typecasts
            // and address-of-first-members first.
            strip_casts(member_expr.op0(),ns,struct_op.type());
            if(ns.follow(member_expr.op0().type())!=ns.follow(struct_op.type()))
              member_expr.op0().make_typecast(struct_op.type());
          }
          
          insert(dest, member_expr, o);       
        }
        else
          insert(dest, exprt(ID_unknown, expr.type()));
      }
    }

    return;
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_reference_set_rec(expr.op1(), dest, ns);
    get_reference_set_rec(expr.op2(), dest, ns);
    return;
  }

  insert(dest, exprt(ID_unknown, expr.type()));
}

/*******************************************************************\

Function: value_sett::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::assign(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool is_simplified,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN LHS: " << from_expr(ns, "", lhs) << std::endl;
  std::cout << "ASSIGN RHS: " << from_expr(ns, "", rhs) << std::endl;
  output(ns, std::cout);
  #endif

  const typet &type=ns.follow(lhs.type());

  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=
      to_struct_union_type(type);
      
    for(struct_union_typet::componentst::const_iterator
        c_it=struct_union_type.components().begin();
        c_it!=struct_union_type.components().end();
        c_it++)
    {
      const typet &subtype=c_it->type();
      const irep_idt &name=c_it->get(ID_name);

      // ignore methods and padding
      if(subtype.id()==ID_code ||
         c_it->get_is_padding()) continue;
    
      member_exprt lhs_member(subtype);
      lhs_member.set_component_name(name);
      lhs_member.op0()=lhs;

      exprt rhs_member;

      if(rhs.id()==ID_unknown ||
         rhs.id()==ID_invalid)
      {
        rhs_member=exprt(rhs.id(), subtype);
      }
      else
      {
        if(!base_type_eq(rhs.type(), type, ns))
          throw "value_sett::assign type mismatch: "
                "rhs.type():\n"+rhs.type().pretty()+"\n"+
                "type:\n"+type.pretty();

        rhs_member=make_member(rhs, name, ns);
      
        assign(lhs_member, rhs_member, ns, is_simplified, add_to_sets);
      }
    }
  }
  else if(type.id()==ID_array)
  {
    exprt lhs_index(ID_index, type.subtype());
    lhs_index.copy_to_operands(lhs, exprt(ID_unknown, index_type()));

    if(rhs.id()==ID_unknown ||
       rhs.id()==ID_invalid)
    {
      assign(lhs_index, exprt(rhs.id(), type.subtype()), ns, is_simplified, add_to_sets);
    }
    else
    {
      if(!base_type_eq(rhs.type(), type, ns))
        throw "value_sett::assign type mismatch: "
          "rhs.type():\n"+rhs.type().pretty()+"\n"+
          "type:\n"+type.pretty();
        
      if(rhs.id()==ID_array_of)
      {
        assert(rhs.operands().size()==1);
        assign(lhs_index, rhs.op0(), ns, is_simplified, add_to_sets);
      }
      else if(rhs.id()==ID_array ||
              rhs.id()==ID_constant)
      {
        forall_operands(o_it, rhs)
        {
          assign(lhs_index, *o_it, ns, is_simplified, add_to_sets);
          add_to_sets=true;
        }
      }
      else if(rhs.id()==ID_with)
      {
        assert(rhs.operands().size()==3);

        exprt op0_index(ID_index, type.subtype());
        op0_index.copy_to_operands(rhs.op0(), exprt(ID_unknown, index_type()));

        assign(lhs_index, op0_index, ns, is_simplified, add_to_sets);
        assign(lhs_index, rhs.op2(), ns, is_simplified, true);
      }
      else
      {
        exprt rhs_index(ID_index, type.subtype());
        rhs_index.copy_to_operands(rhs, exprt(ID_unknown, index_type()));
        assign(lhs_index, rhs_index, ns, is_simplified, true);
      }
    }
  }
  else
  {
    // basic type
    object_mapt values_rhs;
    get_value_set(rhs, values_rhs, ns, is_simplified);

    // Special case: if an ext-val-set with modified=false is written,
    // set modified=true before inserting, to represent the fact that
    // <some external>.x = <some external>.x might have a side-effect if
    // the two externals differ, and generally differentiates an
    // initialiser from an external set that has been read from somewhere
    // and then written.

    std::vector<std::pair<unsigned, exprt> > replacements;
    for(const auto& obj : values_rhs.read())
    {
      const exprt& objexpr=object_numbering[obj.first];
      if(objexpr.id()=="external-value-set")
      {
        external_value_set_exprt mod(
          to_external_value_set(objexpr).as_modified());
        replacements.push_back({obj.first,mod});
      }
    }

    for(const auto& kv : replacements)
    {
      values_rhs.write().erase(kv.first);
      insert(values_rhs,kv.second);
    }

#if 0
    // Check that external-value-set types are being properly adjusted:
    for(const auto& kv : values_rhs.read())
    {
      const auto& rhs_expr=value_sett::object_numbering[kv.first];
      if(lhs.type().id()==ID_pointer &&
         rhs_expr.id()=="external-value-set" &&
         ns.follow(rhs_expr.type())!=ns.follow(lhs.type().subtype()) &&
         rhs_expr.type()!=void_typet() &&
         lhs.type().subtype()!=void_typet())
      {
        for(const auto& kv : values_rhs.read())
        {
          const auto& rhs_expr=value_sett::object_numbering[kv.first];
          std::cout << "RHS: " << from_expr(ns,"",rhs_expr) << "\n";
        }
        assert(false);
      }
    }
#endif
    
    assign_rec(lhs, values_rhs, "", ns, add_to_sets);
    
  }
}

/*******************************************************************\

Function: value_sett::do_free

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_free(
  const exprt &op,
  const namespacet &ns)
{
  // op must be a pointer
  if(op.type().id()!=ID_pointer)
    throw "free expected to have pointer-type operand";

  // find out what it points to    
  object_mapt value_set;
  get_value_set(op, value_set, ns, false);
  
  const object_map_dt &object_map=value_set.read();
  
  // find out which *instances* interest us
  expr_sett to_mark;
  
  for(object_map_dt::const_iterator
      it=object_map.begin();
      it!=object_map.end();
      it++)
  {
    const exprt &object=object_numbering[it->first];

    if(object.id()==ID_dynamic_object)
    {
      const dynamic_object_exprt &dynamic_object=
        to_dynamic_object_expr(object);
      
      if(dynamic_object.valid().is_true())
        to_mark.insert(dynamic_object.instance());
    }
  }
  
  // mark these as 'may be invalid'
  // this, unfortunately, destroys the sharing
  for(valuest::iterator v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    object_mapt new_object_map;

    const object_map_dt &old_object_map=
      v_it->second.object_map.read();
      
    bool changed=false;
    
    for(object_map_dt::const_iterator
        o_it=old_object_map.begin();
        o_it!=old_object_map.end();
        o_it++)
    {
      const exprt &object=object_numbering[o_it->first];

      if(object.id()==ID_dynamic_object)
      {
        const exprt &instance=
          to_dynamic_object_expr(object).instance();

        if(to_mark.count(instance)==0)
          set(new_object_map, o_it);
        else
        {
          // adjust
          objectt o=o_it->second;
          exprt tmp(object);
          to_dynamic_object_expr(tmp).valid()=exprt(ID_unknown);
          insert(new_object_map, tmp, o);
          changed=true;
        }
      }
      else
        set(new_object_map, o_it);
    }
    
    if(changed)
      v_it->second.object_map=new_object_map;
  }
}

/*******************************************************************\

Function: value_sett::assign_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::assign_rec(
  const exprt &lhs,
  const object_mapt &values_rhs,
  const std::string &suffix,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
  std::cout << "ASSIGN_REC LHS: " << from_expr(ns, "", lhs) << std::endl;
  std::cout << "ASSIGN_REC LHS ID: " << lhs.id() << std::endl;
  std::cout << "ASSIGN_REC SUFFIX: " << suffix << std::endl;

  for(object_map_dt::const_iterator it=values_rhs.read().begin(); 
      it!=values_rhs.read().end(); 
      it++)
    std::cout << "ASSIGN_REC RHS: " << 
      from_expr(ns, "", object_numbering[it->first]) << std::endl;
  std::cout << std::endl;
  #endif
  
  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    typet declared_on_type;
    std::string suffix_without_subtype_ignored;
    type_from_suffix(lhs.type(),suffix,ns,declared_on_type,suffix_without_subtype_ignored);
    entryt &e=get_entry(entryt(identifier, suffix, declared_on_type), lhs.type(), ns);
    
    if(add_to_sets)
      make_union(e.object_map, values_rhs);
    else
      e.object_map=values_rhs;
  }
  else if(lhs.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(lhs);
  
    const std::string name=
      "value_set::dynamic_object"+
      dynamic_object.instance().get_string(ID_value);

    typet declared_on_type;
    std::string suffix_without_subtype_ignored;
    type_from_suffix(lhs.type(),suffix,ns,declared_on_type,suffix_without_subtype_ignored);
    entryt &e=get_entry(entryt(name, suffix, declared_on_type), lhs.type(), ns);

    make_union(e.object_map, values_rhs);
  }
  else if(lhs.id()=="external-value-set")
  {
    // Write through an opaque external value set.
    const auto& evsi=to_external_value_set(lhs);
    typet declared_on_type;
    std::string suffix_without_subtype;
    const typet& field_type=type_from_suffix(lhs.type(),suffix,ns,
					     declared_on_type,suffix_without_subtype);
    std::string access_path_suffix=
      suffix_without_subtype == "" ?
      "[]" :
      suffix_without_subtype;
    access_path_entry_exprt newentry(access_path_suffix,function,
				     i2string(location_number),declared_on_type);
    external_value_set_exprt new_ext_set=evsi;
    new_ext_set.extend_access_path(newentry);
    
    const std::string basename=new_ext_set.get_access_path_basename(declared_on_type);
    std::string entryname=basename+access_path_suffix;
    
    entryt entry(basename,access_path_suffix,declared_on_type);

    auto insert_result=const_cast<valuest&>(values).
      insert(std::make_pair(irep_idt(entryname),entry));

    auto& lhs_entry=insert_result.first->second;
    
    if(insert_result.second && field_type.id()==ID_pointer)
    {
      new_ext_set.type()=field_type.subtype();
      insert(lhs_entry.object_map,new_ext_set);
    }
  }
  else if(lhs.id()==ID_dereference)
  {
    if(lhs.operands().size()!=1)
      throw lhs.id_string()+" expected to have one operand";
      
    object_mapt reference_set;
    get_reference_set(lhs, reference_set, ns);
    
    if(reference_set.read().size()!=1)
      add_to_sets=true;
      
    for(object_map_dt::const_iterator
        it=reference_set.read().begin();
        it!=reference_set.read().end();
        it++)
    {
      const exprt &object=object_numbering[it->first];

      if(object.id()!=ID_unknown)
        assign_rec(object, values_rhs, suffix, ns, add_to_sets);
    }
  }
  else if(lhs.id()==ID_index)
  {
    if(lhs.operands().size()!=2)
      throw "index expected to have two operands";
      
    const typet &type=ns.follow(lhs.op0().type());
      
    assert(type.id()==ID_array || type.id()==ID_incomplete_array);

    assign_rec(lhs.op0(), values_rhs, "[]"+suffix, ns, true);
  }
  else if(lhs.id()==ID_member)
  {
    if(lhs.operands().size()!=1)
      throw "member expected to have one operand";
  
    const std::string &component_name=lhs.get_string(ID_component_name);

    const typet &type=ns.follow(lhs.op0().type());

    assert(type.id()==ID_struct ||
           type.id()==ID_union ||
           type.id()==ID_incomplete_struct ||
           type.id()==ID_incomplete_union);
           
    assign_rec(lhs.op0(), values_rhs, "."+component_name+suffix, ns, add_to_sets);
  }
  else if(lhs.id()=="valid_object" ||
          lhs.id()=="dynamic_size" ||
          lhs.id()=="dynamic_type" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // we ignore this here
  }
  else if(lhs.id()==ID_string_constant)
  {
    // someone writes into a string-constant
    // evil guy
  }
  else if(lhs.id()=="NULL-object")
  {
    // evil as well
  }
  else if(lhs.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(lhs);
  
    assign_rec(typecast_expr.op(), values_rhs, suffix, ns, add_to_sets);
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assert(lhs.operands().size()==2);
    assign_rec(lhs.op0(), values_rhs, suffix, ns, true);
  }
  else if(lhs.id()==ID_integer_address)
  {
    // that's like assigning into __CPROVER_memory[...],
    // which we don't track
  }
  else
    throw "assign NYI: `"+lhs.id_string()+"'";
}

/*******************************************************************\

Function: value_sett::do_function_call

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_function_call(
  const irep_idt &function,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(function);

  const code_typet &type=to_code_type(symbol.type);
  const code_typet::parameterst &parameter_types=type.parameters();

  // these first need to be assigned to dummy, temporary arguments
  // and only thereafter to the actuals, in order
  // to avoid overwriting actuals that are needed for recursive
  // calls

  for(unsigned i=0; i<arguments.size(); i++)
  {
    const std::string identifier="value_set::dummy_arg_"+i2string(i);
    exprt dummy_lhs=symbol_exprt(identifier, arguments[i].type());
    assign(dummy_lhs, arguments[i], ns, false, false);
  }

  // now assign to 'actual actuals'

  unsigned i=0;

  for(code_typet::parameterst::const_iterator
      it=parameter_types.begin();
      it!=parameter_types.end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(identifier=="") continue;

    const exprt v_expr=
      symbol_exprt("value_set::dummy_arg_"+i2string(i), it->type());
    
    exprt actual_lhs=symbol_exprt(identifier, it->type());
    assign(actual_lhs, v_expr, ns, true, true);
    i++;
  }

  // we could delete the dummy_arg_* now.
}

/*******************************************************************\

Function: value_sett::do_end_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::do_end_function(
  const exprt &lhs,
  const namespacet &ns)
{
  if(lhs.is_nil()) return;

  symbol_exprt rhs("value_set::return_value", lhs.type());

  assign(lhs, rhs, ns, false, false);
}

/*******************************************************************\

Function: value_sett::apply_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::apply_code(
  const codet &code,
  const namespacet &ns)
{
  const irep_idt &statement=code.get_statement();
  
  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code(to_code(*it), ns);
  }
  else if(statement==ID_function_call)
  {
    // shouldn't be here
    assert(false);
  }
  else if(statement==ID_assign ||
          statement==ID_init)
  {
    if(code.operands().size()!=2)
      throw "assignment expected to have two operands";

    assign(code.op0(), code.op1(), ns, false, false);
  }
  else if(statement==ID_decl)
  {
    if(code.operands().size()!=1)
      throw "decl expected to have one operand";

    const exprt &lhs=code.op0();

    if(lhs.id()!=ID_symbol)
      throw "decl expected to have symbol on lhs";
      
    const typet &lhs_type=ns.follow(lhs.type());

    if(lhs_type.id()==ID_pointer ||
       (lhs_type.id()==ID_array &&
        ns.follow(lhs_type.subtype()).id()==ID_pointer))
    {
      // assign the address of the failed object
      exprt failed=get_failed_symbol(to_symbol_expr(lhs), ns);
      
      if(failed.is_not_nil())
      {
        address_of_exprt address_of_expr;
        address_of_expr.object()=failed;
        address_of_expr.type()=lhs.type();
        assign(lhs, address_of_expr, ns, false, false);
      }
      else
        assign(lhs, exprt(ID_invalid), ns, false, false);
    }
  }
  else if(statement==ID_dead &&
	  use_dead_statements)
  {
    const exprt &lhs=code.op0();
    if(lhs.id()!=ID_symbol)
      throw "dead expected to have symbol on lhs";
      
    assign(lhs,exprt(ID_invalid),ns,true,false);
  }
  else if(statement=="specc_notify" ||
          statement=="specc_wait")
  {
    // ignore, does not change variables
  }
  else if(statement==ID_expression)
  {
    // can be ignored, we don't expect sideeffects here
  }
  else if(statement=="cpp_delete" ||
          statement=="cpp_delete[]")
  {
    // does nothing
  }
  else if(statement==ID_free)
  {
    // this may kill a valid bit

    if(code.operands().size()!=1)
      throw "free expected to have one operand";

    do_free(code.op0(), ns);
  }
  else if(statement=="lock" || statement=="unlock")
  {
    // ignore for now
  }
  else if(statement==ID_asm)
  {
    // ignore for now, probably not safe
  }
  else if(statement==ID_nondet)
  {
    // doesn't do anything
  }
  else if(statement==ID_printf)
  {
    // doesn't do anything
  }
  else if(statement==ID_return)
  {
    // this is turned into an assignment
    if(code.operands().size()==1)
    {
      symbol_exprt lhs("value_set::return_value", code.op0().type());
      assign(lhs, code.op0(), ns, false, false);
    }
  }
  else if(statement==ID_array_set)
  {
  }
  else if(statement==ID_array_copy)
  {
  }
  else if(statement==ID_assume)
  {
    guard(to_code_assume(code).op0(), ns);
  }
  else if(statement==ID_user_specified_predicate ||
          statement==ID_user_specified_parameter_predicates ||
          statement==ID_user_specified_return_predicates)
  {
    // doesn't do anything
  }
  else if(statement==ID_fence)
  {
  }
  else if(statement=="set_may" || statement=="get_may" || statement=="clear_may")
  {
  }
  else
  {
    //std::cerr << code.pretty() << std::endl;
    throw "value_sett: unexpected statement: "+id2string(statement);
  }
}

/*******************************************************************\

Function: value_sett::guard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_sett::guard(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      guard(*it, ns);
  }
  else if(expr.id()==ID_equal)
  {
  }
  else if(expr.id()==ID_notequal)
  {
  }
  else if(expr.id()==ID_not)
  {
  }
  else if(expr.id()==ID_dynamic_object)
  {
    assert(expr.operands().size()==1);

    dynamic_object_exprt dynamic_object(unsigned_char_type());
    //dynamic_object.instance()=from_integer(location_number, typet(ID_natural));
    dynamic_object.valid()=true_exprt();

    address_of_exprt address_of(dynamic_object);
    address_of.type()=expr.op0().type();

    assign(expr.op0(), address_of, ns, false, false);
  }
}

/*******************************************************************\

Function: value_sett::make_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt value_sett::make_member(
  const exprt &src,
  const irep_idt &component_name,
  const namespacet &ns)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(ns.follow(src.type()));

  if(src.id()==ID_struct ||
     src.id()==ID_constant)
  {
    unsigned no=struct_union_type.component_number(component_name);
    assert(no<src.operands().size());
    return src.operands()[no];
  }
  else if(src.id()==ID_with)
  {
    assert(src.operands().size()==3);

    // see if op1 is the member we want
    const exprt &member_operand=src.op1();

    if(component_name==member_operand.get(ID_component_name))
      // yes! just take op2
      return src.op2();
    else
      // no! do this recursively
      return make_member(src.op0(), component_name, ns);
  }
  else if(src.id()==ID_typecast)
  {
    // push through typecast
    assert(src.operands().size()==1);
    return make_member(src.op0(), component_name, ns);
  }

  // give up
  typet subtype=struct_union_type.component_type(component_name);
  member_exprt member_expr(subtype);
  member_expr.op0()=src;
  member_expr.set_component_name(component_name);

  return member_expr;
}

bool value_sett::use_malloc_type;
bool value_sett::use_dead_statements;
bool value_sett::keep_identical_structs;
