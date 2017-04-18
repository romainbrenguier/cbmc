/*******************************************************************\

Module: Java_string_libraries_preprocess, gives code for methods on
        strings of the java standard library. In particular methods
        from java.lang.String, java.lang.StringBuilder,
        java.lang.StringBuffer.

Author: Romain Brenguier

Date:   April 2017

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/fresh_symbol.h>
#include <util/refined_string_type.h>
#include <util/string_expr.h>
#include "java_types.h"

#include "java_string_libraries_preprocess.h"

// Identifiers for string functions
#define ID_STRING_BUILDER_APPEND_OBJECT 0

/*******************************************************************\

Constructor: java_string_libraries_preprocesst

     Inputs:
       _symbol_table - a symbol table

    Purpose: initialize the symbol_table field and the conversion table.

\*******************************************************************/

java_string_libraries_preprocesst::java_string_libraries_preprocesst(
  symbol_tablet _symbol_table):
    symbol_table(_symbol_table)
{ }

/*******************************************************************\

Function: java_string_libraries_preprocesst::check_java_type

  Inputs: a type and a string

 Outputs: Boolean telling whether the type is a struct with the given
          tag or a symbolic type with the tag prefixed by "java::"

\*******************************************************************/

bool java_string_libraries_preprocesst::check_java_type(
  const typet &type, const std::string &tag)
{
  if(type.id()==ID_symbol)
  {
    irep_idt tag_id=to_symbol_type(type).get_identifier();
    return tag_id=="java::"+tag;
  }
  else if(type.id()==ID_struct)
  {
    irep_idt tag_id=to_struct_type(type).get_tag();
    return tag_id==tag;
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.String");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_builder_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string builder

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_builder_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuilder");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_builder_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuilder
          pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_builder_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_builder_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_buffer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java string buffer

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_buffer_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.StringBuffer");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_string_buffer_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java StringBuffer
          pointers

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_string_buffer_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_string_buffer_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_sequence_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char sequence

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_sequence_type(
  const typet &type)
{
  return check_java_type(type, "java.lang.CharSequence");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_sequence_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char sequence

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_sequence_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_char_sequence_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_array_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of java char array

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_array_type(
  const typet &type)
{
  return check_java_type(type, "array[char]");
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::is_java_char_array_pointer_type

  Inputs: a type

 Outputs: Boolean telling whether the type is that of a pointer
          to a java char array

\*******************************************************************/

bool java_string_libraries_preprocesst::is_java_char_array_pointer_type(
  const typet &type)
{
  if(type.id()==ID_pointer)
  {
    const pointer_typet &pt=to_pointer_type(type);
    const typet &subtype=pt.subtype();
    return is_java_char_array_type(subtype);
  }
  return false;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::string_data_type

  Inputs:
    symbol_table - a symbol_table containing an entry for java Strings

 Outputs: the type of data fields in java Strings.

\*******************************************************************/

typet string_data_type(symbol_tablet symbol_table)
{
  symbolt sym=symbol_table.lookup("java::java.lang.String");
  typet concrete_type=sym.type;
  // TODO: we should look at the name of the field
  typet data_type=to_struct_type(concrete_type).components()[2].type();
  return data_type;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::string_length_type

  Inputs:
    symbol_table - a symbol_table containing an entry for java Strings

 Outputs: the type of lenngth fields in java Strings.

\*******************************************************************/

typet string_length_type(symbol_tablet symbol_table)
{
  symbolt sym=symbol_table.lookup("java::java.lang.String");
  typet concrete_type=sym.type;
  // TODO: we should look at the name of the field
  typet length_type=to_struct_type(concrete_type).components()[1].type();
  return length_type;
}

/*******************************************************************\

Function: fresh_array

  Inputs:
    type - an array type
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol in the table with static lifetime and name
          containing `cprover_string_array` and given type

\*******************************************************************/

symbol_exprt java_string_libraries_preprocesst::fresh_array(
  const typet &type,
  const source_locationt &location)
{
  symbolt array_symbol=get_fresh_aux_symbol(
    type,
    "java::cprover_string_array",
    "java::cprover_string_array",
    location,
    ID_java,
    symbol_table);
  array_symbol.is_static_lifetime=true;
  return array_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::declare_function

  Inputs: a name and a type

 Purpose: declare a function with the given name and type

 TODO: duplicates goto_programs/string_refine_preprocess function

\*******************************************************************/

void java_string_libraries_preprocesst::declare_function(
  irep_idt function_name, const typet &type)
{
  auxiliary_symbolt func_symbol;
  func_symbol.base_name=function_name;
  func_symbol.is_static_lifetime=false;
  func_symbol.mode=ID_java;
  func_symbol.name=function_name;
  func_symbol.type=type;
  symbol_table.add(func_symbol);
}

/*******************************************************************\

Function: string_refine_preprocesst::process_arguments

  Inputs:
    params - a list of function parameters

 Outputs: a list of expressions

 Purpose: for each expression that is of a type implementing strings,
          we declare a new `cprover_string` whose contents is deduced
          from the expression and replace the
          expression by this cprover_string in the output list;
          in the other case the expression is kept as is for the output list.

\*******************************************************************/

exprt::operandst java_string_libraries_preprocesst::process_arguments(
  code_typet::parameterst params)
{
  exprt::operandst ops;
  for(const auto &p : params)
  {
    if(implements_java_char_sequence(p.type()))
    {
      refined_string_typet ref_type(
        string_length_type(symbol_table),
        string_data_type(symbol_table).subtype().subtype());
      symbol_exprt sym(p.get_identifier(), p.type());
      dereference_exprt deref(sym, to_pointer_type(sym.type()).subtype());
      member_exprt length(deref, "length", string_length_type(symbol_table));
      member_exprt data(deref, "data", string_data_type(symbol_table));
      string_exprt str(length, data, ref_type);
      ops.push_back(str);
    }
    else
    {
      ops.push_back(symbol_exprt(p.get_identifier(), p.type()));
    }
  }
  return ops;
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::fresh_string

  Inputs:
    type - a type for refined strings
    location - a location in the program

 Outputs: a new symbol

 Purpose: add a symbol with static lifetime and name containing
          `cprover_string` and given type

\*******************************************************************/

symbol_exprt java_string_libraries_preprocesst::fresh_string(
  const typet &type, const source_locationt &loc)
{
  symbolt string_symbol=get_fresh_aux_symbol(
    type, "java::cprover_string", "cprover_string", loc, ID_java, symbol_table);
  string_symbol.is_static_lifetime=true;
  return string_symbol.symbol_expr();
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::make_string_assign

  Inputs:
    function_type - a function type
    function_name - the name of the function
    location - a location in the program

  Output: return the following code:
          > lhs->length=function_name_length(arguments)
          > tmp_data=function_name_data(arguments)
          > lhs->data=&tmp_data
          > ....

\*******************************************************************/

codet java_string_libraries_preprocesst::make_string_assign(
  const code_typet &function_type,
  const irep_idt &function_name,
  const source_locationt &location)
{
  assert(implements_java_char_sequence(function_type.return_type()));
  code_typet::parameterst params=function_type.parameters();
  // symbol_exprt ret("java::return_tmp", params[0].type());
  // for string builder function we should assing directly the first parameter
  exprt ret=symbol_exprt(params[0].get_identifier(), params[0].type());
  exprt arg1=symbol_exprt(params[1].get_identifier(), params[1].type());
  dereference_exprt deref(ret, ret.type().subtype());
  typet length_type=string_length_type(symbol_table);
  typet data_type=string_data_type(symbol_table);

  std::string fnamel="java::"+id2string(function_name)+"_length";
  std::string fnamed="java::"+id2string(function_name)+"_data";
  declare_function(fnamel, length_type);
  declare_function(fnamed, data_type);
  function_application_exprt rhs_length(symbol_exprt(fnamel), length_type);
  function_application_exprt rhs_data(symbol_exprt(fnamed), data_type.subtype());

  exprt::operandst processed_arguments=process_arguments(params);
  rhs_length.arguments()=processed_arguments;
  rhs_data.arguments()=processed_arguments;

  symbolt sym_length=get_fresh_aux_symbol(
    length_type, "java::length", "length", location, ID_java, symbol_table);
  symbol_exprt tmp_length=sym_length.symbol_expr();
  symbol_exprt tmp_array=fresh_array(data_type.subtype(), location);

  member_exprt lhs_length(deref, "length", length_type);
  member_exprt lhs_data(deref, "data", tmp_array.type());

  refined_string_typet ref_type(length_type, data_type.subtype().subtype());
  string_exprt str(tmp_length, tmp_array, ref_type);
  symbol_exprt cprover_string_sym=fresh_string(ref_type, location);

  std::list<codet> assigns;
  assigns.push_back(code_assignt(tmp_length, rhs_length));
  assigns.push_back(code_assignt(lhs_length, tmp_length));
  assigns.push_back(code_assignt(tmp_array, rhs_data));
  assigns.push_back(code_assignt(cprover_string_sym, str));
  assigns.push_back(code_assignt(lhs_data, address_of_exprt(tmp_array)));
  assigns.push_back(code_returnt(ret));
  return code_blockt(assigns);
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::replace_string_call

  Inputs:
    code - the code of a function call

 Outputs: code for the StringBuilder.append(Object) function

\*******************************************************************/

codet java_string_libraries_preprocesst::make_string_builder_append_object_code(
  const code_typet &type, const source_locationt &loc)
{
  return make_string_assign(type, ID_cprover_string_concat_func, loc);
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::replace_string_call

  Inputs:
    code - the code of a function call

 Outputs: code for the body of the String functions if they are part
          of the supported String functions nil_exprt otherwise.

\*******************************************************************/

exprt java_string_libraries_preprocesst::code_of_function(
  const irep_idt &function_id,
  const code_typet &type,
  const source_locationt &loc)
{
  auto it=conversion_table.find(function_id);
  if(it!=conversion_table.end())
  {
    switch(it->second)
    {
    case ID_STRING_BUILDER_APPEND_OBJECT:
      return make_string_builder_append_object_code(type, loc);
    }
  }

  return nil_exprt();
}

/*******************************************************************\

Function: java_string_libraries_preprocesst::initialize_conversion_table

 Purpose: fill maps with correspondance from java method names to
          conversion functions

\*******************************************************************/

void java_string_libraries_preprocesst::initialize_conversion_table()
{
  conversion_table["java::java.lang.StringBuilder.append:"
                   "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"]=
    ID_STRING_BUILDER_APPEND_OBJECT;
}
