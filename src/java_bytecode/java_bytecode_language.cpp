/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/suffix.h>
#include <util/config.h>
#include <util/cmdline.h>
#include <util/string2int.h>

#include <goto-programs/class_hierarchy.h>

#include "java_bytecode_language.h"
#include "java_bytecode_convert_class.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_internal_additions.h"
#include "java_bytecode_typecheck.h"
#include "java_entry_point.h"
#include "java_opaque_method_stubs.h"
#include "java_bytecode_parser.h"
#include "java_class_loader.h"

#include "expr2java.h"

/*******************************************************************    \

Function: java_bytecode_languaget::get_language_options

  Inputs: Command-line options

 Outputs: None

 Purpose: Consume options that are java bytecode specific.

\*******************************************************************/

void java_bytecode_languaget::get_language_options(const cmdlinet& cmd)
{
  disable_runtime_checks=cmd.isset("disable-runtime-check");
  assume_inputs_non_null=cmd.isset("java-assume-inputs-non-null");
  if(cmd.isset("java-max-input-array-length"))
    max_nondet_array_length=safe_string2int(cmd.get_value("java-max-input-array-length"));
  if(cmd.isset("java-max-vla-length"))
    max_user_array_length=safe_string2int(cmd.get_value("java-max-vla-length"));
}

/*******************************************************************\

Function: java_bytecode_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> java_bytecode_languaget::extensions() const
{
  std::set<std::string> s;
  s.insert("class");
  s.insert("jar");
  return s;
}

/*******************************************************************\

Function: java_bytecode_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_languaget::modules_provided(std::set<std::string> &modules)
{
  // modules.insert(translation_unit(parse_path));
}

/*******************************************************************\

Function: java_bytecode_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool java_bytecode_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // there is no preprocessing!
  return true;
}
             
/*******************************************************************\

Function: java_bytecode_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  java_class_loader.set_message_handler(get_message_handler());

  // look at extension
  if(has_suffix(path, ".class"))
  {
    // override main_class
    main_class=java_class_loadert::file_to_class_name(path);
  }
  else if(has_suffix(path, ".jar"))
  {
    #ifdef HAVE_LIBZIP
    if(config.java.main_class.empty())
    {
      // Does it have a main class set in the manifest?
      jar_filet::manifestt manifest=
        java_class_loader.jar_pool(path).get_manifest();
      std::string manifest_main_class=manifest["Main-Class"];

      if(manifest_main_class!="")
        main_class=manifest_main_class;
    }
    else
      main_class=config.java.main_class;
      
    // Do we have one now?
    if(main_class.empty())
    {
      status() << "JAR file without entry point: loading it all" << eom;
      java_class_loader.load_entire_jar(path);
      for(const auto& kv : java_class_loader.jar_map.at(path).entries)
        main_jar_classes.push_back(kv.first);
    }
    else
      java_class_loader.add_jar_file(path);
    
    #else
    error() << "No support for reading JAR files" << eom;
    return true;
    #endif
  }
  else
    assert(false);

  if(!main_class.empty())
  {
    status() << "Java main class: " << main_class << eom;
    java_class_loader(main_class);
  }

  return false;
}

static irep_idt get_virtual_method_target(
  const std::set<irep_idt>& needed_classes,
  const irep_idt& call_basename,
  const irep_idt& classname,
  const symbol_tablet& symbol_table)
{
  // Program-wide, is this class ever instantiated?
  if(!needed_classes.count(classname))
    return irep_idt();
  auto methodid=id2string(classname)+"."+id2string(call_basename);
  if(symbol_table.has_symbol(methodid))
    return methodid;
  else
    return irep_idt();
}

static void get_virtual_method_targets(
  const code_function_callt& c,
  const std::set<irep_idt>& needed_classes,
  std::vector<irep_idt>& needed_methods,
  symbol_tablet& symbol_table,
  const class_hierarchyt& class_hierarchy)
{
  const auto& called_function=c.function();
  assert(called_function.id()==ID_virtual_function);
  
  const auto& call_class=called_function.get(ID_C_class);
  assert(call_class!=irep_idt());
  const auto& call_basename=called_function.get(ID_component_name);
  assert(call_basename!=irep_idt());

  auto old_size=needed_methods.size();
    
  auto child_classes=class_hierarchy.get_children_trans(call_class);
  for(const auto& child_class : child_classes)
  {
    auto child_method=get_virtual_method_target(needed_classes,call_basename,
                                                child_class,symbol_table);
    if(child_method!=irep_idt())
      needed_methods.push_back(child_method);
  }

  irep_idt parent_class_id=call_class;
  while(1)
  {
    auto parent_method=get_virtual_method_target(needed_classes,call_basename,
                                                 parent_class_id,symbol_table);
    if(parent_method!=irep_idt())
    {
      needed_methods.push_back(parent_method);
      break;
    }
    else
    {
      auto findit=class_hierarchy.class_map.find(parent_class_id);
      if(findit==class_hierarchy.class_map.end())
        break;
      else
      {
        const auto& entry=findit->second;
        if(entry.parents.size()==0)
          break;
        else
          parent_class_id=entry.parents[0];
      }
    }
  }

  if(needed_methods.size()==old_size)
  {
    // Didn't find any candidate callee. Generate a stub.
    std::string stubname=id2string(call_class)+"."+id2string(call_basename);
    check_stub_function(symbol_table,stubname,call_basename,stubname,c.function().type());
  }
  
}

static void gather_virtual_callsites(const exprt& e, std::vector<const code_function_callt*>& result)
{
  if(e.id()!=ID_code)
    return;
  const codet& c=to_code(e);
  if(c.get_statement()==ID_function_call &&
     to_code_function_call(c).function().id()==ID_virtual_function)
    result.push_back(&to_code_function_call(c));
  else
    forall_operands(it,e)
      gather_virtual_callsites(*it,result);
}

static void gather_needed_globals(const exprt& e, const symbol_tablet& symbol_table, symbol_tablet& needed)
{
  if(e.id()==ID_symbol)
  {
    const auto& sym=symbol_table.lookup(to_symbol_expr(e).get_identifier());
    if(sym.is_static_lifetime)
      needed.add(sym);
  }
  else
    forall_operands(opit,e)
      gather_needed_globals(*opit,symbol_table,needed);
}

static void gather_field_types(
  const typet& class_type,
  const namespacet& ns,
  std::set<irep_idt>& needed_classes)
{
  const auto& underlying_type=to_struct_type(ns.follow(class_type));
  for(const auto& field : underlying_type.components())
  {
    if(field.type().id()==ID_struct || field.type().id()==ID_symbol)
      gather_field_types(field.type(),ns,needed_classes);
    else if(field.type().id()==ID_pointer)
    {
      // Skip array primitive pointers, for example:
      if(field.type().subtype().id()!=ID_symbol)
	continue;
      const auto& field_classid=to_symbol_type(field.type().subtype()).get_identifier();
      if(needed_classes.insert(field_classid).second)
	gather_field_types(field.type().subtype(),ns,needed_classes);
    }
  }
}
  
static void initialise_needed_classes(
  const std::vector<irep_idt>& entry_points,
  const namespacet& ns,
  const class_hierarchyt& ch,
  std::set<irep_idt>& needed_classes)
{
  for(const auto& mname : entry_points)
  {
    const auto& symbol=ns.lookup(mname);
    const auto& mtype=to_code_type(symbol.type);
    for(const auto& param : mtype.parameters())
    {
      if(param.type().id()==ID_pointer)
      {
        const auto& param_classid=to_symbol_type(param.type().subtype()).get_identifier();
        std::vector<irep_idt> class_and_parents=ch.get_parents_trans(param_classid);
        class_and_parents.push_back(param_classid);
        for(const auto& classid : class_and_parents)
          needed_classes.insert(classid);
        gather_field_types(param.type().subtype(),ns,needed_classes);
      }
    }
  }
}

/*******************************************************************\

Function: java_bytecode_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  std::map<irep_idt, std::pair<const symbolt*, const java_bytecode_parse_treet::methodt*> >
    lazy_methods;
  
  // first convert all
  for(java_class_loadert::class_mapt::const_iterator
      c_it=java_class_loader.class_map.begin();
      c_it!=java_class_loader.class_map.end();
      c_it++)
  {
    if(c_it->second.parsed_class.name.empty())
      continue;

    debug() << "Converting class " << c_it->first << eom;

    if(java_bytecode_convert_class(
         c_it->second, 
	 disable_runtime_checks,
	 symbol_table, 
	 get_message_handler(),
	 max_user_array_length,
	 lazy_methods
	 ))
      return true;
  }

  // Now incrementally elaborate methods that are reachable from this entry point:

  // Convert-method will need this to find virtual function targets.
  class_hierarchyt ch;
  ch(symbol_table);

  std::vector<irep_idt> method_worklist1;
  std::vector<irep_idt> method_worklist2;

  auto main_function=get_main_symbol(symbol_table,main_class,get_message_handler(),true);
  if(std::get<2>(main_function))
  {
    // Failed, mark all functions in the given main class(es) reachable.
    std::vector<irep_idt> reachable_classes;
    if(!main_class.empty())
      reachable_classes.push_back(main_class);
    else
      reachable_classes=main_jar_classes;
    for(const auto& classname : reachable_classes)
    {
      const auto& methods=java_class_loader.class_map.at(classname).parsed_class.methods;
      for(const auto& method : methods)
      {
        const irep_idt methodid="java::"+id2string(classname)+"."+
          id2string(method.name)+":"+
          id2string(method.signature);
        method_worklist2.push_back(methodid);
      }
    }
  }
  else
    method_worklist2.push_back(std::get<0>(main_function).name);

  std::set<irep_idt> needed_classes;
  initialise_needed_classes(method_worklist2,namespacet(symbol_table),ch,needed_classes);

  std::set<irep_idt> methods_already_populated;
  std::vector<const code_function_callt*> virtual_callsites;

  bool any_new_methods;
  do {

    any_new_methods=false;
    while(method_worklist2.size()!=0)
    {
      std::swap(method_worklist1,method_worklist2);
      for(const auto& mname : method_worklist1)
      {
	if(!methods_already_populated.insert(mname).second)
	  continue;
	auto findit=lazy_methods.find(mname);
	if(findit==lazy_methods.end())
        {
	  debug() << "Skip " << mname << eom;
	  continue;
	}
	debug() << "Lazy methods: elaborate " << mname << eom;      
	const auto& parsed_method=findit->second;
	java_bytecode_convert_method(*parsed_method.first,*parsed_method.second,
				     symbol_table,get_message_handler(),
				     disable_runtime_checks,max_user_array_length,
				     method_worklist2,needed_classes,ch);
	gather_virtual_callsites(symbol_table.lookup(mname).value,virtual_callsites);
	any_new_methods=true;
      }
      method_worklist1.clear();
    }

    // Given the object types we now know may be created, populate more
    // possible virtual function call targets:

    debug() << "Lazy methods: add virtual method targets (" << virtual_callsites.size() <<
      " callsites)" << eom;

    for(const auto& callsite : virtual_callsites)
    {
      // This will also create a stub if a virtual callsite has no targets.
      get_virtual_method_targets(*callsite,needed_classes,method_worklist2,
				 symbol_table,ch);
    }

  } while(any_new_methods);

  // Remove symbols for methods that were declared but never used:
  symbol_tablet keep_symbols;

  for(const auto& sym : symbol_table.symbols)
  {
    if(sym.second.is_static_lifetime)
      continue;    
    if(lazy_methods.count(sym.first) && !methods_already_populated.count(sym.first))
      continue;
    if(sym.second.type.id()==ID_code)
      gather_needed_globals(sym.second.value,symbol_table,keep_symbols);
    keep_symbols.add(sym.second);
  }

  debug() << "Lazy methods: removed " << symbol_table.symbols.size() - keep_symbols.symbols.size() << " unreachable methods and globals" << eom;

  symbol_table.swap(keep_symbols);

  // now typecheck all
  if(java_bytecode_typecheck(
       symbol_table, get_message_handler()))
    return true;

  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::final(symbol_tablet &symbol_table)
{
  /*
  if(c_final(symbol_table, message_handler)) return true;
  */
  java_internal_additions(symbol_table);

  // XXX for now don't generate stubs:
  return false;
  
  std::tuple<symbolt, bool, bool> t = get_main_symbol(symbol_table, main_class, get_message_handler());
  if(std::get<2>(t))
    return std::get<1>(t);

  symbolt entry = std::get<0>(t);

  java_generate_opaque_method_stubs(symbol_table,assume_inputs_non_null,
				    max_nondet_array_length, entry.location);

  if(java_entry_point(symbol_table,main_class,get_message_handler(),
		      assume_inputs_non_null,max_nondet_array_length))
    return true;
  
  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void java_bytecode_languaget::show_parse(std::ostream &out)
{
  java_class_loader(main_class).output(out);
}

/*******************************************************************\

Function: new_java_bytecode_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_java_bytecode_language()
{
  return new java_bytecode_languaget;
}

/*******************************************************************\

Function: java_bytecode_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2java(expr, ns);
  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2java(type, ns);
  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
                         
bool java_bytecode_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  #if 0
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);
  
  // parsing

  java_bytecode_parser.clear();
  java_bytecode_parser.filename="";
  java_bytecode_parser.in=&i_preprocessed;
  java_bytecode_parser.set_message_handler(message_handler);
  java_bytecode_parser.grammar=java_bytecode_parsert::EXPRESSION;
  java_bytecode_parser.mode=java_bytecode_parsert::GCC;
  java_bytecode_scanner_init();

  bool result=java_bytecode_parser.parse();

  if(java_bytecode_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=java_bytecode_parser.parse_tree.items.front().value();
    
    result=java_bytecode_convert(expr, "", message_handler);

    // typecheck it
    if(!result)
      result=java_bytecode_typecheck(expr, message_handler, ns);
  }

  // save some memory
  java_bytecode_parser.clear();

  return result;
  #endif
  
  return true; // fail for now
}

/*******************************************************************\

Function: java_bytecode_languaget::~java_bytecode_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

java_bytecode_languaget::~java_bytecode_languaget()
{
}
