/*******************************************************************\

Module: JAVA Bytecode Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifdef DEBUG
#include <iostream>
#endif

#include <util/std_expr.h>
#include <util/expanding_vector.h>
#include <util/string2int.h>
#include <util/i2string.h>
#include <util/prefix.h>
#include <util/arith_tools.h>
#include <util/ieee_float.h>
#include <util/expr_util.h>

#include <goto-programs/cfg.h>
#include <goto-programs/class_hierarchy.h>
#include <analyses/cfg_dominators.h>

#include "java_bytecode_convert_method.h"
#include "java_bytecode_convert_method_class.h"
#include "bytecode_info.h"
#include "java_types.h"
#include "java_opaque_method_stubs.h"

#include <limits>
#include <algorithm>
#include <functional>
#include <unordered_set>

namespace {
class patternt
{
public:
  explicit inline patternt(const char *_p):p(_p)
  {
  }

  // match with '?'  
  friend bool operator==(const irep_idt &what, const patternt &pattern)
  {
    for(std::size_t i=0; i<what.size(); i++)
      if(pattern.p[i]==0)
        return false;
      else if(pattern.p[i]!='?' && pattern.p[i]!=what[i])
        return false;

    return pattern.p[what.size()]==0;
  }

protected:
  const char *p;
};

const size_t SLOTS_PER_INTEGER(1u);
const size_t INTEGER_WIDTH(64u);
size_t count_slots(const size_t value, const code_typet::parametert &param)
{
  const std::size_t width(param.type().get_unsigned_int(ID_width));
  return value + SLOTS_PER_INTEGER + width / INTEGER_WIDTH;
}

size_t get_variable_slots(const code_typet::parametert &param)
{
  return count_slots(0, param);
}

bool is_constructor(const class_typet::methodt &method)
{
  const std::string &name(id2string(method.get_name()));
  const std::string::size_type &npos(std::string::npos);
  return npos != name.find("<init>") || npos != name.find("<clinit>");
}

void cast_if_necessary(binary_relation_exprt &condition)
{
  exprt &lhs(condition.lhs());
  exprt &rhs(condition.rhs());
  const typet &lhs_type(lhs.type());
  if(lhs_type == rhs.type()) return;
  rhs = typecast_exprt(rhs, lhs_type);
}
}

java_bytecode_convert_methodt::java_bytecode_convert_methodt(
  symbol_tablet &_symbol_table,
  message_handlert &_message_handler,
  const bool &_disable_runtime_checks,
  int _max_array_length,
  std::vector<irep_idt>& _needed_methods,
  std::set<irep_idt>& _needed_classes,  
  const class_hierarchyt& _ch) :
  messaget(_message_handler),
  symbol_table(_symbol_table),
  disable_runtime_checks(_disable_runtime_checks),
  max_array_length(_max_array_length),
  needed_methods(_needed_methods),
  needed_classes(_needed_classes),
  class_hierarchy(_ch)
{
}

const exprt java_bytecode_convert_methodt::variable(
  const exprt &arg, char type_char, size_t address, bool do_cast)
{
  irep_idt number=to_constant_expr(arg).get_value();
    
  std::size_t number_int=safe_string2size_t(id2string(number));
  typet t=java_type_from_char(type_char);
  variablest &var_list = variables[number_int];

  // search variable in list for correct frame / address if necessary
  variablet &var = find_variable_for_slot(address, var_list);

  if(var.symbol_expr.get_identifier().empty())
  {
    // an un-named local variable
    irep_idt base_name="anonlocal::"+id2string(number)+type_char;
    irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);
      
    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, base_name);
    used_local_names.insert(result);
    return result;
  }
  else
  {
    exprt result=var.symbol_expr;
    if(do_cast && t!=result.type()) result=typecast_exprt(result, t);
    return result;
  }
}

symbol_exprt java_bytecode_convert_methodt::tmp_variable(
  const std::string &prefix, const typet &type)
{
  irep_idt base_name=prefix+"_tmp"+i2string(tmp_vars.size());
  irep_idt identifier=id2string(current_method)+"::"+id2string(base_name);

  auxiliary_symbolt tmp_symbol;
  tmp_symbol.base_name=base_name;
  tmp_symbol.is_static_lifetime=false;
  tmp_symbol.mode=ID_java;
  tmp_symbol.name=identifier;
  tmp_symbol.type=type;
  symbol_table.add(tmp_symbol);

  symbol_exprt result(identifier, type);
  result.set(ID_C_base_name, base_name);
  tmp_vars.push_back(result);

  return result;
}

irep_idt java_bytecode_convert_methodt::label(const irep_idt &address)
{
  return "pc"+id2string(address);
}

exprt::operandst java_bytecode_convert_methodt::pop(std::size_t n)
{
  if(stack.size()<n)
  {
    error() << "malformed bytecode (pop too high)" << eom;
    throw 0;
  }

  exprt::operandst operands;
  operands.resize(n);
  for(std::size_t i=0; i<n; i++)
    operands[i]=stack[stack.size()-n+i];

  stack.resize(stack.size()-n);
  return operands;
}

void java_bytecode_convert_methodt::push(const exprt::operandst &o)
{
  stack.resize(stack.size()+o.size());

  for(std::size_t i=0; i<o.size(); i++)
    stack[stack.size()-o.size()+i]=o[i];
}

void java_bytecode_convert_method_lazy(
  const symbolt& class_symbol,
  const irep_idt method_identifier,
  const java_bytecode_parse_treet::methodt &m,
  symbol_tablet& symbol_table)
{
  symbolt method_symbol;
  typet member_type=java_type_from_string(m.signature);

  method_symbol.name=method_identifier;
  method_symbol.base_name=m.base_name;
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);
  
  if(method_symbol.base_name=="<init>")
  {
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(class_symbol.base_name)+"()";
    member_type.set(ID_constructor,true);
  }
  else
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
      id2string(m.base_name)+"()";

  // do we need to add 'this' as a parameter?
  if(!m.is_static)
  {
    code_typet &code_type=to_code_type(member_type);
    code_typet::parameterst &parameters=code_type.parameters();    
    code_typet::parametert this_p;
    const reference_typet object_ref_type(symbol_typet(class_symbol.name));
    this_p.type()=object_ref_type;
    this_p.set_this();
    parameters.insert(parameters.begin(), this_p);
  }

  method_symbol.type=member_type;
  symbol_table.add(method_symbol);
}
  
/*******************************************************************\

Function: java_bytecode_convert_methodt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convert_methodt::convert(
  const symbolt &class_symbol,
  const methodt &m)
{
  //const class_typet &class_type=to_class_type(class_symbol.type);

  const irep_idt method_identifier=
    id2string(class_symbol.name)+"."+id2string(m.name)+":"+m.signature;
  method_id = method_identifier;

  const auto& old_sym=symbol_table.lookup(method_identifier);
  
  typet member_type=old_sym.type;
  code_typet &code_type=to_code_type(member_type);
  method_return_type=code_type.return_type();
  code_typet::parameterst &parameters=code_type.parameters();

  variables.clear();

  // find parameter names in the local variable table:
  for(const auto & v : m.local_variable_table)
  {
    if(v.start_pc!=0) // Local?
      continue;
    
    typet t=java_type_from_string(v.signature);
    std::ostringstream id_oss;
    id_oss << method_id << "::" << v.name;
    irep_idt identifier(id_oss.str());
    symbol_exprt result(identifier, t);
    result.set(ID_C_base_name, v.name);

    variables[v.index].push_back(variablet());
    auto& newv=variables[v.index].back();
    newv.symbol_expr = result;
    newv.start_pc = v.start_pc;
    newv.length = v.length;
  }

  // set up variables array
  for(std::size_t i=0, param_index=0;
      i < parameters.size(); ++i)
  {
    variables[param_index].resize(1);
    param_index+=get_variable_slots(parameters[i]);
  }

  // assign names to parameters
  for(std::size_t i=0, param_index=0;
      i < parameters.size(); ++i)
  {
    irep_idt base_name, identifier;

    if(i==0 && parameters[i].get_this())
    {
      base_name="this";
      identifier=id2string(method_identifier)+"::"+id2string(base_name);
      parameters[i].set_base_name(base_name);
      parameters[i].set_identifier(identifier);
    }
    else
    {
      // in the variable table?
      base_name=variables[param_index][0].symbol_expr.get(ID_C_base_name);
      identifier=variables[param_index][0].symbol_expr.get(ID_identifier);
      
      if(base_name.empty())
      {
        const typet &type=parameters[i].type();
        char suffix=java_char_from_type(type);
        base_name="arg"+i2string(param_index)+suffix;
        identifier=id2string(method_identifier)+"::"+id2string(base_name);
      }
      
      parameters[i].set_base_name(base_name);
      parameters[i].set_identifier(identifier);
    }

    // add to symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name=base_name;
    parameter_symbol.mode=ID_java;
    parameter_symbol.name=identifier;
    parameter_symbol.type=parameters[i].type();
    symbol_table.add(parameter_symbol);

    // add as a JVM variable
    std::size_t slots=get_variable_slots(parameters[i]);
    variables[param_index][0].symbol_expr=parameter_symbol.symbol_expr();
    variables[param_index][0].is_parameter=true;
    variables[param_index][0].start_pc=0;
    variables[param_index][0].length = std::numeric_limits<size_t>::max();
    param_index+=slots;
  }

  const bool is_virtual=!m.is_static && !m.is_final;

  #if 0
  class_type.methods().push_back(class_typet::methodt());
  class_typet::methodt &method=class_type.methods().back();
  #else
  class_typet::methodt method;
  #endif

  method.set_base_name(m.base_name);
  method.set_name(method_identifier);

  method.set(ID_abstract, m.is_abstract);
  method.set(ID_is_virtual, is_virtual);

  if(is_constructor(method))
    method.set(ID_constructor, true);

  method.type()=member_type;

  // we add the symbol for the method

  symbolt method_symbol;

  method_symbol.name=method.get_name();
  method_symbol.base_name=method.get_base_name();
  method_symbol.mode=ID_java;
  method_symbol.location=m.source_location;
  method_symbol.location.set_function(method_identifier);

  if(method.get_base_name()=="<init>")
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(class_symbol.base_name)+"()";
  else
    method_symbol.pretty_name=id2string(class_symbol.pretty_name)+"."+
                              id2string(method.get_base_name())+"()";

  method_symbol.type=member_type;
  if(is_constructor(method))
    method_symbol.type.set(ID_constructor,true);
  current_method=method_symbol.name;
  method_has_this=code_type.has_this();

  tmp_vars.clear();
  if(!m.is_abstract)
    method_symbol.value=convert_instructions(m, code_type);

  // Replace the existing stub symbol with the real deal:
  const auto s_it=symbol_table.symbols.find(method.get_name());
  assert(s_it!=symbol_table.symbols.end());
    symbol_table.symbols.erase(s_it); // erase, we stubbed it
    
  symbol_table.add(method_symbol);
}

/*******************************************************************\

Function: java_bytecode_convert_methodt::get_bytecode_info

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const bytecode_infot &java_bytecode_convert_methodt::get_bytecode_info(
  const irep_idt &statement)
{
  for(const bytecode_infot *p=bytecode_info; p->mnemonic!=0; p++)
    if(statement==p->mnemonic) return *p;

  error() << "failed to find bytecode mnemonic `"
          << statement << '\'' << eom;
  throw 0;
}

namespace {

irep_idt get_if_cmp_operator(const irep_idt &stmt)
{
  if(stmt == patternt("if_?cmplt")) return ID_lt;
  if(stmt == patternt("if_?cmple")) return ID_le;
  if(stmt == patternt("if_?cmpgt")) return ID_gt;
  if(stmt == patternt("if_?cmpge")) return ID_ge;
  if(stmt == patternt("if_?cmpeq")) return ID_equal;
  if(stmt == patternt("if_?cmpne")) return ID_notequal;

  throw "Unhandled java comparison instruction";
}

constant_exprt as_number(const mp_integer value, const typet &type)
{
  const std::size_t java_int_width(type.get_unsigned_int(ID_width));
  const std::string significant_bits(integer2string(value, 2));
  std::string binary_width(java_int_width - significant_bits.length(), '0');
  return constant_exprt(binary_width += significant_bits, type);
}

member_exprt to_member(const exprt &pointer, const exprt &fieldref)
{
  symbol_typet class_type(fieldref.get(ID_class));

  exprt pointer2=
    typecast_exprt(pointer, pointer_typet(class_type));
    
  const dereference_exprt obj_deref(pointer2, class_type);

  return member_exprt(
    obj_deref, fieldref.get(ID_component_name), fieldref.type());
}

codet get_array_bounds_check(const exprt &arraystruct, const exprt &idx, const source_locationt& original_sloc)
{
  constant_exprt intzero=as_number(0,java_int_type());
  binary_relation_exprt gezero(idx,ID_ge,intzero);
  const member_exprt length_field(
    arraystruct, "length", java_int_type());
  binary_relation_exprt ltlength(idx,ID_lt,length_field);
  code_blockt boundschecks;
  boundschecks.add(code_assertt(gezero));
  boundschecks.operands().back().add_source_location()=original_sloc;  
  boundschecks.operands().back().add_source_location().set_comment("Array index < 0");
  boundschecks.operands().back().add_source_location().set_property_class("array-index-oob-low");
  boundschecks.add(code_assertt(ltlength));
  boundschecks.operands().back().add_source_location()=original_sloc;    
  boundschecks.operands().back().add_source_location().set_comment("Array index >= length");
  boundschecks.operands().back().add_source_location().set_property_class("array-index-oob-high");
  
  // TODO make this throw ArrayIndexOutOfBoundsException instead of asserting.
  return boundschecks;
}
  
}

void java_bytecode_convert_methodt::check_static_field_stub(const symbol_exprt& se,
							    const irep_idt& basename)
{
  const auto& id=se.get_identifier();
  if(symbol_table.symbols.find(id)==symbol_table.symbols.end())
  {
    // Create a stub, to be overwritten if/when the real class is loaded.
    symbolt new_symbol;
    new_symbol.is_static_lifetime=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_state_var=true;
    new_symbol.name=id;
    new_symbol.base_name=basename;
    new_symbol.type=se.type();
    new_symbol.pretty_name=new_symbol.name;
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;  
    new_symbol.value.make_nil();
    symbol_table.add(new_symbol);
  }
}

symbol_exprt check_stub_function(
  symbol_tablet& symbol_table,
  const irep_idt& symname,
  const irep_idt& basename,
  const irep_idt& prettyname,
  const typet& fntype)
{
  auto findit=symbol_table.symbols.find(symname);
  if(findit==symbol_table.symbols.end())
  {
    // no, create stub
    symbolt symbol;
    symbol.name=symname;
    symbol.base_name=basename;
    // XXX: Are all Java class names prefixed java::?
    symbol.pretty_name=prettyname;
    symbol.type=fntype;
    symbol.value.make_nil();
    symbol.mode=ID_java;
        
    assign_parameter_names(to_code_type(symbol.type),symbol.name,symbol_table);
        
    symbol_table.add(symbol);
    return symbol.symbol_expr();  
  }
  return findit->second.symbol_expr();
}
  
void replace_goto_target(codet& repl, const irep_idt& old_label, const irep_idt& new_label)
{
  const auto& stmt=repl.get_statement();
  if(stmt==ID_goto)
  {
    auto& g=to_code_goto(repl);
    if(g.get_destination()==old_label)
      g.set_destination(new_label);
  }
  else {
    for(auto& op : repl.operands())
      if(op.id()==ID_code)
        replace_goto_target(to_code(op),old_label,new_label);
  }
}

code_blockt& java_bytecode_convert_methodt::get_block_for_pcrange(
  struct block_tree_node& tree, code_blockt& this_block,
  unsigned address_start, unsigned address_limit,
  unsigned next_block_start_address)
{
  address_mapt dummy;
  return get_or_create_block_for_pcrange(tree,this_block,address_start,address_limit,
                                         next_block_start_address,dummy,false);
}

code_blockt& java_bytecode_convert_methodt::get_or_create_block_for_pcrange(
  struct block_tree_node& tree, code_blockt& this_block,
  unsigned address_start, unsigned address_limit,
  unsigned next_block_start_address,
  const address_mapt& amap,
  bool allow_merge)
{
  assert(tree.branch.size()==tree.branch_addresses.size());
  if(tree.leaf)
    return this_block;
  assert(tree.branch.size()!=0);
  const auto afterstart=
    std::upper_bound(tree.branch_addresses.begin(),tree.branch_addresses.end(),address_start);
  assert(afterstart!=tree.branch_addresses.begin());
  auto findstart=afterstart;
  --findstart;
  auto child_offset=std::distance(tree.branch_addresses.begin(),findstart);
  auto findlim=
    std::lower_bound(tree.branch_addresses.begin(),tree.branch_addresses.end(),address_limit);
  unsigned findlim_block_start_address=
    findlim==tree.branch_addresses.end() ?
    next_block_start_address :
    (*findlim);

  if(findstart==tree.branch_addresses.begin() && findlim==tree.branch_addresses.end())
    return this_block;

  auto child_iter=this_block.operands().begin();
  while(child_iter!=this_block.operands().end() && to_code(*child_iter).get_statement()==ID_decl)
    ++child_iter;
  assert(child_iter!=this_block.operands().end());
  std::advance(child_iter,child_offset);
  assert(child_iter!=this_block.operands().end());  
  auto& child_label=to_code_label(to_code(*child_iter));
  auto& child_block=to_code_block(child_label.code());
      
  bool single_child=afterstart==findlim;
  if(single_child)
  {
    // Range wholly contained within a child block
    return get_or_create_block_for_pcrange(tree.branch[child_offset],child_block,
                                           address_start,address_limit,
                                           findlim_block_start_address,amap,
                                           allow_merge);
  }

  // Otherwise we're being asked for a range of subblocks, but not all of them.
  // If it's legal to draw a new lexical scope around the requested subset, do so;
  // otherwise just return this block.

  // This can be a new lexical scope if all incoming edges target the new block header,
  // or come from within the suggested new block.

  if(!allow_merge)
    return this_block;

  auto checkit=amap.find(*findstart);
  assert(checkit!=amap.end());
  ++checkit; // Skip the header, which can have incoming edges from outside.
  for(; checkit!=amap.end() && checkit->first < findlim_block_start_address; ++checkit)
  {
    for(auto p : checkit->second.predecessors)
    {
      if(p<(*findstart) || p>=findlim_block_start_address)
      {
        warning() << "Warning: refusing to create lexical block spanning " <<
          (*findstart) << "-" << findlim_block_start_address << " due to incoming edge " <<
          p << " -> " << checkit->first << "\n";
        return this_block;
      }
    }
  }

  // All incoming edges are acceptable! Create a new block wrapping the relevant children.
  // Borrow the header block's label, and redirect any block-internal edges to target the inner
  // header block.

  const auto child_label_irep=child_label.get_label();
  std::string new_label_str=as_string(child_label_irep);
  new_label_str+='$';
  irep_idt new_label_irep(new_label_str);

  code_labelt newlabel(child_label_irep, code_blockt());
  code_blockt& newblock=to_code_block(newlabel.code());
  auto nblocks=std::distance(findstart,findlim);
  assert(nblocks >= 2);
  debug() << "Combining " << std::distance(findstart,findlim) << " blocks for addresses " <<
    (*findstart) << "-" << findlim_block_start_address << "\n";

  // Make a new block containing every child of interest:
  auto& this_block_children=this_block.operands();
  assert(tree.branch.size()==this_block_children.size());
  for(auto blockidx=child_offset, blocklim=child_offset+nblocks; blockidx!=blocklim; ++blockidx)
    newblock.move_to_operands(this_block_children[blockidx]);

  // Relabel the inner header:
  to_code_label(to_code(newblock.operands()[0])).set_label(new_label_irep);
  // Relabel internal gotos:
  replace_goto_target(newblock,child_label_irep,new_label_irep);

  // Remove the now-empty sibling blocks:
  auto delfirst=this_block_children.begin();
  std::advance(delfirst,child_offset+1);
  auto dellim=delfirst;
  std::advance(dellim,nblocks-1);
  this_block_children.erase(delfirst,dellim);
  this_block_children[child_offset].swap(newlabel);

  // Perform the same transformation on the index tree:
  block_tree_node newnode;
  auto branchstart=tree.branch.begin();
  std::advance(branchstart,child_offset);
  auto branchlim=branchstart;
  std::advance(branchlim,nblocks);
  for(auto branchiter=branchstart; branchiter!=branchlim; ++branchiter)
    newnode.branch.push_back(std::move(*branchiter));
  ++branchstart;
  tree.branch.erase(branchstart,branchlim);

  assert(tree.branch.size()==this_block_children.size());

  auto branchaddriter=tree.branch_addresses.begin();
  std::advance(branchaddriter,child_offset);
  auto branchaddrlim=branchaddriter;
  std::advance(branchaddrlim,nblocks);
  newnode.branch_addresses.insert(newnode.branch_addresses.begin(),
                                  branchaddriter,branchaddrlim);
  ++branchaddriter;
  tree.branch_addresses.erase(branchaddriter,branchaddrlim);

  tree.branch[child_offset]=std::move(newnode);

  assert(tree.branch.size()==tree.branch_addresses.size());

  return to_code_block(to_code_label(to_code(this_block_children[child_offset])).code());
    
}

static void gather_symbol_live_ranges(
  unsigned pc,
  const exprt& e,
  std::map<irep_idt, java_bytecode_convert_methodt::variablet>& result)
{
  if(e.id()==ID_symbol)
  {
    const auto& symexpr=to_symbol_expr(e);
    auto findit=result.insert(std::make_pair(symexpr.get_identifier(),
					     java_bytecode_convert_methodt::variablet()));
    auto& var=findit.first->second;
    if(findit.second)
    {
      var.symbol_expr=symexpr;
      var.start_pc=pc;
      var.length=1;
    }
    else
    {
      if(pc < var.start_pc)
      {
	var.length += (var.start_pc - pc);
	var.start_pc = pc;
      }
      else
      {
	var.length = std::max(var.length, (pc - var.start_pc) + 1);
      }
    }
  }
  else
    forall_operands(it,e)
      gather_symbol_live_ranges(pc,*it,result);
}

/*******************************************************************    \

Function: java_bytecode_convert_methodt::convert_instructions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static unsigned get_bytecode_type_width(const typet& ty)
{
  if(ty.id()==ID_pointer)
    return 32;
  return ty.get_unsigned_int(ID_width);
}

codet java_bytecode_convert_methodt::convert_instructions(
  const methodt &method,
  const code_typet &method_type)
{

  const instructionst& instructions=method.instructions;
  
  // Run a worklist algorithm, assuming that the bytecode has not
  // been tampered with. See "Leroy, X. (2003). Java bytecode
  // verification: algorithms and formalizations. Journal of Automated
  // Reasoning, 30(3-4), 235-269." for a more complete treatment.

  // first pass: get targets and map addresses to instructions
  
  address_mapt address_map;
  std::set<unsigned> targets;

  std::vector<unsigned> jsr_ret_targets;
  std::vector<instructionst::const_iterator> ret_instructions;

  for(instructionst::const_iterator
      i_it=instructions.begin();
      i_it!=instructions.end();
      i_it++)
  {
    std::pair<address_mapt::iterator, bool> a_entry=
      address_map.insert(std::make_pair(
          i_it->address,
          converted_instructiont(i_it, code_skipt())));
    assert(a_entry.second);
    // addresses are strictly increasing, hence we must have inserted
    // a new maximal key
    assert(a_entry.first==--address_map.end());

    if(i_it->statement!="goto" &&
       i_it->statement!="return" &&
       !(i_it->statement==patternt("?return")) &&
       i_it->statement!="athrow" &&
       i_it->statement!="jsr" &&
       i_it->statement!="jsr_w" &&
       i_it->statement!="ret")
    {
      instructionst::const_iterator next=i_it;
      if(++next!=instructions.end())
        a_entry.first->second.successors.push_back(next->address);
    }

    if(i_it->statement=="goto" ||
       i_it->statement==patternt("if_?cmp??") ||
       i_it->statement==patternt("if??") ||
       i_it->statement=="ifnonnull" ||
       i_it->statement=="ifnull" ||
       i_it->statement=="jsr" ||
       i_it->statement=="jsr_w")
    {
      assert(!i_it->args.empty());

      const unsigned target=safe_string2unsigned(
        id2string(to_constant_expr(i_it->args[0]).get_value()));
      targets.insert(target);

      a_entry.first->second.successors.push_back(target);

      if(i_it->statement=="jsr" ||
	 i_it->statement=="jsr_w")
      {
	instructionst::const_iterator next=i_it;
	assert(++next!=instructions.end() && "jsr without valid return address?");
	jsr_ret_targets.push_back(next->address);
      }
    }
    else if(i_it->statement=="tableswitch" ||
            i_it->statement=="lookupswitch")
    {
      bool is_label=true;
      for(instructiont::argst::const_iterator
          a_it=i_it->args.begin();
          a_it!=i_it->args.end();
          a_it++, is_label=!is_label)
      {
        if(is_label)
        {
          const unsigned target=safe_string2unsigned(
            id2string(to_constant_expr(*a_it).get_value()));
          targets.insert(target);
          a_entry.first->second.successors.push_back(target);
        }
      }
    }
    else if(i_it->statement=="ret")
    {
      // Finish these later, once we've seen all jsr instructions.
      ret_instructions.push_back(i_it);
    }
  }

  // Draw edges from every `ret` to every `jsr` successor.
  // Could do better with flow analysis to distinguish multiple subroutines within
  // the same function.
  for(const auto retinst : ret_instructions)
  {
    auto& a_entry=address_map.at(retinst->address);
    a_entry.successors.insert(a_entry.successors.end(),
			      jsr_ret_targets.begin(),
			      jsr_ret_targets.end());
  }

  for(address_mapt::iterator
      it=address_map.begin();
      it!=address_map.end();
      ++it)
  {
    for(unsigned s : it->second.successors)
    {
      address_mapt::iterator a_it=address_map.find(s);
      assert(a_it!=address_map.end());

      a_it->second.predecessors.insert(it->first);
    }
  }

  // Now that the control flow graph is built, set up our local variables
  // (these require the graph to determine live ranges)
  setup_local_variables(method,address_map);

  std::set<unsigned> working_set;
  bool assertion_failure = false;

  if(!instructions.empty())
    working_set.insert(instructions.front().address);

  while(!working_set.empty())
  {
    std::set<unsigned>::iterator cur=working_set.begin();
    address_mapt::iterator a_it=address_map.find(*cur);
    assert(a_it!=address_map.end());
    working_set.erase(cur);

    if(a_it->second.done) continue;
    working_set.insert(a_it->second.successors.begin(),
                       a_it->second.successors.end());

    instructionst::const_iterator i_it=a_it->second.source;
    stack.swap(a_it->second.stack);
    a_it->second.stack.clear();
    codet &c=a_it->second.code;

    assert(stack.empty() ||
           a_it->second.predecessors.size()<=1 ||
           has_prefix(stack.front().get_string(ID_C_base_name),
                      "$stack"));

    irep_idt statement=i_it->statement;
    exprt arg0=i_it->args.size()>=1?i_it->args[0]:nil_exprt();
    exprt arg1=i_it->args.size()>=2?i_it->args[1]:nil_exprt();

    const bytecode_infot &bytecode_info=get_bytecode_info(statement);

    // deal with _idx suffixes
    if(statement.size()>=2 &&
       statement[statement.size()-2]=='_' &&
       isdigit(statement[statement.size()-1]))
    {
      arg0=constant_exprt(
        std::string(id2string(statement), statement.size()-1, 1),
        integer_typet());
      statement=std::string(id2string(statement), 0, statement.size()-2);
    }
    
    exprt::operandst op=pop(bytecode_info.pop);
    exprt::operandst results;
    results.resize(bytecode_info.push, nil_exprt());
    
    if(statement=="aconst_null")
    {
      assert(results.size()==1);
      results[0]=gen_zero(java_reference_type(void_typet()));
    }
    else if(statement=="athrow")
    {
      assert(op.size()==1 && results.size()==1);
      if(!assertion_failure) 
      {
        side_effect_expr_throwt throw_expr;
        throw_expr.add_source_location()=i_it->source_location;
        throw_expr.copy_to_operands(op[0]);
        c=code_expressiont(throw_expr);
        results[0]=op[0];
      }
      else
      {
      	// TODO: this can be removed once we properly handle throw
      	// if this athrow is generated by an assertion, then skip it
        c=code_skipt();
	assertion_failure=false;
      }
    }
    else if(statement=="checkcast")
    {
      if(!disable_runtime_checks)
      {
	// checkcast throws an exception in case a cast of object
	// on stack to given type fails.
	// The stack isn't modified.
	// TODO: convert assertions to exceptions.
	assert(op.size()==1 && results.size()==1);
	binary_predicate_exprt check(op[0], "java_instanceof", arg0);
	c=code_assertt(check);
	c.add_source_location().set_comment("Dynamic cast check");
	c.add_source_location().set_property_class("bad-dynamic-cast");
      }
      else
      {
	c=code_skipt();
      }
      results[0]=op[0];
    }
    else if(statement=="invokedynamic")
    {
      // TODO: Java 8 lambdas use this.
      code_typet &code_type=to_code_type(arg0.type());
      const code_typet::parameterst &parameters(code_type.parameters());

      pop(parameters.size());

      const typet &return_type=code_type.return_type();

      if(return_type.id()!=ID_empty)
      {
        results.resize(1);
        results[0]=gen_zero(return_type);
      }
    }
    else if(statement=="invokeinterface" ||
            statement=="invokespecial" ||
            statement=="invokevirtual" ||
            statement=="invokestatic")
    {
      // Remember that this is triggered by an assertion
      if(statement=="invokespecial" && 
	 as_string(arg0.get(ID_identifier)).find("AssertionError")!=std::string::npos)
      {
	assertion_failure=true;
      }
      const bool use_this(statement != "invokestatic");
      const bool is_virtual(
        statement == "invokevirtual" || statement == "invokeinterface");
      
      code_typet &code_type=to_code_type(arg0.type());
      code_typet::parameterst &parameters(code_type.parameters());

      if(use_this)
      {
        if(parameters.empty() || !parameters[0].get_this())
        {
          irep_idt classname = arg0.get(ID_C_class);
          typet thistype = symbol_typet(classname);          
	  // Note invokespecial is used for super-method calls as well as constructors.
	  if(statement=="invokespecial")
	  {
	    if(as_string(arg0.get(ID_identifier)).find("<init>")!=std::string::npos)
	    {
	      needed_classes.insert(classname);
	      code_type.set(ID_constructor, true);
	    }
	    else
	      code_type.set("java_super_method_call", true);
	  }
          pointer_typet object_ref_type(thistype);
          code_typet::parametert this_p(object_ref_type);
          this_p.set_this();
          this_p.set_base_name("this");
          parameters.insert(parameters.begin(), this_p);
        }
      }

      code_function_callt call;

      source_locationt loc;
      loc = i_it->source_location;
      loc.set_function(method_id);
      source_locationt &dloc = loc;

      call.add_source_location()=dloc;
      call.arguments() = pop(parameters.size());

      // double-check a bit      
      if(use_this)
      {
        const exprt &this_arg=call.arguments().front();
        assert(this_arg.type().id()==ID_pointer);
      }
      
      // do some type adjustment for the arguments,
      // as Java promotes arguments
      // Also cast pointers since intermediate locals
      // can be void*.

      for(std::size_t i=0; i<parameters.size(); i++)
      {
        const typet &type=parameters[i].type();
        if(type==java_boolean_type() ||
           type==java_char_type() ||
           type==java_byte_type() ||
           type==java_short_type() ||
           type.id()==ID_pointer)
        {
          assert(i<call.arguments().size());
          if(type!=call.arguments()[i].type())
            call.arguments()[i].make_typecast(type);
        }
      }
      
      // do some type adjustment for return values

      const typet &return_type=code_type.return_type();

      if(return_type.id()!=ID_empty)
      {
        // return types are promoted in Java
        call.lhs()=tmp_variable("return", return_type);
        exprt promoted=java_bytecode_promotion(call.lhs());
        results.resize(1);
        results[0]=promoted;
      }

      assert(arg0.id()==ID_virtual_function);

      // does the function symbol exist?
      irep_idt id=arg0.get(ID_identifier);
      auto fn_basename=arg0.get(ID_C_base_name);
      auto fn_prettyname=id2string(arg0.get(ID_C_class)).substr(6) + "." +
	  id2string(fn_basename) + "()";
      auto fn_type=arg0.type();

      if(is_virtual)
      {
        // dynamic binding
        assert(use_this);
        assert(!call.arguments().empty());
        call.function()=arg0;
	// Populate needed methods later, once we know what object types can exist.
      }
      else
      {
        // static binding
        call.function()=symbol_exprt(arg0.get(ID_identifier), arg0.type());
	needed_methods.push_back(arg0.get(ID_identifier));
        check_stub_function(symbol_table,id,fn_basename,fn_prettyname,fn_type);
      }

      call.function().add_source_location()=dloc;
      c = call;
    }
    else if(statement=="return")
    {
      assert(op.empty() && results.empty());
      c=code_returnt();
    }
    else if(statement==patternt("?return"))
    {
      // Return types are promoted in java, so this might need
      // conversion.
      assert(op.size()==1 && results.empty());
      exprt r=op[0];
      if(r.type()!=method_return_type) r=typecast_exprt(r, method_return_type);
      c=code_returnt(r);
    }
    else if(statement==patternt("?astore"))
    {
      assert(op.size()==3 && results.empty());
      
      char type_char=statement[0];
      
      exprt pointer=
        typecast_exprt(op[0], java_array_type(type_char));

      const dereference_exprt deref(pointer, pointer.type().subtype());

      const member_exprt data_ptr(
        deref, "data", pointer_typet(java_type_from_char(type_char)));

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      typet element_type=data_ptr.type().subtype();
      const dereference_exprt element(data_plus_offset, element_type);

      code_blockt assert_and_put;
      if(!disable_runtime_checks)
      {
	codet bounds_check=get_array_bounds_check(deref,op[1],i_it->source_location);
	bounds_check.add_source_location()=i_it->source_location;
	assert_and_put.move_to_operands(bounds_check);
      }
      code_assignt array_put(element, op[2]);
      array_put.add_source_location()=i_it->source_location;
      assert_and_put.move_to_operands(array_put);
      c=std::move(assert_and_put);
      c.add_source_location()=i_it->source_location;
    }
    else if(statement==patternt("?store"))
    {
      // store value into some local variable
      assert(op.size()==1 && results.empty());

      exprt var=variable(arg0, statement[0], i_it->address, /*do_cast=*/false);

      exprt toassign=op[0];
      //toassign.add_source_location()=i_it->source_location;
      if('a'==statement[0] && toassign.type()!=var.type())
        toassign=typecast_exprt(toassign,var.type());

      c=code_assignt(var,toassign);
    }
    else if(statement==patternt("?aload"))
    {
      assert(op.size() == 2 && results.size() == 1);
      
      char type_char=statement[0];

      exprt pointer=
        typecast_exprt(op[0], java_array_type(type_char));

      const dereference_exprt deref(pointer, pointer.type().subtype());

      const member_exprt data_ptr(
        deref, "data", pointer_typet(java_type_from_char(type_char)));

      plus_exprt data_plus_offset(data_ptr, op[1], data_ptr.type());
      typet element_type=data_ptr.type().subtype();
      dereference_exprt element(data_plus_offset, element_type);

      if(!disable_runtime_checks)
      {
        codet bounds_check=get_array_bounds_check(deref,op[1],i_it->source_location);
        bounds_check.add_source_location()=i_it->source_location;
	c=std::move(bounds_check);
      }
      results[0]=java_bytecode_promotion(element);
    }
    else if(statement==patternt("?load"))
    {
      // load a value from a local variable
      results[0]=variable(arg0, statement[0], i_it->address);
    }
    else if(statement=="ldc" || statement=="ldc_w" ||
            statement=="ldc2" || statement=="ldc2_w")
    {
      assert(op.empty() && results.size()==1);
      
      // 1) Pushing a String causes a reference to a java.lang.String object
      // to be constructed and pushed onto the operand stack.

      // 2) Pushing an int or a float causes a primitive value to be pushed
      // onto the stack.
      
      // 3) Pushing a Class constant causes a reference to a java.lang.Class
      // to be pushed onto the operand stack
      
      if(arg0.id()==ID_java_string_literal)
      {
        // these need to be references to java.lang.String
        results[0]=arg0;
        symbol_typet string_type("java::java.lang.String");
        results[0].type()=pointer_typet(string_type);
      }
      else if(arg0.id()==ID_type)
      {
        irep_idt class_id=arg0.type().get(ID_identifier);
        symbol_typet java_lang_Class("java::java.lang.Class");
        pointer_typet classptr(java_lang_Class);
        symbol_exprt symbol_expr(id2string(class_id)+"@class_model", classptr);
        check_static_field_stub(symbol_expr,symbol_expr.get_identifier());
        results[0]=symbol_expr;
      }
      else if(arg0.id()==ID_constant)
      {
        results[0]=arg0;
      }
      else
      {
        error() << "unexpected ldc argument" << eom;
        throw 0;
      }
      
    }
    else if(statement=="goto" || statement=="goto_w")
    {
      assert(op.empty() && results.empty());
      irep_idt number=to_constant_expr(arg0).get_value();
      code_gotot code_goto(label(number));
      c=code_goto;
    }
    else if(statement=="jsr" || statement=="jsr_w")
    {
      // As 'goto', except we must also push the subroutine return address:
      assert(op.empty() && results.size()==1);
      irep_idt number=to_constant_expr(arg0).get_value();
      code_gotot code_goto(label(number));
      c=code_goto;
      results[0]=as_number(std::next(i_it)->address,pointer_typet(void_typet(),64));
    }
    else if(statement=="ret")
    {
      // Since we have a bounded target set, make life easier on our analyses
      // and write something like if(retaddr==5) goto 5; else if(retaddr==10) goto 10; ...
      assert(op.empty() && results.empty());
      code_blockt branches;
      auto retvar=variable(arg0, 'a', i_it->address);
      assert(!jsr_ret_targets.empty());
      for(size_t idx=0, idxlim=jsr_ret_targets.size(); idx!=idxlim; ++idx)
      {
	irep_idt number=i2string(jsr_ret_targets[idx]);
	code_gotot g(label(number));
	g.add_source_location()=i_it->source_location;
	g.add_source_location().set_function(method_id);	
	if(idx==idxlim-1)
	  branches.move_to_operands(g);
	else
        {
	  code_ifthenelset branch;
	  auto address_ptr=as_number(jsr_ret_targets[idx],pointer_typet(void_typet(),64));	  
	  branch.cond()=equal_exprt(retvar,address_ptr);
	  branch.cond().add_source_location()=i_it->source_location;
	  branch.cond().add_source_location().set_function(method_id);
	  branch.then_case()=g;
	  branch.add_source_location()=i_it->source_location;
	  branch.add_source_location().set_function(method_id);
	  branches.move_to_operands(branch);
	}
      }
      c=std::move(branches);
    }
    else if(statement=="iconst_m1")
    {
      assert(results.size()==1);
      results[0]=from_integer(-1, java_int_type());
    }
    else if(statement==patternt("?const"))
    {
      assert(results.size() == 1);

      const char type_char=statement[0];
      const bool is_double('d' == type_char);
      const bool is_float('f' == type_char);

      if(is_double || is_float)
      {
        const ieee_float_spect spec(
            is_float ?
                ieee_float_spect::single_precision() :
                ieee_float_spect::double_precision());

        ieee_floatt value(spec);
        const typet &arg_type(arg0.type());
        if(ID_integer == arg_type.id())
          value.from_integer(arg0.get_int(ID_value));
        else
          value.from_expr(to_constant_expr(arg0));

        results[0] = value.to_expr();
      }
      else
      {
        const unsigned int value(arg0.get_unsigned_int(ID_value));
        const typet type=java_type_from_char(statement[0]);
        results[0] = as_number(value, type);
      }
    }
    else if(statement==patternt("?ipush"))
    {
      assert(results.size()==1);
      results[0]=typecast_exprt(arg0, java_int_type());
    }
    else if(statement==patternt("if_?cmp??"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==2 && results.empty());

      code_ifthenelset code_branch;
      const irep_idt cmp_op=get_if_cmp_operator(statement);
      
      binary_relation_exprt condition(op[0], cmp_op, op[1]);

      cast_if_necessary(condition);
      code_branch.cond()=condition;
      code_branch.cond().add_source_location()=i_it->source_location;
      code_branch.then_case()=code_gotot(label(number));
      code_branch.then_case().add_source_location()=i_it->source_location;
      code_branch.add_source_location()=i_it->source_location;
      
      c=code_branch;
    }
    else if(statement==patternt("if??"))
    {
      const irep_idt id=
        statement=="ifeq"?ID_equal:
        statement=="ifne"?ID_notequal:
        statement=="iflt"?ID_lt:
        statement=="ifge"?ID_ge:
        statement=="ifgt"?ID_gt:
        statement=="ifle"?ID_le:
        (assert(false), "");

      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());

      code_ifthenelset code_branch;
      code_branch.cond()=binary_relation_exprt(op[0], id, gen_zero(op[0].type()));
      code_branch.cond().add_source_location()=i_it->source_location;
      code_branch.cond().add_source_location().set_function(method_id);
      code_branch.then_case()=code_gotot(label(number));
      code_branch.then_case().add_source_location()=i_it->source_location;
      code_branch.then_case().add_source_location().set_function(method_id);
      code_branch.add_source_location()=i_it->source_location;
      code_branch.add_source_location().set_function(method_id);

      c=code_branch;
    }
    else if(statement==patternt("ifnonnull"))
    {
      irep_idt number=to_constant_expr(arg0).get_value();
      assert(op.size()==1 && results.empty());
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], pointer_typet(empty_typet()));
      const exprt rhs(gen_zero(lhs.type()));
      code_branch.cond()=binary_relation_exprt(lhs, ID_notequal, rhs);
      code_branch.then_case()=code_gotot(label(number));
      code_branch.then_case().add_source_location()=i_it->source_location;
      code_branch.add_source_location()=i_it->source_location;

      c=code_branch;
    }
    else if(statement==patternt("ifnull"))
    {
      assert(op.size()==1 && results.empty());
      irep_idt number=to_constant_expr(arg0).get_value();
      code_ifthenelset code_branch;
      const typecast_exprt lhs(op[0], pointer_typet(empty_typet()));
      const exprt rhs(gen_zero(lhs.type()));
      code_branch.cond()=binary_relation_exprt(lhs, ID_equal, rhs);
      code_branch.then_case()=code_gotot(label(number));
      code_branch.then_case().add_source_location()=i_it->source_location;
      code_branch.add_source_location()=i_it->source_location;

      c=code_branch;
    }
    else if(statement=="iinc")
    {
      code_assignt code_assign;
      code_assign.lhs()=variable(arg0, 'i', i_it->address, /*do_cast=*/false);
      code_assign.rhs()=plus_exprt(variable(arg0, 'i', i_it->address),
                                   typecast_exprt(arg1, java_int_type()));
      c=code_assign;
    }
    else if(statement==patternt("?xor"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitxor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?or"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitor_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?and"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=bitand_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=shl_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?shr"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=ashr_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?ushr"))
    {
      assert(op.size()==2 && results.size()==1);
      const typet type=java_type_from_char(statement[0]);

      const std::size_t width=type.get_size_t(ID_width);
      typet target=unsignedbv_typet(width);

      const typecast_exprt lhs(op[0], target);
      const typecast_exprt rhs(op[1], target);

      results[0]=typecast_exprt(lshr_exprt(lhs, rhs),op[0].type());
    }
    else if(statement==patternt("?add"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=plus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?sub"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=minus_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?div"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=div_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?mul"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=mult_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?neg"))
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=unary_minus_exprt(op[0], op[0].type());
    }
    else if(statement==patternt("?rem"))
    {
      assert(op.size()==2 && results.size()==1);
      if(statement=="frem" || statement=="drem")
        results[0]=rem_exprt(op[0], op[1]);
      else
        results[0]=mod_exprt(op[0], op[1]);
    }
    else if(statement==patternt("?cmp"))
    {
      assert(op.size() == 2 && results.size() == 1);

      // The integer result on the stack is:
      //  0 if op[0] equals op[1]
      // -1 if op[0] is less than op[1]
      //  1 if op[0] is greater than op[1]

      const typet t=java_int_type();

      results[0]=
        if_exprt(binary_relation_exprt(op[0], ID_equal, op[1]), gen_zero(t),
        if_exprt(binary_relation_exprt(op[0], ID_gt, op[1]), from_integer(1, t),
        from_integer(-1, t)));
    }
    else if(statement==patternt("?cmp?"))
    {
      assert(op.size()==2 && results.size()==1);
      const floatbv_typet type(to_floatbv_type(java_type_from_char(statement[0])));
      const ieee_float_spect spec(type);
      const ieee_floatt nan(ieee_floatt::NaN(spec));
      const constant_exprt nan_expr(nan.to_expr());
      const int nan_value(statement[4] == 'l' ? -1 : 1);
      const typet result_type(java_int_type());
      const exprt nan_result(from_integer(nan_value, result_type));

      // (value1 == NaN || value2 == NaN) ? nan_value : value1  < value2 ? -1 : value2 < value1  1 ? 1 : 0;
      // (value1 == NaN || value2 == NaN) ? nan_value : value1 == value2 ? 0  : value1 < value2 -1 ? 1 : 0;

      results[0]=
        if_exprt(or_exprt(ieee_float_equal_exprt(nan_expr, op[0]), ieee_float_equal_exprt(nan_expr, op[1])), nan_result,
        if_exprt(ieee_float_equal_exprt(op[0], op[1]), gen_zero(result_type),
        if_exprt(binary_relation_exprt(op[0], ID_lt, op[1]), from_integer(-1, result_type), from_integer(1, result_type))));
    }
    else if(statement==patternt("?cmpl"))
    {
      assert(op.size()==2 && results.size()==1);
      results[0]=binary_relation_exprt(op[0], ID_lt, op[1]);
    }
    else if(statement=="dup")
    {
      assert(op.size()==1 && results.size()==2);
      results[0]=results[1]=op[0];
    }
    else if(statement=="dup_x1")
    {
      assert(op.size()==2 && results.size()==3);
      results[0]=op[1];
      results[1]=op[0];
      results[2]=op[1];
    }
    else if(statement=="dup_x2")
    {
      assert(op.size()==3 && results.size()==4);
      results[0]=op[2];
      results[1]=op[0];
      results[2]=op[1];
      results[3]=op[2];
    }
    // dup2* behaviour depends on the size of the operands on the
    // stack
    else if(statement=="dup2")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(2);
      else
        op=pop(1);

      results.insert(results.end(), op.begin(), op.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dup2_x1")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(3);
      else
        op=pop(2);

      results.insert(results.end(), op.begin()+1, op.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dup2_x2")
    {
      assert(!stack.empty() && results.empty());

      if(get_bytecode_type_width(stack.back().type())==32)
        op=pop(2);
      else
        op=pop(1);

      assert(!stack.empty());
      exprt::operandst op2;

      if(get_bytecode_type_width(stack.back().type())==32)
        op2=pop(2);
      else
        op2=pop(1);

      results.insert(results.end(), op.begin(), op.end());
      results.insert(results.end(), op2.begin(), op2.end());
      results.insert(results.end(), op.begin(), op.end());
    }
    else if(statement=="dconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="fconst")
    {
      assert(op.empty() && results.size()==1);
    }
    else if(statement=="getfield")
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=java_bytecode_promotion(to_member(op[0], arg0));
    }
    else if(statement=="getstatic")
    {
      assert(op.empty() && results.size()==1);
      symbol_exprt symbol_expr(arg0.type());
      const auto& fieldname=arg0.get_string(ID_component_name);
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+fieldname);
      check_static_field_stub(symbol_expr,fieldname);
      if(arg0.type().id()==ID_symbol)
	needed_classes.insert(to_symbol_type(arg0.type()).get_identifier());
      results[0]=java_bytecode_promotion(symbol_expr);

      // set $assertionDisabled to false
      if(fieldname.find("$assertionsDisabled")!=std::string::npos)
      {
        exprt e;
        e.make_false();
        c=code_assignt(symbol_expr, e);
      }

    }
    else if(statement=="putfield")
    {
      assert(op.size()==2 && results.size()==0);
      c = code_assignt(to_member(op[0], arg0), op[1]);
    }
    else if(statement=="putstatic")
    {
      assert(op.size()==1 && results.empty());
      symbol_exprt symbol_expr(arg0.type());
      const auto& fieldname=arg0.get_string(ID_component_name);
      symbol_expr.set_identifier(arg0.get_string(ID_class)+"."+fieldname);
      check_static_field_stub(symbol_expr,fieldname);
      if(arg0.type().id()==ID_symbol)
	needed_classes.insert(to_symbol_type(arg0.type()).get_identifier());      
      c=code_assignt(symbol_expr, op[0]);
    }
    else if(statement==patternt("?2?")) // i2c etc.
    {
      assert(op.size()==1 && results.size()==1);
      results[0]=typecast_exprt(op[0], java_type_from_char(statement[2]));
    }
    else if(statement=="new")
    {
      // use temporary since the stack symbol might get duplicated
      assert(op.empty() && results.size()==1);
      const pointer_typet ref_type(arg0.type());
      exprt java_new_expr=side_effect_exprt(ID_java_new, ref_type);

      if(!i_it->source_location.get_line().empty())
        java_new_expr.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable("new", ref_type);
      c=code_assignt(tmp, java_new_expr);
      results[0]=tmp;
    }
    else if(statement=="newarray" ||
            statement=="anewarray")
    {
      // the op is the array size
      assert(op.size()==1 && results.size()==1);

      char element_type;
      
      if(statement=="newarray")
      {
        irep_idt id=arg0.type().id();

        if(id==ID_bool)
          element_type='z';
        else if(id==ID_char)
          element_type='c';
        else if(id==ID_float)
          element_type='f';
        else if(id==ID_double)
          element_type='d';
        else if(id==ID_byte)
          element_type='b';
        else if(id==ID_short)
          element_type='s';
        else if(id==ID_int)
          element_type='i';
        else if(id==ID_long)
          element_type='j';
        else
          element_type='?';
      }
      else
        element_type='a';

      const pointer_typet ref_type=java_array_type(element_type);

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.copy_to_operands(op[0]);

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      code_blockt checkandcreate;
      if(!disable_runtime_checks)
      {
	// TODO make this throw NegativeArrayIndexException instead.
	constant_exprt intzero=as_number(0,java_int_type());
	binary_relation_exprt gezero(op[0],ID_ge,intzero);
	code_assertt check(gezero);
        check.add_source_location().set_comment("Array size < 0");
        check.add_source_location().set_property_class("array-create-negative-size");      
	checkandcreate.move_to_operands(check);

	if(max_array_length!=0)
	  {
	    constant_exprt size_limit=as_number(max_array_length,java_int_type());
	    binary_relation_exprt le_max_size(op[0],ID_le,size_limit);
	    code_assumet assume_le_max_size(le_max_size);
	    checkandcreate.move_to_operands(assume_le_max_size);
	  }
      }
      const exprt tmp=tmp_variable("newarray", ref_type);
      checkandcreate.copy_to_operands(code_assignt(tmp, java_new_array));
      c=std::move(checkandcreate);
      results[0]=tmp;
    }
    else if(statement=="multianewarray")
    {
      // The first argument is the type, the second argument is the number of dimensions.
      // The size of each dimension is on the stack.
      irep_idt number=to_constant_expr(arg1).get_value();
      std::size_t dimension=safe_string2size_t(id2string(number));

      op=pop(dimension);
      assert(results.size()==1);

      const pointer_typet ref_type=pointer_typet(arg0.type());

      side_effect_exprt java_new_array(ID_java_new_array, ref_type);
      java_new_array.operands()=op;

      if(!i_it->source_location.get_line().empty())
        java_new_array.add_source_location()=i_it->source_location;

      const exprt tmp=tmp_variable("newarray", ref_type);
      c=code_assignt(tmp, java_new_array);
      results[0]=tmp;
    }
    else if(statement=="arraylength")
    {
      assert(op.size()==1 && results.size()==1);

      exprt pointer=
        typecast_exprt(op[0], java_array_type(statement[0]));

      const dereference_exprt array(pointer, pointer.type().subtype());
      assert(pointer.type().subtype().id()==ID_symbol);

      const member_exprt length(array, "length", java_int_type());

      results[0]=length;
    }
    else if(statement=="tableswitch" ||
            statement=="lookupswitch")
    {
      assert(op.size()==1 && results.size()==0);

      // we turn into switch-case
      code_switcht code_switch;
      code_switch.add_source_location()=i_it->source_location;
      code_switch.value()=op[0];
      code_blockt code_block;
      code_block.add_source_location()=i_it->source_location;

      bool is_label=true;
      for(instructiont::argst::const_iterator
          a_it=i_it->args.begin();
          a_it!=i_it->args.end();
          a_it++, is_label=!is_label)
      {
        if(is_label)
        {
          code_switch_caset code_case;
          code_case.add_source_location()=i_it->source_location;

          irep_idt number=to_constant_expr(*a_it).get_value();
          code_case.code()=code_gotot(label(number));
          code_case.code().add_source_location()=i_it->source_location;
        
          if(a_it==i_it->args.begin())
            code_case.set_default();
          else
          {
            instructiont::argst::const_iterator prev=a_it;
            prev--;
            code_case.case_op()=typecast_exprt(*prev, op[0].type());
            code_case.case_op().add_source_location()=i_it->source_location;
          }
          
          code_block.add(code_case);
        }
      }
      
      code_switch.body()=code_block;
      c=code_switch;
    }
    else if(statement=="pop" || statement=="pop2")
    {
      // these are skips
      c=code_skipt();

      // pop2 removes two single-word items from the stack (e.g. two
      // integers, or an integer and an object reference) or one
      // two-word item (i.e. a double or a long).
      // http://cs.au.dk/~mis/dOvs/jvmspec/ref-pop2.html
      if(statement=="pop2" &&
         get_bytecode_type_width(op[0].type())==32)
        pop(1);
    }
    else if(statement=="instanceof")
    {
      assert(op.size()==1 && results.size()==1);

      results[0]=
        binary_predicate_exprt(op[0], "java_instanceof", arg0);
    }
    else if(statement=="monitorenter")
    {
      // becomes a function call
      code_typet type;
      type.return_type()=void_typet();
      type.parameters().resize(1);
      type.parameters()[0].type()=reference_typet(void_typet());
      auto symexpr=check_stub_function(
        symbol_table,
        "java::monitorenter",
        "monitorenter",
        "monitorenter",
        type);
      code_function_callt call;
      call.function()=symexpr;
      call.lhs().make_nil();
      call.arguments().push_back(op[0]);
      call.add_source_location()=i_it->source_location;
      c=call;
    }
    else if(statement=="monitorexit")
    {
      // becomes a function call
      code_typet type;
      type.return_type()=void_typet();
      type.parameters().resize(1);
      type.parameters()[0].type()=reference_typet(void_typet());
      auto symexpr=check_stub_function(
        symbol_table,
        "java::monitorexit",
        "monitorexit",
        "monitorexit",
        type);
      code_function_callt call;
      call.function()=symexpr;
      call.lhs().make_nil();
      call.arguments().push_back(op[0]);
      call.add_source_location()=i_it->source_location;
      c=call;
    }
    else
    {
      c=codet(statement);
      c.operands()=op;
    }
    
    if(!i_it->source_location.get_line().empty())
      c.add_source_location()=i_it->source_location;

    push(results);

    a_it->second.done=true;
    for(std::list<unsigned>::iterator
        it=a_it->second.successors.begin();
        it!=a_it->second.successors.end();
        ++it)
    {
      address_mapt::iterator a_it2=address_map.find(*it);
      assert(a_it2!=address_map.end());

      if(!stack.empty() && a_it2->second.predecessors.size()>1)
      {
        // copy into temporaries
        code_blockt more_code;

        // introduce temporaries when successor is seen for the first
        // time
        if(a_it2->second.stack.empty())
        {
          for(stackt::iterator s_it=stack.begin();
              s_it!=stack.end();
              ++s_it)
          {
            symbol_exprt lhs=tmp_variable("$stack", s_it->type());
            code_assignt a(lhs, *s_it);
            more_code.copy_to_operands(a);

            s_it->swap(lhs);
          }
        }
        else
        {
          assert(a_it2->second.stack.size()==stack.size());
          stackt::const_iterator os_it=a_it2->second.stack.begin();
          for(stackt::iterator s_it=stack.begin();
              s_it!=stack.end();
              ++s_it)
          {
            assert(has_prefix(os_it->get_string(ID_C_base_name),
                              "$stack"));
            symbol_exprt lhs=to_symbol_expr(*os_it);
            code_assignt a(lhs, *s_it);
            more_code.copy_to_operands(a);

            s_it->swap(lhs);
            ++os_it;
          }
        }

        if(results.empty())
        {
          more_code.copy_to_operands(c);
          c.swap(more_code);
        }
        else
        {
          c.make_block();
	  auto& last_statement=to_code_block(c).find_last_statement();
	  if(last_statement.get_statement()==ID_goto)
	  {
	    // Insert stack twiddling before branch:
	    last_statement.make_block();
	    last_statement.operands().insert(last_statement.operands().begin(),
					     more_code.operands().begin(),
					     more_code.operands().end());
	  }
	  else
	    forall_operands(o_it, more_code)
	      c.copy_to_operands(*o_it);
        }
      }

      a_it2->second.stack=stack;
    }
  }

  // TODO: add exception handlers from exception table
  // review successor computation of athrow!
  code_blockt code;

  // Add anonymous locals to the symtab:
  for(const auto & var : used_local_names)
  {
    auxiliary_symbolt new_symbol;
    new_symbol.name=var.get_identifier();
    new_symbol.type=var.type();
    new_symbol.base_name=var.get(ID_C_base_name);
    new_symbol.pretty_name=id2string(var.get_identifier()).substr(6, std::string::npos);
    new_symbol.mode=ID_java;
    new_symbol.is_type=false;
    symbol_table.add(new_symbol);
  }

  // Try to recover block structure as indicated in the local variable table:

  // The block tree node mirrors the block structure of root_block,
  // indexing the Java PCs where each subblock starts and ends.
  block_tree_node root;
  code_blockt root_block;

  // First create a simple flat list of basic blocks. We'll add lexical nesting
  // constructs as variable live-ranges require next.
  bool start_new_block=true;
  for(auto ait=address_map.begin(), aend=address_map.end(); ait != aend; ++ait)
  {
    const auto& it=*ait;
    const unsigned address=it.first;
    assert(it.first==it.second.source->address);
    const codet &c=it.second.code;

    if(!start_new_block)
      start_new_block=targets.find(address)!=targets.end();
    if(!start_new_block)
      start_new_block=it.second.predecessors.size()>1;
    if((!start_new_block) && it.second.predecessors.size()==1)
      start_new_block=*(it.second.predecessors.begin())!=std::prev(ait)->first;

    if(start_new_block)
    {
      code_labelt newlabel(label(i2string(address)), code_blockt());
      root_block.move_to_operands(newlabel);
      root.branch.push_back(block_tree_node::get_leaf());
      assert((root.branch_addresses.size()==0 ||
              root.branch_addresses.back()<address) &&
             "Block addresses should be unique and increasing");
      root.branch_addresses.push_back(address);
    }

    if(c.get_statement()!=ID_skip)
    {
      auto& lastlabel=to_code_label(to_code(root_block.operands().back()));
      auto& add_to_block=to_code_block(lastlabel.code());
      add_to_block.add(c);
    }
    start_new_block=it.second.successors.size()>1;
  }

  // Find out where temporaries are used: 
  std::map<irep_idt, variablet> temporary_variable_live_ranges;
  for(const auto& aentry : address_map)
    gather_symbol_live_ranges(aentry.first,aentry.second.code,temporary_variable_live_ranges);

  std::vector<const variablet*> vars_to_process;
  for(const auto& vlist : variables)
    for(const auto& v : vlist)
      vars_to_process.push_back(&v);

  for(const auto& v : tmp_vars)
    vars_to_process.push_back(&temporary_variable_live_ranges.at(v.get_identifier()));

  for(const auto& v : used_local_names)
    vars_to_process.push_back(&temporary_variable_live_ranges.at(v.get_identifier()));

  for(const auto vp : vars_to_process)
  {
    const auto& v=*vp;
    if(v.is_parameter)
      continue;
    // Merge lexical scopes as far as possible to allow us to
    // declare these variable scopes faithfully.
    // Don't insert yet, as for the time being the blocks' only
    // operands must be other blocks.
    get_or_create_block_for_pcrange(
      root,
      root_block,
      v.start_pc,
      v.start_pc+v.length,
      std::numeric_limits<unsigned>::max(),
      address_map);
  }
  for(const auto vp : vars_to_process)
  {
    const auto& v=*vp;
    if(v.is_parameter)
      continue;
    if(v.symbol_expr.get_identifier()==irep_idt())
      continue;
    auto& block=get_block_for_pcrange(
      root,
      root_block,
      v.start_pc,
      v.start_pc+v.length,
      std::numeric_limits<unsigned>::max());
    code_declt d(v.symbol_expr);
    block.operands().insert(block.operands().begin(),d);
  }

  for(auto& block : root_block.operands())
    code.move_to_operands(block);

  return code;
}

/*******************************************************************\

Function: java_bytecode_convert_method

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_convert_method(
  const symbolt &class_symbol,
  const java_bytecode_parse_treet::methodt &method,
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  const bool &disable_runtime_checks,
  int max_array_length,
  std::vector<irep_idt>& needed_methods,
  std::set<irep_idt>& needed_classes,
  const class_hierarchyt& ch)
{
  java_bytecode_convert_methodt java_bytecode_convert_method(
				symbol_table, 
				message_handler, 
				disable_runtime_checks, 
				max_array_length,
				needed_methods,
				needed_classes,
				ch);

  java_bytecode_convert_method(class_symbol, method);
}
