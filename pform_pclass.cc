/*
 * Copyright (c) 2012-2024 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
 */

# include  <cstdarg>
# include  "pform.h"
# include  "PClass.h"
# include  "PExpr.h"
# include  "parse_misc.h"
# include  "ivl_assert.h"

using namespace std;

/*
 * The functions here help the parser put together class type declarations.
 */
static PClass*pform_cur_class = 0;

/*
 * Track whether the current method being parsed is static.
 * Static methods don't get an implicit 'this' parameter.
 */
static bool pform_cur_method_is_static = false;

/*
 * Track whether the current method being parsed is virtual.
 * Virtual methods use dynamic dispatch at runtime.
 */
static bool pform_cur_method_is_virtual = false;

/*
 * The base_type is set to the base class if this declaration is
 * starting a derived class. For example, for the syntax:
 *
 *    class foo extends bar (exprs) ...
 *
 * the base_type is the type of the class "bar", and the base_exprs,
 * if present, are the "exprs" that would be passed to a chained
 * constructor.
 */
void pform_start_class_declaration(const struct vlltype&loc,
				   class_type_t*type,
				   data_type_t*base_type,
				   list<named_pexpr_t> *base_args,
				   list<class_spec_param_t*> *base_type_params,
				   bool virtual_class)
{
      PClass*class_scope = pform_push_class_scope(loc, type->name);
      class_scope->type = type;
      ivl_assert(loc, pform_cur_class == 0);
      pform_cur_class = class_scope;

      ivl_assert(loc, type->base_type == 0);
      type->base_type.reset(base_type);
      type->virtual_class = virtual_class;


      ivl_assert(loc, type->base_args.empty());
      if (base_args) {
	    type->base_args.insert(type->base_args.begin(), base_args->begin(),
			           base_args->end());
	    delete base_args;
      }

      // Store base class type parameters (e.g., extends uvm_driver#(my_tx))
      if (base_type_params) {
	    type->base_type_params.insert(type->base_type_params.begin(),
					  base_type_params->begin(),
					  base_type_params->end());
	    delete base_type_params;
      }

      // Inherit type parameters from base class (e.g., REQ, RSP from uvm_driver)
      // This allows using base class type parameters like REQ in property declarations.
      if (base_type) {
	    // Get the base class's class_type_t to access its type parameters
	    class_type_t *base_class_type = nullptr;

	    // If base_type is a typeref_t, extract the underlying class_type_t
	    // Also check if the typeref has spec_params attached (from ps_type_identifier rule)
	    std::list<class_spec_param_t*>* typeref_spec_params = nullptr;
	    if (typeref_t *tref = dynamic_cast<typeref_t*>(base_type)) {
		  typedef_t *td = tref->get_typedef();
		  if (td) {
			// Try to cast the underlying data_type to class_type_t
			// Note: basic_type may not be set to CLASS, so we use dynamic_cast
			base_class_type = dynamic_cast<class_type_t*>(
			    const_cast<data_type_t*>(td->get_data_type()));
		  }
		  // Check if typeref has spec_params
		  typeref_spec_params = tref->get_spec_params();
	    } else if (class_type_t *ct = dynamic_cast<class_type_t*>(base_type)) {
		  base_class_type = ct;
	    }

	    // If we found the base class and it has type parameters, register them
	    if (base_class_type && !base_class_type->parameters.empty()) {
		  // Use typeref spec params if base_type_params is empty
		  // (The ps_type_identifier rule can set spec_params on the typeref)
		  std::list<class_spec_param_t*>* effective_spec_params = nullptr;
		  if (!type->base_type_params.empty()) {
			effective_spec_params = &type->base_type_params;
		  } else if (typeref_spec_params && !typeref_spec_params->empty()) {
			effective_spec_params = typeref_spec_params;
		  }

		  // Map base class type parameters to the specialization arguments
		  std::list<class_spec_param_t*>::iterator spec_it;
		  if (effective_spec_params) {
			spec_it = effective_spec_params->begin();
		  }
		  for (class_param_t *base_param : base_class_type->parameters) {
			if (!base_param->is_type) continue;  // Only handle type parameters

			// Create a typedef for this inherited type parameter
			// If we have specialization params, use the corresponding type
			data_type_t *param_type = nullptr;
			if (effective_spec_params && spec_it != effective_spec_params->end()) {
			      class_spec_param_t *spec = *spec_it;
			      if (spec->type_param) {
				    param_type = spec->type_param;
			      }
			      ++spec_it;
			} else if (base_param->default_type) {
			      param_type = base_param->default_type;
			      // If default_type is a type_parameter_t referencing another
			      // type parameter (like RSP=REQ), look up what that param resolves to
			      if (type_parameter_t *tp = dynamic_cast<type_parameter_t*>(param_type)) {
				    // Look up the referenced type parameter in current class scope
				    LexicalScope::typedef_map_t::iterator it =
					  pform_cur_class->typedefs.find(tp->name);
				    if (it != pform_cur_class->typedefs.end()) {
					  typedef_t *ref_td = it->second;
					  if (ref_td && ref_td->get_data_type()) {
						param_type = const_cast<data_type_t*>(ref_td->get_data_type());
					  }
				    }
			      }
			}

			// Register the type parameter in the current class scope
			if (param_type) {
			      pform_set_typedef(loc, base_param->name, param_type, nullptr);
			} else {
			      // Register as type_parameter_t if no concrete type is available
			      type_parameter_t *tp = new type_parameter_t(base_param->name);
			      tp->set_lineno(loc.first_line);
			      tp->set_file(filename_strings.make(loc.text));
			      pform_set_typedef(loc, base_param->name, tp, nullptr);
			}
		  }
	    }
      }

      // Register class type parameters as types within the class scope.
      // This allows using the type parameter names as types for properties.
      for (class_param_t*param : type->parameters) {
	    // Create a vlltype from the parameter's LineInfo for FILE_NAME calls
	    struct vlltype param_loc;
	    param_loc.first_line = param->get_lineno();
	    param_loc.text = param->get_file().str();

	    if (param->is_type) {
		  // Create a type_parameter_t for this type parameter
		  type_parameter_t *tp = new type_parameter_t(param->name);
		  tp->set_lineno(param->get_lineno());
		  tp->set_file(param->get_file());
		  // Register it as a typedef in the class scope
		  pform_set_typedef(param_loc, param->name, tp, nullptr);

		  // Also register it as a parameter in the scope
		  LexicalScope::param_expr_t*parm = new LexicalScope::param_expr_t();
		  parm->set_lineno(param->get_lineno());
		  parm->set_file(param->get_file());
		  // For type parameters, create a PETypename expression from the default type
		  if (param->default_type) {
			PETypename*type_expr = new PETypename(param->default_type);
			FILE_NAME(type_expr, param_loc);
			parm->expr = type_expr;
		  } else {
			parm->expr = nullptr;
		  }
		  parm->data_type = nullptr;
		  parm->range = nullptr;
		  parm->local_flag = false;
		  parm->overridable = true;
		  parm->type_flag = true;
		  parm->lexical_pos = param->get_lineno();
		  class_scope->parameters[param->name] = parm;
	    } else {
		  // Value parameter - register as a parameter in the scope
		  LexicalScope::param_expr_t*parm = new LexicalScope::param_expr_t();
		  parm->set_lineno(param->get_lineno());
		  parm->set_file(param->get_file());
		  parm->expr = param->default_expr;
		  parm->data_type = param->type;
		  parm->range = nullptr;
		  parm->local_flag = false;
		  parm->overridable = true;
		  parm->type_flag = false;
		  parm->lexical_pos = param->get_lineno();
		  class_scope->parameters[param->name] = parm;
	    }
      }
}

void pform_class_property(const struct vlltype&loc,
			  property_qualifier_t property_qual,
			  data_type_t*data_type,
			  list<decl_assignment_t*>*decls)
{
      ivl_assert(loc, pform_cur_class);

	// Add the non-static properties to the class type
	// object. Unwind the list of names to make a map of name to
	// type.
      for (list<decl_assignment_t*>::iterator cur = decls->begin()
		 ; cur != decls->end() ; ++cur) {

	    decl_assignment_t*curp = *cur;
	    data_type_t*use_type = data_type;

	    if (! curp->index.empty()) {
		  list<pform_range_t>*pd = new list<pform_range_t> (curp->index);
		  use_type = new uarray_type_t(use_type, pd);
		  FILE_NAME(use_type, loc);
	    }

	    pform_cur_class->type->properties[curp->name.first]
		  = class_type_t::prop_info_t(property_qual,use_type);
	    FILE_NAME(&pform_cur_class->type->properties[curp->name.first], loc);

	    if (PExpr*rval = curp->expr.release()) {
		  PExpr*lval = new PEIdent(curp->name.first, curp->name.second);
		  FILE_NAME(lval, loc);
		  PAssign*tmp = new PAssign(lval, rval);
		  FILE_NAME(tmp, loc);

		  if (property_qual.test_static())
			pform_cur_class->type->initialize_static.push_back(tmp);
		  else
			pform_cur_class->type->initialize.push_back(tmp);
	    }
      }
}

/*
 * Handle virtual interface property declarations.
 * Creates a property with virtual_interface_type_t as its type.
 */
void pform_class_property_virtual_interface(const struct vlltype&loc,
				 property_qualifier_t property_qual,
				 perm_string interface_name,
				 perm_string var_name,
				 PExpr*init_expr)
{
      ivl_assert(loc, pform_cur_class);

      // Create a virtual interface type for this property
      virtual_interface_type_t* vif_type = new virtual_interface_type_t(interface_name);
      FILE_NAME(vif_type, loc);

      // Store the property in the class
      pform_cur_class->type->properties[var_name]
	    = class_type_t::prop_info_t(property_qual, vif_type);
      FILE_NAME(&pform_cur_class->type->properties[var_name], loc);

      // Handle initializer if present
      if (init_expr) {
	    PExpr*lval = new PEIdent(var_name, false);
	    FILE_NAME(lval, loc);
	    PAssign*tmp = new PAssign(lval, init_expr);
	    FILE_NAME(tmp, loc);

	    if (property_qual.test_static())
		  pform_cur_class->type->initialize_static.push_back(tmp);
	    else
		  pform_cur_class->type->initialize.push_back(tmp);
      }
}

void pform_set_this_class(const struct vlltype&loc, PTaskFunc*net)
{
      if (pform_cur_class == 0)
	    return;

      // Set the virtual flag on the method if marked as virtual
      if (pform_cur_method_is_virtual)
	    net->set_virtual(true);

      // Static methods don't get an implicit 'this' parameter
      if (pform_cur_method_is_static)
	    return;

      list<pform_port_t>*this_name = new list<pform_port_t>;
      this_name->push_back(pform_port_t({ perm_string::literal(THIS_TOKEN), 0 }, 0, 0));
      vector<pform_tf_port_t>*this_port = pform_make_task_ports(loc,
						       NetNet::PINPUT,
						       pform_cur_class->type,
						       this_name);
	// The pform_make_task_ports() function deletes the this_name
	// object.

      ivl_assert(loc, !this_port->empty());
      ivl_assert(loc, this_port->at(0).defe == 0);
      PWire*this_wire = this_port->at(0).port;
      delete this_port;

      net->set_this(pform_cur_class->type, this_wire);
}

void pform_set_constructor_return(PFunction*net)
{
      ivl_assert(*net, pform_cur_class);
      net->set_return(pform_cur_class->type);
}

/*
 * A constructor is basically a function with special implications.
 */
PFunction*pform_push_constructor_scope(const struct vlltype&loc)
{
      ivl_assert(loc, pform_cur_class);
      PFunction*func = pform_push_function_scope(loc, "new", LexicalScope::AUTOMATIC);
      return func;
}

void pform_end_class_declaration(const struct vlltype&loc)
{
      ivl_assert(loc, pform_cur_class);

	// If there were initializer statements, then collect them
	// into an implicit constructor function. Also make sure that an
	// explicit constructor exists if base class constructor arguments are
	// specified, so that the base class constructor will be called.
      if (!pform_cur_class->type->initialize.empty() ||
          !pform_cur_class->type->base_args.empty()) {
	    PFunction*func = pform_push_function_scope(loc, "new@", LexicalScope::AUTOMATIC);
	    func->set_ports(0);
	    pform_set_constructor_return(func);
	    pform_set_this_class(loc, func);

	    class_type_t*use_class = pform_cur_class->type;
	    if (use_class->initialize.size() == 1) {
		  func->set_statement(use_class->initialize.front());
	    } else {
		  PBlock*tmp = new PBlock(PBlock::BL_SEQ);
		  tmp->set_statement(use_class->initialize);
		  func->set_statement(tmp);
	    }
	    pform_pop_scope();
      }

      pform_cur_class = 0;
      pform_pop_scope();
}

bool pform_in_class()
{
      return pform_cur_class != 0;
}

/*
 * Handle covergroup declarations inside a class.
 * This creates a property with the covergroup name that can be instantiated
 * and have methods called on it (sample, get_coverage, etc.).
 *
 * The covergroup is treated as an instance of a generated class that provides
 * stub implementations of the standard covergroup methods. This allows
 * testbenches with covergroups to compile and run, though coverage data
 * won't be collected.
 */
void pform_covergroup_declaration(const struct vlltype&loc,
				  const char* covergroup_name,
				  vector<pform_tf_port_t>* sample_ports)
{
      (void)sample_ports;  // TODO: Use sample ports to generate proper method signature

      if (!pform_cur_class) {
	    yywarn(loc, "warning: Covergroup declarations parsed but not yet functional.");
	    return;
      }

      // Create a covergroup_type_t that will be elaborated to the __ivl_covergroup
      // stub class from uvm_pkg or a placeholder type.
      perm_string cg_name = lex_strings.make(covergroup_name);

      // Create a covergroup type that will be resolved during elaboration.
      covergroup_type_t* cg_type = new covergroup_type_t(cg_name);
      FILE_NAME(cg_type, loc);

      // Add the covergroup as a property of the enclosing class
      pform_cur_class->type->properties[cg_name]
	    = class_type_t::prop_info_t(property_qualifier_t::make_none(), cg_type);
      FILE_NAME(&pform_cur_class->type->properties[cg_name], loc);

      yywarn(loc, "warning: Covergroup declarations parsed but not yet functional.");
}

static bool pform_in_extern_decl = false;

void pform_begin_extern_declaration()
{
      pform_in_extern_decl = true;
}

void pform_end_extern_declaration()
{
      pform_in_extern_decl = false;
}

bool pform_in_extern_declaration()
{
      return pform_in_extern_decl;
}

void pform_set_method_static(bool is_static)
{
      pform_cur_method_is_static = is_static;
}

void pform_reset_method_static()
{
      pform_cur_method_is_static = false;
}

void pform_set_method_virtual(bool is_virtual)
{
      pform_cur_method_is_virtual = is_virtual;
}

void pform_reset_method_virtual()
{
      pform_cur_method_is_virtual = false;
}

/*
 * Declare an extern function in a class. For now, just warn that external
 * methods are parsed but the body must be provided inline or we issue an error.
 * Full out-of-body support requires additional scope management.
 */
void pform_declare_extern_function(const struct vlltype&loc,
				   property_qualifier_t quals,
				   data_type_t* return_type,
				   const char* name,
				   vector<pform_tf_port_t>* ports)
{
      (void)return_type;
      (void)ports;

      // Store the method qualifiers for later use by out-of-body definition.
      // This allows virtual, static, and other qualifiers to be preserved.
      if (pform_cur_class && pform_cur_class->type) {
	    perm_string pname = lex_strings.make(name);
	    pform_cur_class->type->extern_method_quals[pname] = quals;
      }

      // Warn that out-of-body definition is expected.
      yywarn(loc, "extern function declaration - out-of-body definition expected.");
}

/*
 * Declare an extern task in a class.
 */
void pform_declare_extern_task(const struct vlltype&loc,
			       property_qualifier_t quals,
			       const char* name,
			       vector<pform_tf_port_t>* ports)
{
      (void)ports;

      // Store the method qualifiers for later use by out-of-body definition.
      // This allows virtual, static, and other qualifiers to be preserved.
      if (pform_cur_class && pform_cur_class->type) {
	    perm_string pname = lex_strings.make(name);
	    pform_cur_class->type->extern_method_quals[pname] = quals;
      }

      // Warn that out-of-body definition is expected.
      yywarn(loc, "extern task declaration - out-of-body definition expected.");
}

/*
 * Setter for pform_cur_class - used by out-of-body method support.
 */
void pform_set_cur_class(PClass*cls)
{
      pform_cur_class = cls;
}

/*
 * End an out-of-body method definition.
 */
void pform_end_external_method(void)
{
      pform_cur_class = 0;
}
