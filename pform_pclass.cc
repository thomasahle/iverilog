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
