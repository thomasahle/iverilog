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

# include  "PExpr.h"
# include  "PScope.h"
# include  "pform_types.h"
# include  "netlist.h"
# include  "netassoc.h"
# include  "netclass.h"
# include  "netdarray.h"
# include  "netenum.h"
# include  "netqueue.h"
# include  "netparray.h"
# include  "netscalar.h"
# include  "netstruct.h"
# include  "netvector.h"
# include  "netmisc.h"
# include  "compiler.h"
# include  "Module.h"
# include  <typeinfo>
# include  <sstream>
# include  "ivl_assert.h"

using namespace std;

/*
 * Elaborations of types may vary depending on the scope that it is
 * done in, so keep a per-scope cache of the results.
 */
ivl_type_t data_type_t::elaborate_type(Design*des, NetScope*scope)
{
      scope = find_scope(des, scope);

      Definitions*use_definitions = scope;

      map<Definitions*,ivl_type_t>::iterator pos = cache_type_elaborate_.lower_bound(use_definitions);
	  if (pos != cache_type_elaborate_.end() && pos->first == use_definitions)
	     return pos->second;

      ivl_type_t tmp;
      if (elaborating) {
	    des->errors++;
	    cerr << get_fileline() << ": error: "
	         << "Circular type definition found involving `" << *this << "`."
		 << endl;
	    // Try to recover
	    tmp = netvector_t::integer_type();
      } else {
	    elaborating = true;
	    tmp = elaborate_type_raw(des, scope);
	    elaborating = false;
      }

      cache_type_elaborate_.insert(pos, pair<NetScope*,ivl_type_t>(scope, tmp));
      return tmp;
}

NetScope *data_type_t::find_scope(Design *, NetScope *scope) const
{
	return scope;
}

ivl_type_t data_type_t::elaborate_type_raw(Design*des, NetScope*) const
{
      cerr << get_fileline() << ": internal error: "
	   << "Elaborate method not implemented for " << typeid(*this).name()
	   << "." << endl;
      des->errors += 1;
      return 0;
}

ivl_type_t atom_type_t::elaborate_type_raw(Design*des, NetScope*) const
{
      switch (type_code) {
	  case INTEGER:
	    return netvector_t::integer_type(signed_flag);

	  case TIME:
	    if (signed_flag)
		  return &netvector_t::time_signed;
	    else
		  return &netvector_t::time_unsigned;

	  case LONGINT:
	    if (signed_flag)
		  return &netvector_t::atom2s64;
	    else
		  return &netvector_t::atom2u64;

	  case INT:
	    if (signed_flag)
		  return &netvector_t::atom2s32;
	    else
		  return &netvector_t::atom2u32;

	  case SHORTINT:
	    if (signed_flag)
		  return &netvector_t::atom2s16;
	    else
		  return &netvector_t::atom2u16;

	  case BYTE:
	    if (signed_flag)
		  return &netvector_t::atom2s8;
	    else
		  return &netvector_t::atom2u8;

	  default:
	    cerr << get_fileline() << ": internal error: "
		 << "atom_type_t type_code=" << type_code << "." << endl;
	    des->errors += 1;
	    return 0;
      }
}

ivl_type_t class_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      return scope->find_class(des, name);
}

/*
 * elaborate_type_raw for enumerations is actually mostly performed
 * during scope elaboration so that the enumeration literals are
 * available at the right time. At that time, the netenum_t* object is
 * stashed in the scope so that I can retrieve it here.
 */
ivl_type_t enum_type_t::elaborate_type_raw(Design *des, NetScope *scope) const
{
      ivl_type_t base = base_type->elaborate_type(des, scope);

      const class netvector_t *vec_type = dynamic_cast<const netvector_t*>(base);

      if (!vec_type && !dynamic_cast<const netparray_t*>(base)) {
	    cerr << get_fileline() << ": error: "
		 << "Invalid enum base type `" << *base << "`."
		 << endl;
	    des->errors++;
      } else if (base->slice_dimensions().size() > 1) {
	    cerr << get_fileline() << ": error: "
		 << "Enum type must not have more than 1 packed dimension."
		 << endl;
	    des->errors++;
      }

      bool integer_flag = false;
      if (vec_type)
	    integer_flag = vec_type->get_isint();

      netenum_t *type = new netenum_t(base, names->size(), integer_flag);
      type->set_line(*this);

      scope->add_enumeration_set(this, type);

      return type;
}

ivl_type_t vector_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      netranges_t packed;
      if (pdims.get())
	    evaluate_ranges(des, scope, this, packed, *pdims);

      netvector_t*tmp = new netvector_t(packed, base_type);
      tmp->set_signed(signed_flag);
      tmp->set_isint(integer_flag);
      tmp->set_implicit(implicit_flag);

      return tmp;
}

ivl_type_t real_type_t::elaborate_type_raw(Design*, NetScope*) const
{
      switch (type_code_) {
	  case REAL:
	    return &netreal_t::type_real;
	  case SHORTREAL:
	    return &netreal_t::type_shortreal;
      }
      return 0;
}

ivl_type_t string_type_t::elaborate_type_raw(Design*, NetScope*) const
{
      return &netstring_t::type_string;
}

// Helper to find the Module definition for an interface by name
static Module* find_interface_module(perm_string name)
{
      extern std::map<perm_string,Module*> pform_modules;
      auto it = pform_modules.find(name);
      if (it != pform_modules.end() && it->second->is_interface) {
            return it->second;
      }
      return nullptr;
}

/*
 * Virtual interface elaboration: Creates a netvirtual_interface_t that stores
 * the interface name and a pointer to the interface definition scope.
 *
 * Note: At type elaboration time, the interface instance scope may not be
 * available yet because interface instances are elaborated during scope
 * elaboration. We store the interface_def as null if not found.
 * The actual interface scope will be bound at runtime when the virtual
 * interface variable is assigned to an actual interface instance.
 *
 * For compile-time member checking, we use the Module definition from
 * pform_modules to verify that the interface has the requested members.
 */
ivl_type_t virtual_interface_type_t::elaborate_type_raw(Design*des, NetScope*) const
{
      // First check if the interface definition exists in pform_modules
      Module* iface_mod = find_interface_module(interface_name);

      // Search for the interface scope in root scopes (for interfaces instantiated at top level)
      const NetScope* interface_def = nullptr;

      for (NetScope*root : des->find_root_scopes()) {
            if (root->is_interface() && root->module_name() == interface_name) {
                  interface_def = root;
                  break;
            }

            // Also search children of root scopes (for interfaces instantiated inside modules)
            // At type elaboration time, child scopes may not exist yet, but check anyway
            if (const NetScope* child = root->child_byname(interface_name)) {
                  if (child->is_interface()) {
                        interface_def = child;
                        break;
                  }
            }
      }

      (void)iface_mod; // Mark as intentionally unused for now

      return new netvirtual_interface_t(interface_name, interface_def);
}

/*
 * Covergroup type elaboration.
 * Since covergroups are parsed but not fully functional, we try to look up
 * the __ivl_covergroup stub class from the UVM library. If not found, we
 * return a simple type that allows the code to compile.
 */
ivl_type_t covergroup_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      // Try to find the __ivl_covergroup stub class
      perm_string stub_name = perm_string::literal("__ivl_covergroup");
      netclass_t* stub_class = scope->find_class(des, stub_name);
      if (stub_class) {
            return stub_class;
      }

      // If not found, emit a warning and return a simple integer type
      // This allows the code to at least compile
      cerr << get_fileline() << ": warning: "
           << "Covergroup '" << covergroup_name << "' elaborated as stub. "
           << "Covergroups are parsed but not yet functional." << endl;

      // Return a simple vector type as placeholder
      return new netvector_t(IVL_VT_LOGIC, 31, 0);
}

ivl_type_t parray_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      netranges_t packed;
      if (dims.get())
	    evaluate_ranges(des, scope, this, packed, *dims);

      ivl_type_t etype = base_type->elaborate_type(des, scope);
      if (!etype->packed()) {
		cerr << this->get_fileline() << " error: Packed array ";
		cerr << "base-type `";
		cerr << *base_type;
		cerr << "` is not packed." << endl;
		des->errors++;
      }

      return new netparray_t(packed, etype);
}

ivl_type_t struct_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      netstruct_t*res = new netstruct_t;

      res->set_line(*this);

      res->packed(packed_flag);
      res->set_signed(signed_flag);

      if (union_flag)
	    res->union_flag(true);

      for (list<struct_member_t*>::iterator cur = members->begin()
		 ; cur != members->end() ; ++ cur) {

	      // Elaborate the type of the member.
	    struct_member_t*curp = *cur;
	    ivl_type_t mem_vec = curp->type->elaborate_type(des, scope);
	    if (mem_vec == 0)
		  continue;

	      // There may be several names that are the same type:
	      //   <data_type> name1, name2, ...;
	      // Process all the member, and give them a type.
	    for (list<decl_assignment_t*>::iterator cur_name = curp->names->begin()
		       ; cur_name != curp->names->end() ;  ++ cur_name) {
		  decl_assignment_t*namep = *cur_name;

		  if (packed_flag && namep->expr) {
			cerr << namep->expr->get_fileline() << " error: "
			     << "Packed structs must not have default member values."
			     << endl;
			des->errors++;
		  }

		  netstruct_t::member_t memb;
		  memb.name = namep->name.first;
		  memb.net_type = elaborate_array_type(des, scope, *this,
						       mem_vec, namep->index);
		  res->append_member(des, memb);
	    }
      }

      return res;
}

static ivl_type_t elaborate_darray_check_type(Design *des, const LineInfo &li,
					      ivl_type_t type,
					      const char *darray_type)
{
      if (dynamic_cast<const netvector_t*>(type) ||
	  dynamic_cast<const netparray_t*>(type) ||
	  dynamic_cast<const netreal_t*>(type) ||
	  dynamic_cast<const netstring_t*>(type) ||
	  dynamic_cast<const netstruct_t*>(type) ||
	  dynamic_cast<const netclass_t*>(type))
	    return type;

      cerr << li.get_fileline() << ": Sorry: "
           << darray_type << " of type `" << *type
	   << "` is not yet supported." << endl;
      des->errors++;

      // Return something to recover
      return new netvector_t(IVL_VT_LOGIC);
}

static ivl_type_t elaborate_queue_type(Design *des, NetScope *scope,
				       const LineInfo &li, ivl_type_t base_type,
				       PExpr *ridx)
{
      base_type = elaborate_darray_check_type(des, li, base_type, "Queue");

      long max_idx = -1;
      if (ridx) {
	    NetExpr*tmp = elab_and_eval(des, scope, ridx, -1, true);
	    NetEConst*cv = dynamic_cast<NetEConst*>(tmp);
	    if (cv == 0) {
		  cerr << li.get_fileline() << ": error: "
		       << "queue bound must be constant."
		       << endl;
		  des->errors++;
	    } else {
		  verinum res = cv->value();
		  if (res.is_defined()) {
			max_idx = res.as_long();
			if (max_idx < 0) {
			      cerr << li.get_fileline() << ": error: "
				   << "queue bound must be positive ("
				   << max_idx << ")." << endl;
			      des->errors++;
			      max_idx = -1;
			}
		  } else {
			cerr << li.get_fileline() << ": error: "
			     << "queue bound must be defined."
			     << endl;
			des->errors++;
		  }
	    }
	    delete cv;
      }

      return new netqueue_t(base_type, max_idx);
}

// If dims is not empty create a unpacked array type and clear dims, otherwise
// return the base type. Also check that we actually support the base type.
static ivl_type_t elaborate_static_array_type(Design *des, const LineInfo &li,
					      ivl_type_t base_type,
					      netranges_t &dims)
{
      if (dims.empty())
	    return base_type;

      if (dynamic_cast<const netqueue_t*>(base_type)) {
	    cerr << li.get_fileline() << ": sorry: "
		 << "array of queue type is not yet supported."
		 << endl;
	    des->errors++;
	    // Recover
	    base_type = new netvector_t(IVL_VT_LOGIC);
      } else if (dynamic_cast<const netdarray_t*>(base_type)) {
	    cerr << li.get_fileline() << ": sorry: "
		 << "array of dynamic array type is not yet supported."
		 << endl;
	    des->errors++;
	    // Recover
	    base_type = new netvector_t(IVL_VT_LOGIC);
      }

      ivl_type_t type = new netuarray_t(dims, base_type);
      dims.clear();

      return type;
}

ivl_type_t elaborate_array_type(Design *des, NetScope *scope,
			        const LineInfo &li, ivl_type_t base_type,
			        const list<pform_range_t> &dims)
{
      const long warn_dimension_size = 1 << 30;
      netranges_t dimensions;
      dimensions.reserve(dims.size());

      ivl_type_t type = base_type;

      for (list<pform_range_t>::const_iterator cur = dims.begin();
	   cur != dims.end() ; ++cur) {
	    PExpr *lidx = cur->first;
	    PExpr *ridx = cur->second;

	    if (lidx == 0 && ridx == 0) {
		    // Special case: If we encounter an undefined dimensions,
		    // then turn this into a dynamic array and put all the
		    // packed dimensions there.
		  type = elaborate_static_array_type(des, li, type, dimensions);
		  type = elaborate_darray_check_type(des, li, type, "Dynamic array");
		  type = new netdarray_t(type);
		  continue;
	    } else if (PETypename *ptype = dynamic_cast<PETypename*>(lidx)) {
		    // Special case: Detect the mark for an ASSOCIATIVE ARRAY
		    // with a typed index, which is [data_type].
		  type = elaborate_static_array_type(des, li, type, dimensions);
		  type = elaborate_darray_check_type(des, li, type, "Associative array");
		  ivl_type_t idx_type = ptype->get_type()->elaborate_type(des, scope);
		  type = new netassoc_t(type, idx_type);
		  continue;
	    } else if (dynamic_cast<PENull*>(lidx)) {
		    // Special case: Detect the mark for a QUEUE declaration,
		    // which is the dimensions [null:max_idx].
		    // Also detect wildcard associative array [*] which is
		    // marked as [PENull:PENumber(1)].
		  if (ridx && dynamic_cast<PENumber*>(ridx)) {
			// Wildcard associative array [*]
			type = elaborate_static_array_type(des, li, type, dimensions);
			type = elaborate_darray_check_type(des, li, type, "Associative array");
			type = new netassoc_t(type, nullptr);
			continue;
		  }
		  type = elaborate_static_array_type(des, li, type, dimensions);
		  type = elaborate_queue_type(des, scope, li, type, ridx);
		  continue;
	    }

	    long index_l, index_r;
	    evaluate_range(des, scope, &li, *cur, index_l, index_r);

	    if (abs(index_r - index_l) > warn_dimension_size) {
		  cerr << li.get_fileline() << ": warning: "
		       << "Array dimension is greater than "
		       << warn_dimension_size << "."
		       << endl;
	    }

	    dimensions.push_back(netrange_t(index_l, index_r));
      }

      return elaborate_static_array_type(des, li, type, dimensions);
}

ivl_type_t uarray_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      ivl_type_t btype = base_type->elaborate_type(des, scope);

      return elaborate_array_type(des, scope, *this, btype, *dims.get());
}

/*
 * Helper function to generate a unique mangled name for a class specialization.
 * For example: holder#(int, 16) -> holder$$int$$16
 */
static perm_string make_specialization_name(perm_string base_name,
                                            const std::list<class_spec_param_t*>* spec_params,
                                            Design*des, NetScope*scope)
{
      std::ostringstream name_stream;
      name_stream << base_name.str() << "$$";

      bool first = true;
      for (const auto* param : *spec_params) {
            if (!first) name_stream << "$$";
            first = false;

            if (param->type_param) {
                  // For type parameters, use the type name
                  ivl_type_t elab_type = param->type_param->elaborate_type(des, scope);
                  if (elab_type) {
                        // Get a string representation of the type
                        std::ostringstream type_str;
                        type_str << *elab_type;
                        // Replace spaces and special chars with underscore
                        std::string ts = type_str.str();
                        for (char& c : ts) {
                              if (!isalnum(c)) c = '_';
                        }
                        name_stream << ts;
                  } else {
                        name_stream << "unknown";
                  }
            } else if (param->value_param) {
                  // For value parameters, try to evaluate to a constant
                  NetExpr*expr = elab_and_eval(des, scope, param->value_param, -1);
                  if (NetEConst*ce = dynamic_cast<NetEConst*>(expr)) {
                        name_stream << ce->value().as_long();
                  } else {
                        name_stream << "expr";
                  }
            }
      }

      return lex_strings.make(name_stream.str());
}

ivl_type_t typeref_t::elaborate_type_raw(Design*des, NetScope*s) const
{
      if (!s) {
	    // Try to recover
	    return new netvector_t(IVL_VT_LOGIC);
      }

      // Check if this is a class with specialization parameters
      if (spec_params && !spec_params->empty()) {
            // Get the base type to check if it's a class
            // Try to cast directly since basic_type may not be set for class types
            const class_type_t* class_def = dynamic_cast<const class_type_t*>(type->get_data_type());
            if (class_def && !class_def->parameters.empty()) {
                        // Generate a unique name for this specialization
                        perm_string spec_name = make_specialization_name(class_def->name, spec_params, des, s);

                        // Check if this specialization already exists
                        netclass_t* existing = s->find_class(des, spec_name);
                        if (existing) {
                              return existing;
                        }

                        // Get the unspecialized base class
                        netclass_t* base_class = s->find_class(des, class_def->name);
                        if (!base_class) {
                              cerr << get_fileline() << ": error: "
                                   << "Cannot find base class " << class_def->name
                                   << " for specialization." << endl;
                              des->errors++;
                              return type->elaborate_type(des, s);
                        }

                        // Create a new specialized class
                        // Note: The specialized class inherits from the base class (the template)
                        // so that methods defined in the template are inherited
                        netclass_t* spec_class = new netclass_t(spec_name, base_class);

                        // Create a new scope for the specialization
                        // Use the base class scope as parent so that type parameters can be found
                        const NetScope* base_class_scope = base_class->class_scope();
                        NetScope* definition_scope = base_class->definition_scope();
                        if (!definition_scope) definition_scope = s;

                        // Note: We make spec_scope a child of the base class scope
                        // so that type parameter typedefs can be found during elaboration
                        NetScope* spec_scope = new NetScope(const_cast<NetScope*>(base_class_scope),
                                                           hname_t(spec_name),
                                                           NetScope::CLASS,
                                                           definition_scope->unit());
                        spec_scope->set_line(this);
                        spec_scope->set_class_def(spec_class);
                        spec_class->set_class_scope(spec_scope);
                        spec_class->set_definition_scope(definition_scope);

                        // Apply specialization parameters
                        auto param_it = class_def->parameters.begin();
                        auto spec_it = spec_params->begin();

                        while (param_it != class_def->parameters.end() && spec_it != spec_params->end()) {
                              class_param_t* formal = *param_it;
                              class_spec_param_t* actual = *spec_it;

                              if (formal->is_type) {
                                    // Type parameter - elaborate the actual type
                                    ivl_type_t actual_type = nullptr;
                                    if (actual->type_param) {
                                          actual_type = actual->type_param->elaborate_type(des, s);
                                    } else if (formal->default_type) {
                                          actual_type = formal->default_type->elaborate_type(des, s);
                                    }
                                    if (actual_type) {
                                          // Store as a type parameter in the scope
                                          spec_scope->set_type_parameter(formal->name, actual_type);
                                    }
                              } else {
                                    // Value parameter - create a parameter with the actual value
                                    PExpr* val_expr = actual->value_param;
                                    if (!val_expr && formal->default_expr) {
                                          val_expr = formal->default_expr;
                                    }
                                    if (val_expr) {
                                          // Evaluate the expression
                                          NetExpr* net_expr = elab_and_eval(des, s, val_expr, -1);
                                          if (net_expr) {
                                                spec_scope->set_parameter(formal->name, net_expr, *this);
                                          }
                                    }
                              }

                              ++param_it;
                              ++spec_it;
                        }

                        // Elaborate properties using the specialized scope
                        for (const auto& prop : class_def->properties) {
                              ivl_type_t prop_type = prop.second.type->elaborate_type(des, spec_scope);
                              spec_class->set_property(prop.first, prop.second.qual, prop_type);
                        }

                        // Add the specialized class to the definition scope
                        definition_scope->add_class(spec_class);

                        return spec_class;
            }
      }

      return type->elaborate_type(des, s);
}

NetScope *typeref_t::find_scope(Design *des, NetScope *s) const
{
        // If a scope has been specified use that as a starting point for the
	// search
      if (scope)
	    s = des->find_package(scope->pscope_name());

      return s;
}

ivl_type_t typedef_t::elaborate_type(Design *des, NetScope *scope)
{
      if (!data_type.get()) {
	    cerr << get_fileline() << ": error: Undefined type `" << name << "`."
		 << endl;
	    des->errors++;

	    // Try to recover
	    return netvector_t::integer_type();
      }

      // Save the original scope - we need it for type parameter lookup
      NetScope *original_scope = scope;

        // Search upwards from where the type was referenced
      scope = scope->find_typedef_scope(des, this);
      if (!scope) {
	    cerr << get_fileline() << ": sorry: "
	         << "Can not find the scope type definition `" << name << "`."
		 << endl;
	    des->errors++;

	    // Try to recover
	    return netvector_t::integer_type();
      }

      // For type parameters, use the original scope for lookup
      // This allows specialized classes to find overridden type parameters
      type_parameter_t* type_param = dynamic_cast<type_parameter_t*>(data_type.get());
      if (type_param) {
	    scope = original_scope;
      }

      ivl_type_t elab_type = data_type->elaborate_type(des, scope);
      if (!elab_type)
	    return netvector_t::integer_type();

      bool type_ok = true;
      switch (basic_type) {
      case ENUM:
	    type_ok = dynamic_cast<const netenum_t *>(elab_type);
	    break;
      case STRUCT: {
	    const netstruct_t *struct_type = dynamic_cast<const netstruct_t *>(elab_type);
	    type_ok = struct_type && !struct_type->union_flag();
	    break;
      }
      case UNION: {
	    const netstruct_t *struct_type = dynamic_cast<const netstruct_t *>(elab_type);
	    type_ok = struct_type && struct_type->union_flag();
	    break;
      }
      case CLASS:
	    type_ok = dynamic_cast<const netclass_t *>(elab_type);
	    break;
      default:
	    break;
      }

      if (!type_ok) {
	    cerr << data_type->get_fileline() << " error: "
	         << "Unexpected type `" << *elab_type << "` for `" << name
		 << "`. It was forward declared as `" << basic_type
		 << "` at " << get_fileline() << "."
		 << endl;
	    des->errors++;
      }

      return elab_type;
}

ivl_type_t type_parameter_t::elaborate_type_raw(Design *des, NetScope*scope) const
{
      ivl_type_t type;

      scope->get_parameter(des, name, type);

      // Recover
      if (!type)
	    return netvector_t::integer_type();

      return type;
}
