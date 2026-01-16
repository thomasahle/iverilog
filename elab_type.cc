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

static typedef_t* resolve_typedef_by_name(Design*des, NetScope*scope, perm_string name)
{
      if (!scope)
	    return 0;

      NetScope*cur_scope = scope;
      std::set<const NetScope*> visited;

      while (cur_scope) {
	    if (visited.count(cur_scope))
		  break;
	    visited.insert(cur_scope);

	    if (typedef_t*td = cur_scope->find_typedef(name)) {
		  if (td->get_data_type())
			return td;
	    }

	    NetScope*import_scope = cur_scope->find_import(des, name);
	    if (import_scope && !visited.count(import_scope)) {
		  cur_scope = import_scope;
		  continue;
	    }

	    NetScope*parent = cur_scope->parent();
	    if (parent) {
		  cur_scope = parent;
	    } else if (cur_scope != cur_scope->unit()) {
		  cur_scope = cur_scope->unit();
	    } else {
		  break;
	    }
      }

      return 0;
}

/*
 * Elaborations of types may vary depending on the scope that it is
 * done in, so keep a per-scope cache of the results.
 */
ivl_type_t data_type_t::elaborate_type(Design*des, NetScope*scope)
{
      scope = find_scope(des, scope);

      Definitions*use_definitions = scope;

      map<Definitions*,ivl_type_t>::iterator pos = cache_type_elaborate_.lower_bound(use_definitions);
	  if (pos != cache_type_elaborate_.end() && pos->first == use_definitions) {
	     return pos->second;
	  }

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
	    // Use default int type to allow continued elaboration without crash
	    base = netvector_t::integer_type();
	    vec_type = dynamic_cast<const netvector_t*>(base);
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

ivl_type_t event_type_t::elaborate_type_raw(Design*, NetScope*) const
{
      return &netevent_type_t::type_event;
}

ivl_type_t semaphore_type_t::elaborate_type_raw(Design*, NetScope*) const
{
      return &netsemaphore_t::type_semaphore;
}

ivl_type_t mailbox_type_t::elaborate_type_raw(Design*, NetScope*) const
{
      return &netmailbox_t::type_mailbox;
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
 * Helper function to extract a simple property name from a coverpoint expression.
 * Returns empty string if the expression is too complex (not a simple identifier).
 */
static string extract_coverpoint_property_name(PExpr* expr)
{
      // Check if expression is a simple PEIdent
      PEIdent* ident = dynamic_cast<PEIdent*>(expr);
      if (!ident)
            return "";

      // Check for a single-component name (simple property reference)
      const pform_scoped_name_t& path = ident->path();
      if (path.package != nullptr)
            return "";  // Has package scope - too complex

      if (path.name.size() != 1)
            return "";  // Hierarchical path - too complex

      // Get the simple property name
      const name_component_t& comp = path.name.front();
      if (!comp.index.empty())
            return "";  // Has index - too complex

      return comp.name.str();
}

/*
 * Helper function to evaluate a constant expression for bin range values.
 * Returns true if successful, false if expression is not constant.
 */
static bool eval_bin_range_const(PExpr* expr, int64_t& value)
{
      PENumber* num = dynamic_cast<PENumber*>(expr);
      if (num) {
            value = num->value().as_long();
            return true;
      }
      // Could extend to handle more constant expressions
      return false;
}

/*
 * Covergroup type elaboration.
 * Covergroups are implemented via the __ivl_covergroup class from the UVM
 * library. This class provides sample() and get_coverage() methods that
 * track sampling activity and report coverage percentages.
 *
 * If __ivl_covergroup is not found (e.g., UVM package not included),
 * we return a simple type that allows the code to compile.
 */
ivl_type_t covergroup_type_t::elaborate_type_raw(Design*des, NetScope*scope) const
{
      // Calculate the bins count from coverpoints
      int bins_count = calculate_bins_count();

      // Store the bins count in the Design for later use during code generation
      // This allows the constructor to set m_target_bins correctly
      des->set_covergroup_bins_count(covergroup_name, bins_count);

      // Build coverpoint info for runtime bin tracking
      covergroup_info_t cg_info;
      for (const pform_coverpoint_t* pcp : coverpoints) {
            covergroup_coverpoint_t ecp;

            // Get coverpoint name
            if (!pcp->name.nil())
                  ecp.name = pcp->name.str();

            // Try to extract simple property name from expression
            if (pcp->expr) {
                  ecp.property_name = extract_coverpoint_property_name(pcp->expr);
            }

            // Convert bins info
            if (pcp->bins.empty()) {
                  // No explicit bins - auto bins
                  ecp.auto_bins_count = 16;  // Default auto bin count
            } else {
                  ecp.auto_bins_count = 0;
                  for (const pform_bin_t* pbin : pcp->bins) {
                        covergroup_bin_t ebin;
                        ebin.name = pbin->name.str();
                        ebin.is_ignore = (pbin->kind == pform_bin_t::IGNORE_BIN);
                        ebin.is_illegal = (pbin->kind == pform_bin_t::ILLEGAL_BIN);

                        // Convert bin ranges
                        for (const pform_bin_range_t& pr : pbin->ranges) {
                              int64_t low_val = 0, high_val = 0;
                              switch (pr.type) {
                              case pform_bin_range_t::DISCRETE:
                                    if (eval_bin_range_const(pr.low_expr, low_val)) {
                                          ebin.ranges.push_back(covergroup_bin_range_t(low_val));
                                    }
                                    break;
                              case pform_bin_range_t::RANGE:
                                    if (eval_bin_range_const(pr.low_expr, low_val) &&
                                        eval_bin_range_const(pr.high_expr, high_val)) {
                                          ebin.ranges.push_back(covergroup_bin_range_t(low_val, high_val, true));
                                    }
                                    break;
                              default:
                                    // UNBOUNDED_HIGH/UNBOUNDED_LOW not yet handled
                                    break;
                              }
                        }
                        ecp.bins.push_back(ebin);
                  }
            }
            cg_info.coverpoints.push_back(ecp);
      }

      // Store the covergroup info for runtime bin tracking
      des->set_covergroup_info(covergroup_name, cg_info);

      if (debug_elaborate) {
            cerr << get_fileline() << ": debug: Covergroup '" << covergroup_name
                 << "' has " << coverpoints.size() << " coverpoints with "
                 << bins_count << " total bins." << endl;
            for (const covergroup_coverpoint_t& cp : cg_info.coverpoints) {
                  cerr << "    coverpoint '" << cp.name << "'"
                       << " property='" << cp.property_name << "'"
                       << " bins=" << cp.bins.size()
                       << " auto_bins=" << cp.auto_bins_count << endl;
            }
      }

      // Try to find the __ivl_covergroup class
      perm_string stub_name = perm_string::literal("__ivl_covergroup");

      // First try in current scope
      netclass_t* stub_class = scope->find_class(des, stub_name);
      if (stub_class) {
            return stub_class;
      }

      // Search in all package scopes (e.g., uvm_pkg)
      list<NetScope*> pkg_list = des->find_package_scopes();
      for (list<NetScope*>::iterator it = pkg_list.begin()
             ; it != pkg_list.end() ; ++it) {
            NetScope*pkg_scope = *it;
            stub_class = pkg_scope->find_class(des, stub_name);
            if (stub_class) {
                  return stub_class;
            }
      }

      // If not found, emit a warning and return a simple integer type
      // This allows the code to at least compile but coverage won't work
      cerr << get_fileline() << ": warning: "
           << "Covergroup '" << covergroup_name << "' requires __ivl_covergroup class. "
           << "Include uvm_pkg.sv for coverage support." << endl;

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
	  dynamic_cast<const netclass_t*>(type) ||
	  dynamic_cast<const netenum_t*>(type) ||
	  dynamic_cast<const netdarray_t*>(type) ||
	  dynamic_cast<const netqueue_t*>(type))
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

      // Note: queues and dynamic arrays are now supported as element types
      // of static (unpacked) arrays. The VVP runtime handles nested arrays
      // via vvp_darray_object which stores std::vector<vvp_object_t>.

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

      // Track pending associative array key type - the associative array
      // should be created AFTER processing remaining static dimensions
      ivl_type_t pending_assoc_key_type = nullptr;
      bool pending_assoc_wildcard = false;

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
		    // Don't create the netassoc_t yet - wait until we've processed
		    // any remaining static dimensions that should be part of element type.
		  type = elaborate_static_array_type(des, li, type, dimensions);
		  type = elaborate_darray_check_type(des, li, type, "Associative array");
		  pending_assoc_key_type = ptype->get_type()->elaborate_type(des, scope);
		  continue;
	    } else if (dynamic_cast<PENull*>(lidx)) {
		    // Special case: Detect the mark for a QUEUE declaration,
		    // which is the dimensions [null:max_idx].
		    // Also detect wildcard associative array [*] which is
		    // marked as [PENull:PENumber(1)] where value is EXACTLY 1.
		    // Bounded queues like [$:2] have ridx as PENumber(2).
		  if (PENumber *pnum = dynamic_cast<PENumber*>(ridx)) {
			// Check if this is the wildcard marker (value == 1)
			const verinum &val = pnum->value();
			if (val.is_defined() && val.as_long() == 1 &&
			    val.len() == 1) {
			      // Wildcard associative array [*]
			      type = elaborate_static_array_type(des, li, type, dimensions);
			      type = elaborate_darray_check_type(des, li, type, "Associative array");
			      pending_assoc_wildcard = true;
			      continue;
			}
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

      // Apply remaining static dimensions to the element type
      type = elaborate_static_array_type(des, li, type, dimensions);

      // Now create the associative array wrapper if we had a pending one
      if (pending_assoc_key_type || pending_assoc_wildcard) {
	    type = new netassoc_t(type, pending_assoc_key_type);
      }

      return type;
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
                        // Get the unspecialized base class first - we need it to find
                        // the definition scope where specializations are stored.
                        netclass_t* base_class = s->find_class(des, class_def->name);
                        if (!base_class) {
                              cerr << get_fileline() << ": error: "
                                   << "Cannot find base class " << class_def->name
                                   << " for specialization." << endl;
                              des->errors++;
                              return type->elaborate_type(des, s);
                        }

                        // Get the definition scope - this is where specializations
                        // are stored and should be looked up.
                        NetScope* definition_scope = base_class->definition_scope();
                        if (!definition_scope) definition_scope = s;

                        // Generate a unique name for this specialization
                        perm_string spec_name = make_specialization_name(class_def->name, spec_params, des, s);

                        // Check if this specialization already exists in the definition
                        // scope. We must check there because that's where we add new
                        // specializations, regardless of which scope is elaborating them.
                        netclass_t* existing = definition_scope->find_class(des, spec_name);
                        if (existing) {
                              return existing;
                        }

                        // Create a new specialized class that inherits from the template.
                        // This preserves method accessibility through the class hierarchy.
                        // Properties with the same name as parent properties will have their
                        // types overridden in set_property() without changing indices.
                        netclass_t* spec_class = new netclass_t(spec_name, base_class);

                        // Create a new scope for the specialization
                        // Use the base class scope as parent so that type parameters can be found
                        const NetScope* base_class_scope = base_class->class_scope();

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
                                          // Also store in the class for method re-elaboration
                                          spec_class->set_type_param_override(formal->name, actual_type);
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
                                    if (actual->value_param) {
                                          spec_class->set_value_param_override(formal->name);
                                    }
                              }

                              ++param_it;
                              ++spec_it;
                        }

                        // Store specialized property types for the template's properties.
                        // We use set_property_type_override() to store the specialized types
                        // without adding duplicate properties. The template's properties will
                        // be inherited with the correct indices, and get_prop_type() will
                        // return the overridden specialized type when accessed through this class.
                        for (const auto& prop : class_def->properties) {
                              ivl_type_t prop_type = prop.second.type->elaborate_type(des, spec_scope);
                              spec_class->set_property_type_override(prop.first, prop_type);
                        }

                        // NOTE: Method re-elaboration for parameterized class specializations is complex.
                        // The issue is that methods in the base class were elaborated with W=8,
                        // but we need W=16 for Item#(16). Re-elaborating during type elaboration
                        // phase crashes because elaborate_scope is designed for a different phase.
                        //
                        // This is a known limitation. For now, methods inherit from base class
                        // and use the default parameter values. Workarounds:
                        // 1. Use properties directly instead of method parameters
                        // 2. Pass width as a runtime parameter
                        // 3. Override the method in a derived class
                        //
                        // TODO: Implement lazy method specialization at call site.

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
	    if (typedef_t*resolved = resolve_typedef_by_name(des, scope, name)) {
		  return resolved->elaborate_type(des, scope);
	    }
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
