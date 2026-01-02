/*
 * Copyright (c) 2000-2025 Stephen Williams (steve@icarus.com)
 * Copyright CERN 2012-2013 / Stephen Williams (steve@icarus.com)
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

# include "config.h"

# include  "PExpr.h"
# include  "PPackage.h"
# include  "netlist.h"
# include  "netmisc.h"
# include  "netstruct.h"
# include  "netassoc.h"
# include  "netclass.h"
# include  "netdarray.h"
# include  "netqueue.h"
# include  "netparray.h"
# include  "netvector.h"
# include  "netenum.h"
# include  "netscalar.h"
# include  "compiler.h"
# include  "Module.h"
# include  <cstdlib>
# include  <iostream>
# include  <climits>
# include  "ivl_assert.h"

using namespace std;

/*
 * Helper function to find an interface instance scope by searching
 * recursively through all scopes. This is used when the interface_def
 * in the type is null (happens when type elaboration occurs before
 * interface instantiation).
 */
static const NetScope* find_interface_scope_recursive(const NetScope* scope, perm_string iface_name)
{
      if (!scope) return nullptr;

      // Check if this scope is the interface we're looking for
      if (scope->is_interface() && scope->module_name() == iface_name) {
            return scope;
      }

      // Search children recursively using child_by_module_name to find interface
      // instances by their type name (module_name), not instance name
      const NetScope* found = scope->child_by_module_name(iface_name);
      if (found && found->is_interface()) {
            return found;
      }

      return nullptr;
}

/*
 * Helper to find interface definition using Module from pform_modules
 * Returns a PWire for the given member name if found.
 */
static PWire* find_interface_wire_from_module(perm_string iface_name, perm_string member_name)
{
      extern std::map<perm_string,Module*> pform_modules;
      auto it = pform_modules.find(iface_name);
      if (it == pform_modules.end() || !it->second->is_interface) {
            return nullptr;
      }
      Module* iface_mod = it->second;

      // Look for the wire in the module
      auto wit = iface_mod->wires.find(member_name);
      if (wit != iface_mod->wires.end()) {
            return wit->second;
      }
      return nullptr;
}

/*
 * These methods generate a NetAssign_ object for the l-value of the
 * assignment. This is common code for the = and <= statements.
 *
 * What gets generated depends on the structure of the l-value. If the
 * l-value is a simple name (i.e., foo <= <value>) then the NetAssign_
 * is created the width of the foo reg and connected to all the
 * bits.
 *
 * If there is a part select (i.e., foo[3:1] <= <value>) the NetAssign_
 * is made only as wide as it needs to be (3 bits in this example) and
 * connected to the correct bits of foo. A constant bit select is a
 * special case of the part select.
 *
 * If the bit-select is non-constant (i.e., foo[<expr>] = <value>) the
 * NetAssign_ is made wide enough to connect to all the bits of foo,
 * then the mux expression is elaborated and attached to the
 * NetAssign_ node as a b_mux value. The target must interpret the
 * presence of a bmux value as taking a single bit and assigning it to
 * the bit selected by the bmux expression.
 *
 * If the l-value expression is non-trivial, but can be fully
 * evaluated at compile time (meaning any bit selects are constant)
 * then elaboration will make a single NetAssign_ that connects to a
 * synthetic reg that in turn connects to all the proper pins of the
 * l-value.
 *
 * This last case can turn up in statements like: {a, b[1]} = c;
 * rather than create a NetAssign_ for each item in the concatenation,
 * elaboration makes a single NetAssign_ and connects it up properly.
 */

void PEIdent::report_mixed_assignment_conflict_(const char*category) const
{
      cerr << get_fileline() << ": error: Cannot perform procedural "
              "assignment to " << category << " '" << path_
           << "' because it is also continuously assigned." << endl;
}

/*
 * The default interpretation of an l-value to a procedural assignment
 * is to try to make a net elaboration, and see if the result is
 * suitable for assignment.
 */
NetAssign_* PExpr::elaborate_lval(Design*, NetScope*, bool, bool, bool) const
{
      cerr << get_fileline() << ": Assignment l-value too complex." << endl;
      return 0;
}

/*
 * Concatenation expressions can appear as l-values. Handle them here.
 *
 * If adjacent l-values in the concatenation are not bit selects, then
 * merge them into a single NetAssign_ object. This can happen is code
 * like ``{ ...a, b, ...}''. As long as "a" and "b" do not have bit
 * selects (or the bit selects are constant) we can merge the
 * NetAssign_ objects.
 *
 * Be careful to get the bit order right. In the expression ``{a, b}''
 * a is the MSB and b the LSB. Connect the LSB to the low pins of the
 * NetAssign_ object.
 */
NetAssign_* PEConcat::elaborate_lval(Design*des,
				     NetScope*scope,
				     bool is_cassign,
				     bool is_force,
				     bool is_init) const
{
      if (repeat_) {
	    cerr << get_fileline() << ": error: Repeat concatenations make "
		  "no sense in l-value expressions. I refuse." << endl;
	    des->errors += 1;
	    return 0;
      }

      NetAssign_*res = 0;

      for (unsigned idx = 0 ;  idx < parms_.size() ;  idx += 1) {

	    if (parms_[idx] == 0) {
		  cerr << get_fileline() << ": error: Empty expressions "
		       << "not allowed in concatenations." << endl;
		  des->errors += 1;
		  continue;
	    }

	    NetAssign_*tmp = parms_[idx]->elaborate_lval(des, scope,
							 is_cassign, is_force, is_init);

	      /* If the l-value doesn't elaborate, the error was
		 already detected and printed. We just skip it and let
		 the compiler catch more errors. */
	    if (tmp == 0) continue;

	    if (tmp->expr_type() == IVL_VT_REAL) {
		  cerr << parms_[idx]->get_fileline() << ": error: "
		       << "concatenation operand can not be real: "
		       << *parms_[idx] << endl;
		  des->errors += 1;
		  continue;
	    }

	      /* A concatenation is always unsigned. */
	    tmp->set_signed(false);

	      /* Link the new l-value to the previous one. */
	    NetAssign_*last = tmp;
	    while (last->more)
		  last = last->more;

	    last->more = res;
	    res = tmp;
      }

      return res;
}


/*
 * Handle the ident as an l-value. This includes bit and part selects
 * of that ident.
 */
NetAssign_* PEIdent::elaborate_lval(Design*des,
				    NetScope*scope,
				    bool is_cassign,
				    bool is_force,
				    bool is_init) const
{

      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval: "
		 << "Elaborate l-value ident expression: " << *this << endl;
      }

      symbol_search_results sr;
      symbol_search(this, des, scope, path_, lexical_pos_, &sr);

      NetNet *reg = sr.net;
      const pform_name_t &member_path = sr.path_tail;

	/* The l-value must be a variable. If not, then give up and
	   print a useful error message. */
      if (reg == 0) {
	    if (scope->type()==NetScope::FUNC
		&& scope->func_def()->is_void()
		&& scope->basename()==peek_tail_name(path_)) {
		  cerr << get_fileline() << ": error: "
		       << "Cannot assign to " << path_
		       << " because function " << scope_path(scope)
		       << " is void." << endl;
	    } else {
		  cerr << get_fileline() << ": error: Could not find variable ``"
		       << path_ << "'' in ``" << scope_path(scope) <<
			"''" << endl;
		  if (sr.decl_after_use) {
			cerr << sr.decl_after_use->get_fileline() << ":      : "
				"A symbol with that name was declared here. "
				"Check for declaration after use." << endl;
		  }
	    }
	    des->errors += 1;
	    return 0;
      }

      ivl_assert(*this, reg);

      if (debug_elaborate) {
	    cerr << get_fileline() << ": " << __func__ << ": "
		 << "Found l-value path_=" << path_
		 << " as reg=" << reg->name() << endl;
	    cerr << get_fileline() << ": " << __func__ << ": "
		 << "reg->type()=" << reg->type()
		 << ", reg->unpacked_dimensions()=" << reg->unpacked_dimensions()
		 << endl;
	    if (reg->net_type())
		  cerr << get_fileline() << ": " << __func__ << ": "
		       << "reg->net_type()=" << *reg->net_type() << endl;
	    else
		  cerr << get_fileline() << ": " << __func__ << ": "
		       << "reg->net_type()=<nil>" << endl;
	    const pform_name_t &base_path = sr.path_head;
	    cerr << get_fileline() << ": " << __func__ << ": "
		 << " base_path=" << base_path
		 << ", member_path=" << member_path
		 << endl;
      }

      if (reg->get_const() && !is_init) {
	    cerr << get_fileline() << ": error: Assignment to const signal `"
	         << reg->name() << "` is not allowed." << endl;
	    des->errors++;
	    return nullptr;
      }

	// Handle interface port member l-value: intf.signal = value
	// Interface ports are compile-time bindings - we find the bound interface
	// instance and directly use its member signal.
      if (const netvirtual_interface_t*vif_type =
	        dynamic_cast<const netvirtual_interface_t*>(sr.type)) {
	    if (!member_path.empty()) {
		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval: "
			     << "Interface port member l-value: " << path_
			     << " member_path=" << member_path << endl;
		  }

		  // Find the bound interface instance. First check for stored binding.
		  const NetScope* iface_inst = nullptr;
		  perm_string iface_name = vif_type->interface_name();

		  // Get the port name from sr.path_head
		  perm_string port_name = peek_tail_name(sr.path_head);

		  // First, check for stored interface port binding
		  iface_inst = scope->get_interface_port_binding(port_name);

		  // If no explicit binding, look in parent scope (where instantiation happens)
		  if (!iface_inst) {
			NetScope* parent = scope->parent();
			if (parent) {
			      iface_inst = parent->child_by_module_name(iface_name);
			}
		  }

		  // Fallback: search root scopes
		  if (!iface_inst) {
			for (NetScope* root : des->find_root_scopes()) {
			      const NetScope* found = root->child_by_module_name(iface_name);
			      if (found && found->is_interface()) {
				    iface_inst = found;
				    break;
			      }
			}
		  }

		  if (!iface_inst) {
			cerr << get_fileline() << ": error: "
			     << "Interface instance of type `" << iface_name
			     << "` not found for interface port `" << sr.path_head
			     << "`." << endl;
			des->errors += 1;
			return 0;
		  }

		  // Get the member name from the path
		  ivl_assert(*this, member_path.size() >= 1);
		  name_component_t member_comp = member_path.front();

		  // Look up the member signal in the interface instance
		  NetNet* member_sig = const_cast<NetScope*>(iface_inst)->find_signal(member_comp.name);
		  if (!member_sig) {
			cerr << get_fileline() << ": error: "
			     << "Interface `" << iface_name
			     << "` has no member `" << member_comp.name << "`." << endl;
			des->errors += 1;
			return 0;
		  }

		  // Check that the member signal is assignable (reg type)
		  if ((member_sig->type() != NetNet::REG)
		      && ((member_sig->type() != NetNet::UNRESOLVED_WIRE) || !member_sig->coerced_to_uwire())
		      && !is_force) {
			cerr << get_fileline() << ": error: '"
			     << iface_name << "." << member_comp.name
			     << "' is not a valid l-value for a procedural assignment."
			     << endl;
			cerr << member_sig->get_fileline() << ":      : '"
			     << member_comp.name << "' is declared as a "
			     << member_sig->type() << " in the interface." << endl;
			des->errors += 1;
			return 0;
		  }

		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval: "
			     << "Found interface instance " << iface_inst->fullname()
			     << ", member signal " << member_sig->name() << endl;
		  }

		  // Create a direct l-value reference to the interface member signal
		  NetAssign_*lv = new NetAssign_(member_sig);

		  return lv;
	    }
      }

	// Fallback: Check if this is an interface instance member l-value.
	// This can happen when an interface instance is used as a port argument,
	// which may create a wire that shadows the interface scope.
      if (!member_path.empty()) {
	    perm_string base_name = peek_tail_name(sr.path_head);
	    const NetScope* iface_scope = 0;

	    // Search for interface scope by instance name in scope hierarchy
	    for (NetScope* search = scope; search && !iface_scope; search = search->parent()) {
		  const NetScope* child_scope = search->child(hname_t(base_name));
		  if (child_scope && child_scope->is_interface()) {
			iface_scope = child_scope;
		  }
	    }

	    if (iface_scope) {
		  // Found an interface scope - try to access the member
		  ivl_assert(*this, member_path.size() >= 1);
		  name_component_t member_comp = member_path.front();

		  NetNet* member_sig = const_cast<NetScope*>(iface_scope)->find_signal(member_comp.name);
		  if (member_sig) {
			// Check that the member signal is assignable (reg type)
			if ((member_sig->type() != NetNet::REG)
			    && ((member_sig->type() != NetNet::UNRESOLVED_WIRE) || !member_sig->coerced_to_uwire())
			    && !is_force) {
			      cerr << get_fileline() << ": error: '"
			           << iface_scope->module_name() << "." << member_comp.name
			           << "' is not a valid l-value for a procedural assignment."
			           << endl;
			      cerr << member_sig->get_fileline() << ":      : '"
			           << member_comp.name << "' is declared as a "
			           << member_sig->type() << " in the interface." << endl;
			      des->errors += 1;
			      return 0;
			}

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval: "
			           << "Interface instance " << base_name
			           << " member l-value via fallback: " << member_comp.name << endl;
			}

			// Create a direct l-value reference to the interface member signal
			NetAssign_*lv = new NetAssign_(member_sig);
			return lv;
		  }
	    }
      }

	/* We are elaborating procedural assignments. Wires are not allowed
	   unless this is the l-value of a force. */
      if ((reg->type() != NetNet::REG)
	  && ((reg->type() != NetNet::UNRESOLVED_WIRE) || !reg->coerced_to_uwire())
	  && !is_force) {
	    cerr << get_fileline() << ": error: '" << path_
		 << "' is not a valid l-value for a procedural assignment."
		 << endl;
	    cerr << reg->get_fileline() << ":      : '" << path_ <<
		  "' is declared here as a " << reg->type() << "." << endl;
	    des->errors += 1;
	    return 0;
      }

	// Handle dynamic array element with class property access
	// Pattern: objs[i].prop = value
      if (reg->darray_type() && !member_path.empty() && gn_system_verilog()) {
	    ivl_type_t elem_type = reg->darray_type()->element_type();
	    const netclass_t *elem_class = dynamic_cast<const netclass_t*>(elem_type);

	    if (elem_class) {
		    // Check if path_head has an index (darray element access)
		  const name_component_t& head_tail = sr.path_head.back();
		  if (!head_tail.index.empty()) {
			const index_component_t& idx = head_tail.index.back();
			if (idx.sel == index_component_t::SEL_BIT && idx.msb && !idx.lsb) {
			      if (debug_elaborate) {
				    cerr << get_fileline() << ": PEIdent::elaborate_lval: "
					 << "Elaborating darray[i].property pattern for "
					 << path_ << endl;
			      }

				// Create l-value for darray element
			      NetAssign_*lv = new NetAssign_(reg);

				// Elaborate the index expression and set as word
			      NetExpr*mux = elab_and_eval(des, scope, idx.msb, -1);
			      lv->set_word(mux);

				// Now chain with class member elaboration, passing initial_lv
			      return elaborate_lval_net_class_member_(des, scope, elem_class,
								      reg, member_path, lv);
			}
		  }
	    }
      }

      return elaborate_lval_var_(des, scope, is_force, is_cassign, reg,
			         sr.type, member_path);
}

NetAssign_*PEIdent::elaborate_lval_var_(Design *des, NetScope *scope,
				        bool is_force, bool is_cassign,
					NetNet *reg, ivl_type_t data_type,
					const pform_name_t tail_path) const
{
	// We are processing the tail of a string of names. For
	// example, the Verilog may be "a.b.c", so we are processing
	// "c" at this point.
      const name_component_t&name_tail = path_.back();


	// Use the last index to determine what kind of select
	// (bit/part/etc) we are processing. For example, the Verilog
	// may be "a.b.c[1][2][<index>]". All but the last index must
	// be simple expressions, only the <index> may be a part
	// select etc., so look at it to determine how we will be
	// proceeding.
      index_component_t::ctype_t use_sel = index_component_t::SEL_NONE;
      if (!name_tail.index.empty())
	    use_sel = name_tail.index.back().sel;

	// Special case: The l-value is an entire memory, or array
	// slice. Detect the situation by noting if the index count
	// is less than the array dimensions (unpacked).
      if (reg->unpacked_dimensions() > name_tail.index.size()) {
	    return elaborate_lval_array_(des, scope, is_force, reg);
      }

	// If we find that the matched variable is a packed struct,
	// then we can handled it with the net_packed_member_ method.
      if (reg->struct_type() && !tail_path.empty()) {
	    NetAssign_*lv = new NetAssign_(reg);
	    elaborate_lval_net_packed_member_(des, scope, lv, tail_path, is_force);
	    return lv;
      }

	// If the variable is a class object, then handle it with the
	// net_class_member_ method.
      const netclass_t *class_type = dynamic_cast<const netclass_t *>(data_type);
      if (class_type && !tail_path.empty() && gn_system_verilog())
	    return elaborate_lval_net_class_member_(des, scope, class_type, reg, tail_path);

	// Past this point, we should have taken care of the cases
	// where the name is a member/method of a struct/class.
	// XXXX ivl_assert(*this, method_name.nil());
      ivl_assert(*this, tail_path.empty());

      bool need_const_idx = is_cassign || is_force;

      // Check for arrays that have multiple indices to process.
      // For regular arrays, use unpacked_dimensions().
      // For associative arrays, the assoc array itself is a dimension,
      // plus any nested fixed-size arrays in the element type.
      size_t array_dims = reg->unpacked_dimensions();
      if (reg->data_type() == IVL_VT_ASSOC && reg->unpacked_dimensions() > 0) {
	    // For associative arrays WITH additional unpacked dimensions (like data[int][1]),
	    // add 1 for the assoc array dimension. Don't do this for simple assoc arrays
	    // (like data[int]) which should go through the darray_bit_ code path.
	    array_dims += 1;
      }
      if (array_dims > 0)
	    return elaborate_lval_net_word_(des, scope, reg, need_const_idx, is_force);

	// This must be after the array word elaboration above!
      if (reg->get_scalar() &&
          use_sel != index_component_t::SEL_NONE) {
	    cerr << get_fileline() << ": error: can not select part of ";
	    if (reg->data_type() == IVL_VT_REAL) cerr << "real: ";
	    else cerr << "scalar: ";
	    cerr << reg->name() << endl;
	    des->errors += 1;
	    return 0;
      }

      if (use_sel == index_component_t::SEL_PART) {
	    NetAssign_*lv = new NetAssign_(reg);
	    elaborate_lval_net_part_(des, scope, lv, is_force);
	    return lv;
      }

      if (use_sel == index_component_t::SEL_IDX_UP ||
          use_sel == index_component_t::SEL_IDX_DO) {
	    NetAssign_*lv = new NetAssign_(reg);
	    elaborate_lval_net_idx_(des, scope, lv, use_sel, need_const_idx, is_force);
	    return lv;
      }


      if (use_sel == index_component_t::SEL_BIT) {
	    if (reg->darray_type() || reg->assoc_type()) {
		  NetAssign_*lv = new NetAssign_(reg);
		  elaborate_lval_darray_bit_(des, scope, lv, is_force);
		  return lv;
	    } else {
		  NetAssign_*lv = new NetAssign_(reg);
		  elaborate_lval_net_bit_(des, scope, lv, need_const_idx, is_force);
		  return lv;
	    }
      }

      ivl_assert(*this, use_sel == index_component_t::SEL_NONE);

      if (reg->type()==NetNet::UNRESOLVED_WIRE && !is_force) {
	    ivl_assert(*this, reg->coerced_to_uwire());
	    report_mixed_assignment_conflict_("variable");
	    des->errors += 1;
	    return 0;
      }

	/* No select expressions. */

      NetAssign_*lv = new NetAssign_(reg);
      lv->set_signed(reg->get_signed());

      return lv;
}

NetAssign_*PEIdent::elaborate_lval_array_(Design *des, NetScope *,
				          bool is_force, NetNet *reg) const
{
      if (!gn_system_verilog()) {
	    cerr << get_fileline() << ": error: Assignment to an entire"
		  " array or to an array slice requires SystemVerilog."
		 << endl;
	    des->errors += 1;
	    return 0;
      }

      const name_component_t&name_tail = path_.back();
      if (name_tail.index.empty()) {
	    if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
		  ivl_assert(*this, reg->coerced_to_uwire());
		  report_mixed_assignment_conflict_("array");
		  des->errors += 1;
		  return 0;
	    }
	    NetAssign_*lv = new NetAssign_(reg);
	    return lv;
      }

      cerr << get_fileline() << ": sorry: Assignment to an "
	    " array slice is not yet supported."
	   << endl;
      des->errors += 1;
      return 0;
}

NetAssign_* PEIdent::elaborate_lval_net_word_(Design*des,
					      NetScope*scope,
					      NetNet*reg,
					      bool need_const_idx,
					      bool is_force) const
{
      const name_component_t&name_tail = path_.back();
      ivl_assert(*this, !name_tail.index.empty());

      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_word_: "
		 << "Handle as n-dimensional array." << endl;
      }

      if (name_tail.index.size() < reg->unpacked_dimensions()) {
	    cerr << get_fileline() << ": error: Array " << reg->name()
		 << " needs " << reg->unpacked_dimensions() << " indices,"
		 << " but got only " << name_tail.index.size() << "." << endl;
	    des->errors += 1;
	    return 0;
      }

	// Make sure there are enough indices to address an array element.
      const index_component_t&index_head = name_tail.index.front();
      if (index_head.sel == index_component_t::SEL_PART) {
	    cerr << get_fileline() << ": error: cannot perform a part "
	         << "select on array " << reg->name() << "." << endl;
	    des->errors += 1;
	    return 0;
      }


	// Evaluate all the index expressions into an
	// "unpacked_indices" array.
      list<NetExpr*>unpacked_indices;
      list<long> unpacked_indices_const;
      indices_flags flags;
      indices_to_expressions(des, scope, this,
			     name_tail.index, reg->unpacked_dimensions(),
			     false,
			     flags,
			     unpacked_indices,
			     unpacked_indices_const);

      NetExpr*canon_index = 0;
      if (flags.invalid) {
	    // Nothing to do.

      } else if (flags.undefined) {
	    cerr << get_fileline() << ": warning: "
		 << "ignoring undefined l-value array access "
		 << reg->name() << as_indices(unpacked_indices)
		 << "." << endl;

      } else if (flags.variable) {
	    if (need_const_idx) {
		  cerr << get_fileline() << ": error: array '" << reg->name()
		       << "' index must be a constant in this context." << endl;
		  des->errors += 1;
		  return 0;
	    }
	    ivl_assert(*this, unpacked_indices.size() == reg->unpacked_dimensions());
	    canon_index = normalize_variable_unpacked(reg, unpacked_indices);

      } else {
	    ivl_assert(*this, unpacked_indices_const.size() == reg->unpacked_dimensions());
	    canon_index = normalize_variable_unpacked(reg, unpacked_indices_const);

	    if (canon_index == 0) {
		  cerr << get_fileline() << ": warning: "
		       << "ignoring out of bounds l-value array access "
		       << reg->name() << as_indices(unpacked_indices_const)
		       << "." << endl;
	    }
      }

	// Ensure invalid array accesses are ignored.
      if (canon_index == 0)
	    canon_index = new NetEConst(verinum(verinum::Vx));
      canon_index->set_line(*this);

      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_word_: "
		 << "canon_index=" << *canon_index << endl;
      }

      if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
	    ivl_assert(*this, reg->coerced_to_uwire());
	    const NetEConst*canon_const = dynamic_cast<NetEConst*>(canon_index);
	    if (!canon_const || reg->test_part_driven(reg->vector_width() - 1, 0,
						      canon_const->value().as_long())) {
		  report_mixed_assignment_conflict_("array word");
		  des->errors += 1;
		  return 0;
	     }
      }

      NetAssign_*lv = new NetAssign_(reg);
      lv->set_word(canon_index);

      if (debug_elaborate)
	    cerr << get_fileline() << ": debug: Set array word=" << *canon_index << endl;


	/* An array word may also have part selects applied to them. */

      index_component_t::ctype_t use_sel = index_component_t::SEL_NONE;
      // For associative arrays WITH additional unpacked dimensions, count effective unpacked
      // dimensions including the assoc array itself plus any fixed-size unpacked dimensions.
      size_t effective_unpacked = reg->unpacked_dimensions();
      if (reg->data_type() == IVL_VT_ASSOC && reg->unpacked_dimensions() > 0) {
	    // Add 1 for the associative array dimension
	    effective_unpacked += 1;
      }
      if (name_tail.index.size() > effective_unpacked)
	    use_sel = name_tail.index.back().sel;

      if (reg->get_scalar() &&
          use_sel != index_component_t::SEL_NONE) {
	    cerr << get_fileline() << ": error: can not select part of ";
	    if (reg->data_type() == IVL_VT_REAL) cerr << "real";
	    else cerr << "scalar";
	    cerr << " array word: " << reg->name()
	         << as_indices(unpacked_indices) << endl;
	    des->errors += 1;
	    return 0;
      }

      if (use_sel == index_component_t::SEL_BIT)
	    elaborate_lval_net_bit_(des, scope, lv, need_const_idx, is_force);

      if (use_sel == index_component_t::SEL_PART)
	    elaborate_lval_net_part_(des, scope, lv, is_force);

      if (use_sel == index_component_t::SEL_IDX_UP ||
          use_sel == index_component_t::SEL_IDX_DO)
	    elaborate_lval_net_idx_(des, scope, lv, use_sel,
				    need_const_idx, is_force);

      return lv;
}

bool PEIdent::elaborate_lval_net_bit_(Design*des,
				      NetScope*scope,
				      NetAssign_*lv,
				      bool need_const_idx,
				      bool is_force) const
{
      list<long>prefix_indices;
      bool rc = calculate_packed_indices_(des, scope, lv->sig(), prefix_indices);
      if (!rc) return false;

      const name_component_t&name_tail = path_.back();
      ivl_assert(*this, !name_tail.index.empty());

      const index_component_t&index_tail = name_tail.index.back();
      ivl_assert(*this, index_tail.msb != 0);
      ivl_assert(*this, index_tail.lsb == 0);

      NetNet*reg = lv->sig();
      ivl_assert(*this, reg);

	// For associative arrays with unpacked dimensions (e.g., data[int][1]),
	// bit-select is not yet fully supported because calculate_packed_indices_
	// doesn't properly account for the mixed assoc + unpacked dimensions.
      if (reg->data_type() == IVL_VT_ASSOC && reg->unpacked_dimensions() > 0) {
	    cerr << get_fileline() << ": sorry: "
		 << "Bit-select on associative array element '"
		 << reg->name() << "' with additional unpacked dimensions "
		 << "is not yet supported." << endl;
	    des->errors += 1;
	    return false;
      }

	// Bit selects have a single select expression. Evaluate the
	// constant value and treat it as a part select with a bit
	// width of 1.
      NetExpr*mux = elab_and_eval(des, scope, index_tail.msb, -1);
      long lsb = 0;

      if (mux && mux->expr_type() == IVL_VT_REAL) {
           cerr << get_fileline() << ": error: Index expression for "
                << reg->name() << "[" << *mux
                << "] cannot be a real value." << endl;
           des->errors += 1;
           return false;
      }

      if (const NetEConst*index_con = dynamic_cast<NetEConst*> (mux)) {
	      // The index has a constant defined value.
	    if (index_con->value().is_defined()) {
		  lsb = index_con->value().as_long();
		  mux = 0;
	      // The index is undefined and this is a packed array.
	    } else if (prefix_indices.size()+2 <= reg->packed_dims().size()) {
		  long loff;
		  unsigned long lwid;
		  bool rcl = reg->sb_to_slice(prefix_indices, lsb, loff, lwid);
		  ivl_assert(*this, rcl);
		  if (warn_ob_select) {
			cerr << get_fileline()
			     << ": warning: L-value packed array select of "
			     << reg->name();
			if (reg->unpacked_dimensions() > 0) cerr << "[]";
			cerr << " has an undefined index." << endl;
		  }
		  lv->set_part(new NetEConst(verinum(verinum::Vx)), lwid);
		  return true;
	      // The index is undefined and this is a bit select.
	    } else {
		  if (warn_ob_select) {
			cerr << get_fileline()
			     << ": warning: L-value bit select of "
			     << reg->name();
			if (reg->unpacked_dimensions() > 0) cerr << "[]";
			cerr << " has an undefined index." << endl;
		  }
		  lv->set_part(new NetEConst(verinum(verinum::Vx)), 1);
		  return true;
	    }
      }

      if (debug_elaborate && (reg->type()==NetNet::UNRESOLVED_WIRE)) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_bit_: "
		 << "Try to assign bits of variable which is also continuously assigned."
		 << endl;
      }

      if (prefix_indices.size()+2 <= reg->packed_dims().size()) {
	      // Special case: this is a slice of a multi-dimensional
	      // packed array. For example:
	      //   reg [3:0][7:0] x;
	      //   x[2] = ...
	      // This shows up as the prefix_indices being too short
	      // for the packed dimensions of the vector. What we do
	      // here is convert to a "slice" of the vector.
	    if (mux == 0) {
		  long loff;
		  unsigned long lwid;
		  bool rcl = reg->sb_to_slice(prefix_indices, lsb, loff, lwid);
		  ivl_assert(*this, rcl);

		  if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
			ivl_assert(*this, reg->coerced_to_uwire());
			if (reg->test_part_driven(loff+lwid-1, loff)) {
			      report_mixed_assignment_conflict_("slice");
			      des->errors += 1;
			      return false;
			}
		  }

		  lv->set_part(new NetEConst(verinum(loff)), lwid);

	    } else {
		  unsigned long lwid;
		  mux = normalize_variable_slice_base(prefix_indices, mux,
						      reg, lwid);

		  if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
			ivl_assert(*this, reg->coerced_to_uwire());
			report_mixed_assignment_conflict_("slice");
			des->errors += 1;
			return false;
		  }

		  lv->set_part(mux, lwid);
	    }

      } else if (reg->data_type() == IVL_VT_STRING) {
	    ivl_assert(*this, reg->type()!=NetNet::UNRESOLVED_WIRE);
	      // Special case: This is a select of a string
	      // variable. The target of the assignment is a character
	      // select of a string. Force the r-value to be an 8bit
	      // vector and set the "part" to be the character select
	      // expression. The code generator knows what to do with
	      // this.
	    if (debug_elaborate) {
		  cerr << get_fileline() << ": debug: "
		       << "Bit select of string becomes character select." << endl;
	    }
	    if (!mux)
		  mux = new NetEConst(verinum(lsb));
	    lv->set_part(mux, &netvector_t::atom2s8);

      } else if (mux) {
	      // Non-constant bit mux. Correct the mux for the range
	      // of the vector, then set the l-value part select
	      // expression.
	    if (need_const_idx) {
		  cerr << get_fileline() << ": error: '" << reg->name()
		       << "' bit select must be a constant in this context."
		       << endl;
		  des->errors += 1;
		  return false;
	    }
	    mux = normalize_variable_bit_base(prefix_indices, mux, reg);

	    if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
		  ivl_assert(*this, reg->coerced_to_uwire());
		  report_mixed_assignment_conflict_("bit select");
		  des->errors += 1;
		  return false;
	    }

	    lv->set_part(mux, 1);

      } else if (reg->vector_width() == 1 && reg->sb_is_valid(prefix_indices,lsb)) {
	      // Constant bit mux that happens to select the only bit
	      // of the l-value. Don't bother with any select at all.
	      // If there's a continuous assignment, it must be a conflict.
	    if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
		  ivl_assert(*this, reg->coerced_to_uwire());
		  report_mixed_assignment_conflict_("bit select");
		  des->errors += 1;
		  return false;
	    }

      } else {
	      // Constant bit select that does something useful.
	    long loff = reg->sb_to_idx(prefix_indices,lsb);

	    if (warn_ob_select && (loff < 0 || loff >= (long)reg->vector_width())) {
		  cerr << get_fileline() << ": warning: bit select "
		       << reg->name() << "[" <<lsb<<"]"
		       << " is out of range." << endl;
	    }

	    if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
		  ivl_assert(*this, reg->coerced_to_uwire());
		  if (reg->test_part_driven(loff, loff)) {
			report_mixed_assignment_conflict_("bit select");
			des->errors += 1;
			return false;
		  }
	    }

	    lv->set_part(new NetEConst(verinum(loff)), 1);
      }

      return true;
}

bool PEIdent::elaborate_lval_darray_bit_(Design*des,
					 NetScope*scope,
					 NetAssign_*lv,
					 bool is_force) const
{
      const name_component_t&name_tail = path_.back();
      ivl_assert(*this, !name_tail.index.empty());

      if ((lv->sig()->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
	    ivl_assert(*this, lv->sig()->coerced_to_uwire());
	    report_mixed_assignment_conflict_("darray word");
	    des->errors += 1;
	    return false;
      }

      // Handle multi-dimensional access for nested arrays (e.g., arr[i][j])
      if (name_tail.index.size() == 2) {
	    // Check if element type is also a darray/queue
	    const netdarray_t*darray_type = lv->sig()->darray_type();
	    const netassoc_t*assoc_type = lv->sig()->assoc_type();

	    ivl_type_t element_type = 0;
	    if (darray_type)
		  element_type = darray_type->element_type();
	    else if (assoc_type)
		  element_type = assoc_type->element_type();

	    if (element_type) {
		  const netdarray_t*inner_darray = dynamic_cast<const netdarray_t*>(element_type);
		  const netqueue_t*inner_queue = dynamic_cast<const netqueue_t*>(element_type);

		  if (inner_darray || inner_queue) {
			// This is arr[i][j] where arr is int[][]
			// Set first index on current lval
			const index_component_t&first_idx = name_tail.index.front();
			ivl_assert(*this, first_idx.msb != 0);
			ivl_assert(*this, first_idx.lsb == 0);
			NetExpr*mux1 = elab_and_eval(des, scope, first_idx.msb, -1);
			lv->set_word(mux1);

			// Set second index - this will be used for inner array access
			const index_component_t&second_idx = name_tail.index.back();
			ivl_assert(*this, second_idx.msb != 0);
			ivl_assert(*this, second_idx.lsb == 0);
			NetExpr*mux2 = elab_and_eval(des, scope, second_idx.msb, -1);
			lv->set_word2(mux2);

			return true;
		  }

		  // Check if element type is packed (bit-select case)
		  // e.g., bit[7:0] data[int]; data[key][idx] = 1
		  if (element_type->packed()) {
			// First index is array word, second is bit-select
			const index_component_t&first_idx = name_tail.index.front();
			ivl_assert(*this, first_idx.msb != 0);
			ivl_assert(*this, first_idx.lsb == 0);
			NetExpr*mux = elab_and_eval(des, scope, first_idx.msb, -1);
			lv->set_word(mux);

			// Second index is bit-select
			const index_component_t&second_idx = name_tail.index.back();
			ivl_assert(*this, second_idx.msb != 0);
			ivl_assert(*this, second_idx.lsb == 0);
			NetExpr*bit_mux = elab_and_eval(des, scope, second_idx.msb, -1);
			lv->set_part(bit_mux, 1);

			return true;
		  }
	    }
	    // Fall through to error for non-nested cases
      }

      // For now, only support single-dimension dynamic arrays (or nested handled above)
      if (name_tail.index.size() != 1) {
	    cerr << get_fileline() << ": sorry: "
		 << "Associative/dynamic arrays with additional dimensions "
		 << "are not yet supported. Found " << name_tail.index.size()
		 << " indices." << endl;
	    des->errors += 1;
	    return false;
      }

      const index_component_t&index_tail = name_tail.index.back();
      ivl_assert(*this, index_tail.msb != 0);
      ivl_assert(*this, index_tail.lsb == 0);

	// Evaluate the select expression...
      NetExpr*mux = elab_and_eval(des, scope, index_tail.msb, -1);

      lv->set_word(mux);

      return true;
}

bool PEIdent::elaborate_lval_net_part_(Design*des,
				       NetScope*scope,
				       NetAssign_*lv,
				       bool is_force) const
{
      if (lv->sig()->data_type() == IVL_VT_STRING) {
           cerr << get_fileline() << ": error: Cannot part select assign to a string ('"
                << lv->sig()->name() << "')." << endl;
           des->errors += 1;
           return false;
      }

      list<long> prefix_indices;
      bool rc = calculate_packed_indices_(des, scope, lv->sig(), prefix_indices);
      ivl_assert(*this, rc);

	// The range expressions of a part select must be
	// constant. The calculate_parts_ function calculates the
	// values into msb and lsb.
      long msb, lsb;
      bool parts_defined_flag;
      calculate_parts_(des, scope, msb, lsb, parts_defined_flag);

      NetNet*reg = lv->sig();
      ivl_assert(*this, reg);

      if (! parts_defined_flag) {
	    if (warn_ob_select) {
		  cerr << get_fileline()
		       << ": warning: L-value part select of "
		       << reg->name();
		  if (reg->unpacked_dimensions() > 0) cerr << "[]";
		  cerr << " has an undefined index." << endl;
	    }
	      // Use a width of two here so we can distinguish between an
	      // undefined bit or part select.
	    lv->set_part(new NetEConst(verinum(verinum::Vx)), 2);
	    return true;
      }

      if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
	    ivl_assert(*this, reg->coerced_to_uwire());
	    if (reg->test_part_driven(msb, lsb)) {
		  report_mixed_assignment_conflict_("part select");
		  des->errors += 1;
		  return false;
	    }
      }

      const netranges_t&packed = reg->packed_dims();

      long loff, moff;
      if (prefix_indices.size()+1 < packed.size()) {
	      // If there are fewer indices then there are packed
	      // dimensions, then this is a range of slices. Calculate
	      // it into a big slice.
	    bool lrc, mrc;
	    unsigned long lwid, mwid;
	    lrc = reg->sb_to_slice(prefix_indices, lsb, loff, lwid);
	    mrc = reg->sb_to_slice(prefix_indices, msb, moff, mwid);
	    if (!mrc || !lrc) {
		  cerr << get_fileline() << ": error: ";
		  cerr << "Part-select [" << msb << ":" << lsb;
		  cerr << "] exceeds the declared bounds for ";
		  cerr << reg->name();
		  if (reg->unpacked_dimensions() > 0) cerr << "[]";
		  cerr << "." << endl;
		  des->errors += 1;
		  return 0;
	    }
	    assert(lwid == mwid);
	    moff += mwid - 1;
      } else {
	    loff = reg->sb_to_idx(prefix_indices,lsb);
	    moff = reg->sb_to_idx(prefix_indices,msb);
      }

      if (moff < loff) {
	    cerr << get_fileline() << ": error: part select "
		 << reg->name() << "[" << msb<<":"<<lsb<<"]"
		 << " is reversed." << endl;
	    des->errors += 1;
	    return false;
      }

      unsigned long wid = moff - loff + 1;

	// Special case: The range winds up selecting the entire
	// vector. Treat this as no part select at all.
      if (loff == 0 && wid == reg->vector_width()) {
	    return true;
      }

	/* If the part select extends beyond the extremes of the
	   variable, then output a warning. Note that loff is
	   converted to normalized form so is relative the
	   variable pins. */

      if (warn_ob_select && (loff < 0 || moff >= (long)reg->vector_width())) {
	    cerr << get_fileline() << ": warning: Part select "
		 << reg->name() << "[" << msb<<":"<<lsb<<"]"
		 << " is out of range." << endl;
      }

      lv->set_part(new NetEConst(verinum(loff)), wid);

      return true;
}

bool PEIdent::elaborate_lval_net_idx_(Design*des,
				      NetScope*scope,
				      NetAssign_*lv,
				      index_component_t::ctype_t use_sel,
				      bool need_const_idx,
				      bool is_force) const
{
      if (lv->sig()->data_type() == IVL_VT_STRING) {
           cerr << get_fileline() << ": error: Cannot index part select assign to a string ('"
                << lv->sig()->name() << "')." << endl;
           des->errors += 1;
           return false;
      }

      list<long>prefix_indices;
      bool rc = calculate_packed_indices_(des, scope, lv->sig(), prefix_indices);
      ivl_assert(*this, rc);

      const name_component_t&name_tail = path_.back();;
      ivl_assert(*this, !name_tail.index.empty());

      const index_component_t&index_tail = name_tail.index.back();
      ivl_assert(*this, index_tail.msb != 0);
      ivl_assert(*this, index_tail.lsb != 0);

      NetNet*reg = lv->sig();
      ivl_assert(*this, reg);

      unsigned long wid;
      calculate_up_do_width_(des, scope, wid);

      NetExpr*base = elab_and_eval(des, scope, index_tail.msb, -1);

      if (base && base->expr_type() == IVL_VT_REAL) {
	    cerr << get_fileline() << ": error: Indexed part select base "
	            "expression for ";
	    cerr << lv->sig()->name() << "[" << *base;
	    if (index_tail.sel == index_component_t::SEL_IDX_UP) {
		  cerr << "+:";
	    } else {
		  cerr << "-:";
	    }
	    cerr << wid << "] cannot be a real value." << endl;
	    des->errors += 1;
	    return 0;
      }

      ivl_select_type_t sel_type = IVL_SEL_OTHER;

	// Handle the special case that the base is constant. For this
	// case we can reduce the expression.
      if (const NetEConst*base_c = dynamic_cast<NetEConst*> (base)) {
	      // For the undefined case just let the constant pass and
	      // we will handle it in the code generator.
	    if (base_c->value().is_defined()) {
		  long lsv = base_c->value().as_long();
		  long rel_base = 0;

		    // Check whether an unsigned base fits in a 32 bit int.
		    // This ensures correct results for the vlog95 target, and
		    // for the vvp target on LLP64 platforms (Microsoft Windows).
		  if (!base_c->has_sign() && (int32_t)lsv < 0) {
		          // The base is wrapped around.
			delete base;
			if (warn_ob_select) {
			      cerr << get_fileline() << ": warning: " << lv->name();
			      if (lv->word()) cerr << "[]";
			      cerr << "[" << (unsigned long)lsv
				   << (index_tail.sel == index_component_t::SEL_IDX_UP ? "+:" : "-:")
				   << wid << "] is always outside vector." << endl;
			}
			return false;
		  }

		    // Get the signal range.
		  const netranges_t&packed = reg->packed_dims();
		  if (prefix_indices.size()+1 < reg->packed_dims().size()) {
			  // Here we are selecting one or more sub-arrays.
			  // Make this work by finding the indexed sub-arrays and
			  // creating a generated slice that spans the whole range.
			long loff, moff;
			unsigned long lwid, mwid;
			bool lrc, mrc;
			mrc = reg->sb_to_slice(prefix_indices, lsv, moff, mwid);
			if (use_sel == index_component_t::SEL_IDX_UP)
			      lrc = reg->sb_to_slice(prefix_indices, lsv+wid-1, loff, lwid);
			else
			      lrc = reg->sb_to_slice(prefix_indices, lsv-wid+1, loff, lwid);
			if (!mrc || !lrc) {
			      cerr << get_fileline() << ": error: ";
			      cerr << "Part-select [" << lsv;
			      if (index_tail.sel == index_component_t::SEL_IDX_UP) {
				    cerr << "+:";
			      } else {
				    cerr << "-:";
			      }
			      cerr << wid << "] exceeds the declared bounds for ";
			      cerr << reg->name();
			      if (reg->unpacked_dimensions() > 0) cerr << "[]";
			      cerr << "." << endl;
			      des->errors += 1;
			      return 0;
			}
			ivl_assert(*this, lwid == mwid);

			if (moff > loff) {
			      rel_base = loff;
			      wid = moff + mwid - loff;
			} else {
			      rel_base = moff;
			      wid = loff + lwid - moff;
			}
		  } else {
			long offset = 0;
			  // We want the last range, which is where we work.
			const netrange_t&rng = packed.back();
			if (((rng.get_msb() < rng.get_lsb()) &&
			     use_sel == index_component_t::SEL_IDX_UP) ||
			    ((rng.get_msb() > rng.get_lsb()) &&
			     use_sel == index_component_t::SEL_IDX_DO)) {
			      offset = -wid + 1;
			}
			rel_base = reg->sb_to_idx(prefix_indices,lsv) + offset;
		  }
		  delete base;
		  if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
			ivl_assert(*this, reg->coerced_to_uwire());
			if (reg->test_part_driven(rel_base+wid-1, rel_base)) {
			      report_mixed_assignment_conflict_("part select");
			      des->errors += 1;
			      return false;
			}
		  }
		    /* If we cover the entire lvalue just skip the select. */
		  if (rel_base == 0 && wid == reg->vector_width()) return true;
		  base = new NetEConst(verinum(rel_base));
		  if (warn_ob_select) {
			if (rel_base < 0) {
			      cerr << get_fileline() << ": warning: " << reg->name();
			      if (reg->unpacked_dimensions() > 0) cerr << "[]";
			      cerr << "[" << lsv;
			      if (use_sel == index_component_t::SEL_IDX_UP) {
				    cerr << "+:";
			      } else {
				    cerr << "-:";
			      }
			      cerr << wid << "] is selecting before vector." << endl;
			}
			if (rel_base + wid > reg->vector_width()) {
			      cerr << get_fileline() << ": warning: " << reg->name();
			      if (reg->unpacked_dimensions() > 0) cerr << "[]";
			      cerr << "[" << lsv;
			      if (use_sel == index_component_t::SEL_IDX_UP) {
				    cerr << "+:";
			      } else {
				    cerr << "-:";
			      }
			      cerr << wid << "] is selecting after vector." << endl;
			}
		  }
	    } else if (warn_ob_select) {
		  cerr << get_fileline() << ": warning: L-value indexed part "
		       << "select of " << reg->name();
		  if (reg->unpacked_dimensions() > 0) cerr << "[]";
		  cerr << " has an undefined base." << endl;
	    }
      } else {
	    if (need_const_idx) {
		  cerr << get_fileline() << ": error: '" << reg->name()
		       << "' base index must be a constant in this context."
		       << endl;
		  des->errors += 1;
		  return false;
	    }
	    if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
		  ivl_assert(*this, reg->coerced_to_uwire());
		  report_mixed_assignment_conflict_("part select");
		  des->errors += 1;
		  return false;
	    }
	    ivl_assert(*this, prefix_indices.size()+1 == reg->packed_dims().size());
	      /* Correct the mux for the range of the vector. */
	    if (use_sel == index_component_t::SEL_IDX_UP) {
		  base = normalize_variable_part_base(prefix_indices, base,
						      reg, wid, true);
		  sel_type = IVL_SEL_IDX_UP;
	    } else {
		    // This is assumed to be a SEL_IDX_DO.
		  base = normalize_variable_part_base(prefix_indices, base,
						      reg, wid, false);
		  sel_type = IVL_SEL_IDX_DOWN;
	    }
      }

      if (debug_elaborate)
	    cerr << get_fileline() << ": debug: Set part select width="
		 << wid << ", base=" << *base << endl;

      lv->set_part(base, wid, sel_type);

      return true;
}

/*
 * When the l-value turns out to be a class object, this method is
 * called with the bound variable, and the method path. For example,
 * if path_=a.b.c and a.b binds to the variable, then sig is b, and
 * member_path=c. if path_=obj.base.x, and base_path=obj, then sig is
 * obj, and member_path=base.x.
 */
NetAssign_* PEIdent::elaborate_lval_net_class_member_(Design*des, NetScope*scope,
				    const netclass_t *class_type, NetNet*sig,
				    pform_name_t member_path,
				    NetAssign_*initial_lv) const
{
      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
		 << "l-value is property " << member_path
		 << " of " << sig->name();
	    if (initial_lv)
		  cerr << " (with initial_lv, e.g. darray element)";
	    cerr << "." << endl;
      }

      ivl_assert(*this, class_type);

	// Iterate over the member_path. This handles nested class
	// object, by generating nested NetAssign_ object. We start
	// with lv==initial_lv (or 0), so the front of the member_path
	// is the member of the outermost class. If initial_lv is
	// provided (e.g., for darray element access), it's used as the
	// base l-value. Otherwise, we generate an lv from sig. Then
	// iterate over the remaining of the member_path, replacing
	// the outer lv with an lv that nests the lv from the previous
	// iteration.
      NetAssign_*lv = initial_lv;
      do {
	      // Start with the first component of the member path...
	    perm_string method_name = peek_head_name(member_path);
	      // Pull that component from the member_path. We need to
	      // know the current member being worked on, and will
	      // need to know if there are more members to be worked on.
	    name_component_t member_cur = member_path.front();
	    member_path.pop_front();

	    if (debug_elaborate) {
		  cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
		       << "Processing member_cur=" << member_cur
		       << ", class_type=" << (class_type ? class_type->get_name().str() : "NULL")
		       << endl;
	    }

	      // If class_type is null at this point, something went wrong in a previous
	      // iteration. This can happen if we failed to handle a non-class property
	      // type (like virtual interface) that still has more path components.
	    if (!class_type) {
		  cerr << get_fileline() << ": error: "
		       << "Cannot access property " << method_name
		       << " - parent is not a class type." << endl;
		  des->errors += 1;
		  return 0;
	    }

	      // Make sure the property is really present in the class. If
	      // not, then generate an error message and return an error.
	    int pidx = class_type->property_idx_from_name(method_name);
	    if (pidx < 0) {
		  cerr << get_fileline() << ": error: Class " << class_type->get_name()
		       << " does not have a property " << method_name << "." << endl;
		  des->errors += 1;
		  return 0;
	    }

	    property_qualifier_t qual = class_type->get_prop_qual(pidx);
	    if (qual.test_local() && ! class_type->test_scope_is_method(scope)) {
		  cerr << get_fileline() << ": error: "
		       << "Local property " << class_type->get_prop_name(pidx)
		       << " is not accessible (l-value) in this context."
		       << " (scope=" << scope_path(scope) << ")" << endl;
		  des->errors += 1;

	    } else if (qual.test_static()) {

		    // Special case: this is a static property. Ignore the
		    // "this" sig and use the property itself, which is not
		    // part of the sig, as the l-value.
		  NetNet*psig = class_type->find_static_property(method_name);
		  ivl_assert(*this, psig);

		  lv = new NetAssign_(psig);
		  return lv;

	    } else if (qual.test_const()) {
		 if (class_type->get_prop_initialized(pidx)) {
		       cerr << get_fileline() << ": error: "
			    << "Property " << class_type->get_prop_name(pidx)
			    << " is constant in this method."
			    << " (scope=" << scope_path(scope) << ")" << endl;
		       des->errors++;
		 } else if (scope->basename() != "new" && scope->basename() != "new@") {
		       cerr << get_fileline() << ": error: "
			    << "Property " << class_type->get_prop_name(pidx)
			    << " is constant in this method."
			    << " (scope=" << scope_path(scope) << ")" << endl;
		       des->errors++;
		 } else {
			 // Mark this property as initialized. This is used
			 // to know that we have initialized the constant
			 // object so the next assignment will be marked as
			 // illegal.
		       class_type->set_prop_initialized(pidx);

		       if (debug_elaborate) {
			     cerr << get_fileline() << ": PEIdent::elaborate_lval_method_class_member_: "
				  << "Found initializers for property " << class_type->get_prop_name(pidx) << endl;
		       }
		 }
	    }

	    lv = lv? new NetAssign_(lv) : new NetAssign_(sig);
	    lv->set_property(method_name, pidx);

	      // Now get the type of the property.
	    ivl_type_t ptype = class_type->get_prop_type(pidx);
	    NetExpr *canon_index = nullptr;
	    NetExpr *assoc_index = nullptr;
	    if (!member_cur.index.empty()) {
		  if (const netsarray_t *stype = dynamic_cast<const netsarray_t*>(ptype)) {
			canon_index = make_canonical_index(des, scope, this,
							   member_cur.index, stype, false);

		  } else if (const netvector_t *vtype = dynamic_cast<const netvector_t*>(ptype)) {
			// For packed vectors, bit-select is allowed but not yet fully supported
			cerr << get_fileline() << ": warning: "
			     << "Bit-select on class vector property not yet fully supported." << endl;
		  } else if (const netassoc_t *atype = dynamic_cast<const netassoc_t*>(ptype)) {
			// Associative array indexing - elaborate the key expression
			if (member_cur.index.size() != 1) {
			      cerr << get_fileline() << ": error: "
				   << "Associative arrays only support single index." << endl;
			      des->errors++;
			} else {
			      const index_component_t&idx = member_cur.index.front();
			      if (idx.msb && !idx.lsb) {
				    assoc_index = elab_and_eval(des, scope, idx.msb, -1);
			      } else {
				    cerr << get_fileline() << ": error: "
					 << "Invalid index expression for associative array." << endl;
				    des->errors++;
			      }
			}
		  } else if (const netdarray_t *dtype = dynamic_cast<const netdarray_t*>(ptype)) {
			// Dynamic array indexing
			if (member_cur.index.size() == 1) {
			      const index_component_t&idx = member_cur.index.front();
			      if (idx.msb && !idx.lsb) {
				    assoc_index = elab_and_eval(des, scope, idx.msb, -1);
			      } else {
				    cerr << get_fileline() << ": error: "
					 << "Invalid index expression for dynamic array." << endl;
				    des->errors++;
			      }
			} else if (member_cur.index.size() == 2) {
			      // Two indices: arr[i][part-select] or arr[i][bit]
			      const index_component_t&first_idx = member_cur.index.front();
			      const index_component_t&second_idx = member_cur.index.back();

			      // First index must be simple array index
			      if (!first_idx.msb || first_idx.lsb) {
				    cerr << get_fileline() << ": error: "
					 << "First index must be simple expression for dynamic array." << endl;
				    des->errors++;
			      } else {
				    assoc_index = elab_and_eval(des, scope, first_idx.msb, -1);
			      }

			      // Check if second index is a part-select
			      if (second_idx.sel == index_component_t::SEL_IDX_UP ||
				  second_idx.sel == index_component_t::SEL_IDX_DO) {
				    // Indexed part-select: arr[i][base +: width] or arr[i][base -: width]
				    NetExpr* base_expr = elab_and_eval(des, scope, second_idx.msb, -1, false);
				    NetExpr* wid_expr = elab_and_eval(des, scope, second_idx.lsb, -1, true);
				    if (base_expr == 0 || wid_expr == 0) {
					  cerr << get_fileline() << ": error: Failed to elaborate "
					       << "indexed part-select on dynamic array element." << endl;
					  des->errors++;
				    } else {
					  const NetEConst* wid_const = dynamic_cast<const NetEConst*>(wid_expr);
					  if (wid_const == 0) {
						cerr << get_fileline() << ": error: Indexed part-select width "
						     << "must be constant." << endl;
						des->errors++;
					  } else {
						unsigned long wid = wid_const->value().as_ulong();
						ivl_select_type_t sel_type = (second_idx.sel == index_component_t::SEL_IDX_UP)
						      ? IVL_SEL_IDX_UP : IVL_SEL_IDX_DOWN;
						lv->set_part(base_expr, wid, sel_type);

						if (debug_elaborate) {
						      cerr << get_fileline() << ": PEIdent::elaborate_lval_method_class_member_: "
							   << "Added indexed part-select [base "
							   << (second_idx.sel == index_component_t::SEL_IDX_UP ? "+:" : "-:")
							   << " " << wid << "] to darray element." << endl;
						}
					  }
				    }
			      } else if (second_idx.msb && second_idx.lsb) {
				    // Constant part-select: arr[i][msb:lsb]
				    NetExpr* msb_expr = elab_and_eval(des, scope, second_idx.msb, -1, true);
				    NetExpr* lsb_expr = elab_and_eval(des, scope, second_idx.lsb, -1, true);
				    const NetEConst* msb_const = dynamic_cast<const NetEConst*>(msb_expr);
				    const NetEConst* lsb_const = dynamic_cast<const NetEConst*>(lsb_expr);
				    if (msb_const == 0 || lsb_const == 0) {
					  cerr << get_fileline() << ": error: Part-select bounds must "
					       << "be constant." << endl;
					  des->errors++;
				    } else {
					  long msb_val = msb_const->value().as_long();
					  long lsb_val = lsb_const->value().as_long();
					  unsigned long wid = (msb_val >= lsb_val) ? msb_val - lsb_val + 1 : lsb_val - msb_val + 1;
					  long base_val = (msb_val >= lsb_val) ? lsb_val : msb_val;
					  verinum base_ver(base_val);
					  base_ver.has_sign(true);
					  lv->set_part(new NetEConst(base_ver), wid);
				    }
			      } else if (second_idx.msb && !second_idx.lsb) {
				    // Bit-select: arr[i][bit] - treat as 1-bit part-select
				    NetExpr* bit_expr = elab_and_eval(des, scope, second_idx.msb, -1, false);
				    if (bit_expr) {
					  lv->set_part(bit_expr, 1);
				    }
			      } else {
				    cerr << get_fileline() << ": error: "
					 << "Invalid second index expression for dynamic array element." << endl;
				    des->errors++;
			      }
			} else {
			      cerr << get_fileline() << ": error: "
				   << "Dynamic arrays only support single index or index with part-select." << endl;
			      des->errors++;
			}
		  } else {
			cerr << get_fileline() << ": error: "
			     << "Index expressions don't apply to this type of property." << endl;
			des->errors++;
		  }
	    }

	    if (const netuarray_t *tmp_ua = dynamic_cast<const netuarray_t*>(ptype)) {
		  const auto &dims = tmp_ua->static_dimensions();

		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_method_class_member_: "
			     << "Property " << class_type->get_prop_name(pidx)
			     << " has " << dims.size() << " dimensions, "
			     << " got " << member_cur.index.size() << " indices." << endl;
			if (canon_index) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_method_class_member_: "
				   << "Canonical index is:" << *canon_index << endl;
			}
		  }

		  if (dims.size() != member_cur.index.size()) {
			cerr << get_fileline() << ": error: "
			     << "Got " << member_cur.index.size() << " indices, "
			     << "expecting " << dims.size()
			     << " to index the property " << class_type->get_prop_name(pidx) << "." << endl;
			des->errors++;
		  }
	    }

	    if (canon_index)
		  lv->set_word(canon_index);
	    if (assoc_index)
		  lv->set_word(assoc_index);

	      // If the current member is a class object, then get the
	      // type. We may wind up iterating, and need the proper
	      // class type.
	    class_type = dynamic_cast<const netclass_t*>(ptype);

	      // If the property is a dynamic array and was indexed, get the
	      // element type. For dynamic arrays of class objects, we need
	      // the element class type to continue elaboration.
	    if (!class_type && assoc_index) {
		  const netdarray_t *darray = dynamic_cast<const netdarray_t*>(ptype);
		  if (darray) {
			ivl_type_t elem_type = darray->element_type();
			class_type = dynamic_cast<const netclass_t*>(elem_type);
			if (debug_elaborate && class_type) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_method_class_member_: "
				   << "Dynamic array element type is class " << class_type->get_name() << endl;
			}
		  }
	    }

	      // Check if this is a struct-typed property with more path components
	    if (!class_type && !member_path.empty()) {
		  const netstruct_t*struct_type = dynamic_cast<const netstruct_t*>(ptype);
		  if (struct_type) {
			// Struct member access through class property (e.g., obj.struct_prop.member)
			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
				   << "Property " << method_name << " is struct type, member_path="
				   << member_path << endl;
			}

			// Get the struct member name from the remaining path
			name_component_t member_comp = member_path.front();
			member_path.pop_front();
			perm_string member_name = member_comp.name;

			if (struct_type->packed()) {
			      // For packed struct, calculate bit offset
			      unsigned long off = 0;
			      const netstruct_t::member_t* member = struct_type->packed_member(member_name, off);
			      if (!member) {
				    cerr << get_fileline() << ": error: "
					 << "No member '" << member_name << "' in struct type." << endl;
				    des->errors++;
				    return 0;
			      }

			      // Calculate part select width and offset
			      long member_wid = member->net_type->packed_width();
			      NetExpr* off_expr = new NetEConst(verinum(off));

			      // Handle index on packed array member (e.g., pkt.data[i])
			      if (!member_comp.index.empty()) {
				    const netvector_t* mem_vec = dynamic_cast<const netvector_t*>(member->net_type);
				    if (mem_vec && !mem_vec->packed_dims().empty()) {
					  const netranges_t& dims = mem_vec->packed_dims();
					  // Calculate element width (innermost dimension)
					  long elem_wid = 1;
					  if (dims.size() > 1) {
						// Multi-dimensional: element is all but first dimension
						for (size_t d = 1; d < dims.size(); d++) {
						      elem_wid *= dims[d].width();
						}
					  } else {
						elem_wid = 1; // Single dimension means bit select
					  }
					  member_wid = elem_wid;

					  // Get the index expression
					  const index_component_t& idx_comp = member_comp.index.back();
					  NetExpr* idx_expr = elab_and_eval(des, scope, idx_comp.msb, -1, false);
					  if (idx_expr) {
						// Calculate: off + idx * elem_wid
						NetExpr* scaled_idx;
						if (elem_wid == 1) {
						      scaled_idx = idx_expr;
						} else {
						      scaled_idx = new NetEBMult('*', idx_expr,
							    new NetEConst(verinum(elem_wid)),
							    idx_expr->expr_width() + 8, false);
						}
						off_expr = new NetEBAdd('+', off_expr, scaled_idx,
						      off_expr->expr_width() + 8, false);
					  }

					  if (debug_elaborate) {
						cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
						     << "Packed array member indexed access, elem_wid=" << elem_wid << endl;
					  }
				    }
			      }

			      // Set part select for the member
			      lv->set_part(off_expr, member_wid);

			      if (debug_elaborate) {
				    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
					 << "Packed struct member " << member_name
					 << " at offset " << off << ", width " << member_wid << endl;
			      }
			} else {
			      // For unpacked struct, store member index
			      int member_idx = struct_type->member_idx_from_name(member_name);
			      if (member_idx < 0) {
				    cerr << get_fileline() << ": error: "
					 << "No member '" << member_name << "' in struct type." << endl;
				    des->errors++;
				    return 0;
			      }

			      lv->set_struct_member(member_name, member_idx);

			      if (debug_elaborate) {
				    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_class_member_: "
					 << "Unpacked struct member " << member_name
					 << " at index " << member_idx << endl;
			      }
			}

			// Handle nested struct access if more path components remain
			if (!member_path.empty()) {
			      cerr << get_fileline() << ": sorry: "
				   << "Nested struct member access through class property "
				   << "is not yet supported." << endl;
			      des->errors++;
			      return 0;
			}

			return lv;
		  }
	    }

	      // Check if this is a virtual interface property with more path components
	    if (!class_type && !member_path.empty()) {
		  const netvirtual_interface_t*vif_type =
			dynamic_cast<const netvirtual_interface_t*>(ptype);
		  if (vif_type) {
			// Virtual interface member access (vif.member)
			perm_string iface_name = vif_type->interface_name();

			// Get the member name from the path
			name_component_t vif_member_comp = member_path.front();
			member_path.pop_front();

			// Try to get the interface definition from the type
			const NetScope* iface_def = vif_type->interface_def();

			// If not available from type, try to find it by searching scopes
			if (!iface_def) {
			      // Search through all root scopes and their children
			      auto root_scopes = des->find_root_scopes();
			      for (NetScope* root : root_scopes) {
				    iface_def = find_interface_scope_recursive(root, iface_name);
				    if (iface_def) break;
			      }
			}

			// If still not found, try using Module definition to verify member exists
			NetNet* member_sig = nullptr;
			if (iface_def) {
			      // Look up the member signal in the interface scope
			      member_sig = const_cast<NetScope*>(iface_def)->find_signal(vif_member_comp.name);
			}

			if (!member_sig) {
			      // Try to find the member in the Module definition
			      PWire* pwire = find_interface_wire_from_module(iface_name, vif_member_comp.name);
			      if (!pwire) {
				    cerr << get_fileline() << ": error: "
					 << "Interface " << iface_name
					 << " has no member " << vif_member_comp.name << "." << endl;
				    des->errors += 1;
				    return 0;
			      }

			      // Member exists in interface definition, but we need an elaborated
			      // NetNet for the l-value. If no interface instance is found, error.
			      if (!iface_def) {
				    cerr << get_fileline() << ": sorry: "
					 << "Virtual interface member access (."
					 << vif_member_comp.name << ") "
					 << "requires an elaborated interface instance." << endl;
				    des->errors += 1;
				    return 0;
			      }
			}

			if (!member_sig) {
			      cerr << get_fileline() << ": error: "
				   << "Interface " << iface_name
				   << " has no member " << vif_member_comp.name << "." << endl;
			      des->errors += 1;
			      return 0;
			}

			// Set the virtual interface member on the l-value
			lv->set_vif_member(vif_member_comp.name, member_sig);

			// If there are still more path components, error - nested vif member access not supported
			if (!member_path.empty()) {
			      cerr << get_fileline() << ": sorry: "
				   << "Nested virtual interface member access is not yet supported." << endl;
			      des->errors += 1;
			      return 0;
			}

			return lv;
		  }
	    }

      } while (!member_path.empty());


      return lv;
}

/*
 * This method is caled to handle l-value identifiers that are packed
 * structs. The lv is already attached to the variable, so this method
 * calculates the part select that is defined by the member_path. For
 * example, if the path_ is main.sub.sub_local, and the variable is
 * main, then we know at this point that main is a packed struct, and
 * lv contains the reference to the bound variable (main). In this
 * case member_path==sub.sub_local, and it is up to this method to
 * work out the part select that the member_path represents.
 */
bool PEIdent::elaborate_lval_net_packed_member_(Design*des, NetScope*scope,
						NetAssign_*lv,
						pform_name_t member_path,
						bool is_force) const
{
      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
		 << "path_=" << path_
		 << " member_path=" << member_path
		 << endl;
      }

      NetNet*reg = lv->sig();
      ivl_assert(*this, reg);

      const netstruct_t*struct_type = reg->struct_type();
      ivl_assert(*this, struct_type);
      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
		 << "Type=" << *struct_type
		 << endl;
      }

      if (! struct_type->packed()) {
	      // For unpacked structs, delegate to the unpacked member handler
	    return elaborate_lval_net_unpacked_member_(des, scope, lv, member_path, is_force);
      }

	// Looking for the base name. We need that to know about
	// indices we may need to apply. This is to handle the case
	// that the base is an array of structs, and not just a
	// struct.
      pform_name_t::const_reverse_iterator name_idx = path_.name.rbegin();
      for (size_t idx = 1 ; idx < member_path.size() ; idx += 1)
	    ++ name_idx;
      if (name_idx->name != peek_head_name(member_path)) {
	    cerr << get_fileline() << ": internal error: "
		 << "name_idx=" << name_idx->name
		 << ", expecting member_name=" << peek_head_name(member_path)
		 << endl;
	    des->errors += 1;
	    return false;
      }
      ivl_assert(*this, name_idx->name == peek_head_name(member_path));
      ++ name_idx;
      const name_component_t&name_base = *name_idx;

	// Shouldn't be seeing unpacked arrays of packed structs...
      ivl_assert(*this, reg->unpacked_dimensions() == 0);

	// These make up the "part" select that is the equivilent of
	// following the member path through the nested structs. To
	// start with, the off[set] is zero, and use_width is the
	// width of the entire variable. The first member_comp is at
	// some offset within the variable, and will have a reduced
	// width. As we step through the member_path the off
	// increases, and use_width shrinks.
      unsigned long off = 0;
      unsigned long use_width = struct_type->packed_width();
      ivl_type_t member_type;

      pform_name_t completed_path;
      do {
	    const name_component_t member_comp = member_path.front();
	    const perm_string&member_name = member_comp.name;

	    if (debug_elaborate) {
		  cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
		       << "Processing member_comp=" << member_comp
		       << " (completed_path=" << completed_path << ")"
		       << endl;
	    }

	      // This is a packed member, so the name is of the form
	      // "a.b[...].c[...]" which means that the path_ must have at
	      // least 2 components. We are processing "c[...]" at that
	      // point (otherwise known as member_name) and we have a
	      // reference to it in member_comp.

	      // The member_path is the members we want to follow for the
	      // variable. For example, main[N].a.b may have main[N] as the
	      // base_name, and member_path=a.b. The member_name is the
	      // start of the member_path, and is "a". The member_name
	      // should be a member of the struct_type type.

	      // Calculate the offset within the packed structure of the
	      // member, and any indices. We will add in the offset of the
	      // struct into the packed array later. Note that this works
	      // for packed unions as well (although the offset will be 0
	      // for union members).
	    unsigned long tmp_off;
	    const netstruct_t::member_t* member = struct_type->packed_member(member_name, tmp_off);

	    if (member == 0) {
		  cerr << get_fileline() << ": error: Member " << member_name
		       << " is not a member of struct type of "
		       << reg->name()
		       << "." << completed_path << endl;
		  des->errors += 1;
		  return false;
	    }
	    if (debug_elaborate) {
		  cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
		       << "Member type: " << *(member->net_type)
		       << endl;
	    }

	    off += tmp_off;
	    ivl_assert(*this, use_width >= (unsigned long)member->net_type->packed_width());
	    use_width = member->net_type->packed_width();

	      // At this point, off and use_width are the part select
	      // expressed by the member_comp, which is a member of the
	      // struct. We can further refine the part select with any
	      // indices that might be present.

	      // Get the index component type. At this point, we only
	      // support bit select or none.
	    index_component_t::ctype_t use_sel = index_component_t::SEL_NONE;
	    if (!member_comp.index.empty())
		  use_sel = member_comp.index.back().sel;

	    if (use_sel != index_component_t::SEL_NONE
		&& use_sel != index_component_t::SEL_BIT
		&& use_sel != index_component_t::SEL_PART) {
		  cerr << get_fileline() << ": sorry: Assignments to part selects of "
			"a struct member are not yet supported." << endl;
		  des->errors += 1;
		  return false;
	    }

	    member_type = member->net_type;

	    if (const netvector_t*mem_vec = dynamic_cast<const netvector_t*>(member->net_type)) {
		    // If the member type is a netvector_t, then it is a
		    // vector of atom or scaler objects. For example, if the
		    // l-value expression is "foo.member[1][2]",
		    // then the member should be something like:
		    //    ... logic [h:l][m:n] member;
		    // There should be index expressions index the vector
		    // down, but there doesn't need to be all of them. We
		    // can, for example, be selecting a part of the vector.

		    // We only need to process this if there are any
		    // index expressions. If not, then the packed
		    // vector can be handled atomically.

		    // In any case, this should be the tail of the
		    // member_path, because the array element of this
		    // kind of array cannot be a struct.
		  if (!member_comp.index.empty()) {
			  // These are the dimensions defined by the type
			const netranges_t&mem_packed_dims = mem_vec->packed_dims();

			if (member_comp.index.size() > mem_packed_dims.size()) {
			      cerr << get_fileline() << ": error: "
				   << "Too many index expressions for member." << endl;
			      des->errors += 1;
			      return false;
			}

			  // Evaluate all but the last index expression, into prefix_indices.
			list<long>prefix_indices;
			bool rc = evaluate_index_prefix(des, scope, prefix_indices, member_comp.index);
			if (!rc) {
			      // Error already reported by evaluate_index_prefix
			      return false;
			}

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
				   << "prefix_indices.size()==" << prefix_indices.size()
				   << ", mem_packed_dims.size()==" << mem_packed_dims.size()
				   << " (netvector_t context)"
				   << endl;
			}

			  // Try to evaluate the tail index expression.
			  // If it's constant, we can calculate offsets statically.
			  // If not, we need to generate dynamic bit-select code.
			const index_component_t& tail_idx = member_comp.index.back();
			NetExpr* tail_mux = elab_and_eval(des, scope, tail_idx.msb, -1);
			long tail_off = 0;
			unsigned long tail_wid = 1;  // Default for bit-select
			bool tail_is_dynamic = true;

			  // Check if the index is constant
			if (const NetEConst* tail_const = dynamic_cast<NetEConst*>(tail_mux)) {
			      if (tail_const->value().is_defined()) {
				    tail_off = tail_const->value().as_long();
				    tail_is_dynamic = false;
				    delete tail_mux;
				    tail_mux = 0;
			      }
			}

			  // Handle part-select differently (need lsb too)
			if (tail_idx.lsb) {
			      NetExpr* lsb_expr = elab_and_eval(des, scope, tail_idx.lsb, -1);
			      if (const NetEConst* lsb_const = dynamic_cast<NetEConst*>(lsb_expr)) {
				    long lsb_val = lsb_const->value().as_long();
				    if (!tail_is_dynamic) {
					  // Both are constant - calculate width
					  if (tail_off >= lsb_val)
						tail_wid = tail_off - lsb_val + 1;
					  else
						tail_wid = lsb_val - tail_off + 1;
					  tail_off = lsb_val;  // Use lsb as the offset
				    }
			      } else {
				    tail_is_dynamic = true;
			      }
			      delete lsb_expr;
			}

			if (tail_is_dynamic) {
			      if (debug_elaborate) {
				    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
					 << "Dynamic bit-select on struct member, off=" << off
					 << ", use_width=" << use_width
					 << endl;
			      }

			        // Calculate prefix offset first
			      long prefix_loff;
			      unsigned long prefix_lwid;
			      prefix_to_slice(mem_packed_dims, prefix_indices, 0, prefix_loff, prefix_lwid);

			        // The member's base offset within the struct needs to be added to
			        // the dynamic bit-select expression. Create an expression:
			        // member_offset + dynamic_index
			      long total_base = off + prefix_loff;

			        // Create the combined dynamic offset expression
			      NetExpr* base_expr = new NetEConst(verinum(total_base));
			      NetExpr* combined = new NetEBAdd('+', base_expr, tail_mux, 32, true);

			        // For packed struct member bit-select, set up the part with
			        // the dynamic expression for a single bit
			      lv->set_part(combined, tail_wid);

			        // Signal that we've fully handled this member access
			      return true;
			}

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
				   << "Constant bit-select on struct member, tail_off=" << tail_off
				   << ", tail_wid=" << tail_wid
				   << endl;
			}

			  // Now use the prefix_to_slice function to calculate the
			  // offset and width of the addressed slice of the member.
			long loff;
			unsigned long lwid;
			prefix_to_slice(mem_packed_dims, prefix_indices, tail_off, loff, lwid);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
				   << "Calculate loff=" << loff << " lwid=" << lwid
				   << " tail_off=" << tail_off << " tail_wid=" << tail_wid
				   << " off=" << off << " use_width=" << use_width
				   << endl;
			}

			off += loff;
			use_width = lwid * tail_wid;
			member_type = nullptr;
		  }

		    // The netvector_t only has atom elements, to
		    // there is no next struct type.
		  struct_type = 0;

	    } else if (const netparray_t*array = dynamic_cast<const netparray_t*> (member->net_type)) {
		    // If the member is a parray, then the elements
		    // are themselves packed object, including
		    // possibly a struct. Handle this by taking the
		    // part select of the current part of the
		    // variable, then stepping to the element type to
		    // possibly iterate through more of the member_path.

		  ivl_assert(*this, array->packed());

		  if (member_comp.index.empty()) {
			struct_type = 0;
			continue;
		  }

		    // These are the dimensions defined by the type
		  const netranges_t&mem_packed_dims = array->static_dimensions();

		  if (member_comp.index.size() > mem_packed_dims.size()) {
			cerr << get_fileline() << ": error: "
			     << "Too many index expressions for member "
			     << member_name << "." << endl;
			des->errors += 1;
			return false;
		  }

		    // Evaluate all but the last index expression, into prefix_indices.
		  list<long>prefix_indices;
		  bool rc = evaluate_index_prefix(des, scope, prefix_indices, member_comp.index);
		  if (!rc) {
			// Error already reported by evaluate_index_prefix
			return false;
		  }

		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
			     << "prefix_indices.size()==" << prefix_indices.size()
			     << ", mem_packed_dims.size()==" << mem_packed_dims.size()
			     << " (netparray_t context)"
			     << endl;
		  }

		    // Evaluate the last index expression into a constant long.
		  NetExpr*texpr = elab_and_eval(des, scope, member_comp.index.back().msb, -1, true);
		  long tmp;
		  if (texpr == 0 || !eval_as_long(tmp, texpr)) {
			cerr << get_fileline() << ": error: "
			     << "Array index expressions for member " << member_name
			     << " must be constant here." << endl;
			des->errors += 1;
			return false;
		  }

		  delete texpr;

		    // Now use the prefix_to_slice function to calculate the
		    // offset and width of the addressed slice of the member.
		  long loff;
		  unsigned long lwid;
		  prefix_to_slice(mem_packed_dims, prefix_indices, tmp, loff, lwid);

		  ivl_type_t element_type = array->element_type();
		  long element_width = element_type->packed_width();
		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
			     << "parray subselection loff=" << loff
			     << ", lwid=" << lwid
			     << ", element_width=" << element_width
			     << endl;
		  }

		    // The width and offset calculated from the
		    // indices is actually in elements, and not
		    // bits.
		  off += loff * element_width;
		  use_width = lwid * element_width;

		    // To move on to the next component in the member
		    // path, get the element type. For example, for
		    // the path a.b[1].c, we are processing b[1] here,
		    // and the element type should be a netstruct_t
		    // that will wind up containing the member c.
		  struct_type = dynamic_cast<const netstruct_t*> (element_type);

	    } else if (const netstruct_t*tmp_struct = dynamic_cast<const netstruct_t*> (member->net_type)) {
		    // If the member is itself a struct, then get
		    // ready to go on to the next iteration.
		  struct_type = tmp_struct;

	    } else if (const netenum_t*tmp_enum = dynamic_cast<const netenum_t*> (member->net_type)) {
		    // If the element is an enum, then we don't have
		    // anything special to do.
		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
			     << "Tail element is an enum: " << *tmp_enum
			     << endl;
		  }
		  struct_type = 0;

	    } else {
		    // Unknown type?
		  cerr << get_fileline() << ": internal error: "
		       << "Unexpected member type? " << *(member->net_type)
		       << endl;
		  des->errors += 1;
		  return false;
	    }

	      // Complete this component of the path, mark it
	      // completed, and set up for the next component.
	    completed_path .push_back(member_comp);
	    member_path.pop_front();

      } while (!member_path.empty() && struct_type != 0);

      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_packed_member_: "
		 << "After processing member_path, "
		 << "off=" << off
		 << ", use_width=" << use_width
		 << ", completed_path=" << completed_path
		 << ", member_path=" << member_path
		 << endl;
      }

	// The dimensions in the expression must match the packed
	// dimensions that are declared for the variable. For example,
	// if foo is a packed array of struct, then this expression
	// must be "b[n][m]" with the right number of dimensions to
	// match the declaration of "b".
	// Note that one of the packed dimensions is the packed struct
	// itself.
      ivl_assert(*this, name_base.index.size()+1 == reg->packed_dimensions());

	// Generate an expression that takes the input array of
	// expressions and generates a canonical offset into the
	// packed array.
      NetExpr*packed_base = 0;
      if (reg->packed_dimensions() > 1) {
	    list<index_component_t>tmp_index = name_base.index;
	    index_component_t member_select;
	    member_select.sel = index_component_t::SEL_BIT;
	    member_select.msb = new PENumber(new verinum(off));
	    tmp_index.push_back(member_select);
	    packed_base = collapse_array_indices(des, scope, reg, tmp_index);
      }

      long tmp;
      if (packed_base && eval_as_long(tmp, packed_base)) {
	    off = tmp;
	    delete packed_base;
	    packed_base = 0;
      }

      if ((reg->type()==NetNet::UNRESOLVED_WIRE) && !is_force) {
	    ivl_assert(*this, reg->coerced_to_uwire());
	    report_mixed_assignment_conflict_("variable");
	    des->errors += 1;
	    return false;
      }

      if (packed_base == 0) {
	    NetExpr *base = new NetEConst(verinum(off));
	    if (member_type)
		  lv->set_part(base, member_type);
	    else
		  lv->set_part(base, use_width);
	    return true;
      }

	// Oops, packed_base is not fully evaluated, so I don't know
	// yet what to do with it.
      cerr << get_fileline() << ": internal error: "
	   << "I don't know how to handle this index expression? " << *packed_base << endl;
      ivl_assert(*this, 0);
      return false;
}

/*
 * Handle l-value member access for unpacked structs.
 * Unlike packed structs where we calculate bit offsets, for unpacked
 * structs we store the member index and use per-member storage at runtime.
 */
bool PEIdent::elaborate_lval_net_unpacked_member_(Design*des, NetScope*scope,
						  NetAssign_*lv,
						  pform_name_t member_path,
						  bool is_force) const
{
      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
		 << "path_=" << path_
		 << " member_path=" << member_path
		 << endl;
      }

      NetNet*reg = lv->sig();
      ivl_assert(*this, reg);

      const netstruct_t*struct_type = reg->struct_type();
      ivl_assert(*this, struct_type);
      ivl_assert(*this, !struct_type->packed());

      if (is_force) {
	    cerr << get_fileline() << ": error: Cannot force/release "
		 << "unpacked struct members." << endl;
	    des->errors += 1;
	    return false;
      }

	// For now, only support single-level member access (no nested structs)
      if (member_path.size() != 1) {
	    cerr << get_fileline() << ": sorry: Nested unpacked struct "
		 << "member access not yet supported." << endl;
	    des->errors += 1;
	    return false;
      }

      const name_component_t& member_comp = member_path.front();
      const perm_string& member_name = member_comp.name;

	// Look up the member by name
      int member_idx = struct_type->member_idx_from_name(member_name);
      if (member_idx < 0) {
	    cerr << get_fileline() << ": error: "
		 << "No member '" << member_name << "' in struct type." << endl;
	    des->errors += 1;
	    return false;
      }

      const netstruct_t::member_t* member = struct_type->get_member(member_idx);
      ivl_assert(*this, member);

	// Store the struct member information in the l-value
      lv->set_struct_member(member_name, member_idx);

      if (debug_elaborate) {
	    cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
		 << "Found member '" << member_name << "' at index " << member_idx
		 << ", type=" << *(member->net_type)
		 << ", has_index=" << (!member_comp.index.empty())
		 << endl;
      }

	// Handle indexed access to packed member of unpacked struct
	// e.g., my_struct.packed_member[bit_idx] = value
	// or my_struct.packed_2d_member[i][j] = value
      if (!member_comp.index.empty()) {
	    const netvector_t* vec_type = dynamic_cast<const netvector_t*>(member->net_type);
	    if (vec_type && vec_type->packed()) {
		    // Member is a packed vector - handle bit/part select
		  const index_component_t& idx_comp = member_comp.index.back();

		    // Handle multi-dimensional indexed access to packed struct members
		  if (member_comp.index.size() > 1 && idx_comp.sel == index_component_t::SEL_BIT) {
			  // Multi-dimensional bit select: member[i][j]
			  // Compute the canonical offset for all indices
			const netranges_t& pdims = vec_type->packed_dims();
			if (member_comp.index.size() != pdims.size()) {
			      cerr << get_fileline() << ": error: "
				   << "Number of indices doesn't match packed dimensions." << endl;
			      des->errors += 1;
			      return false;
			}

			  // Build the base expression: sum of (normalized_index * stride)
			NetExpr* base_expr = 0;
			auto pdim_it = pdims.begin();
			auto idx_it = member_comp.index.begin();
			unsigned long stride = vec_type->packed_width();

			for (size_t i = 0; i < member_comp.index.size(); ++i, ++pdim_it, ++idx_it) {
			      stride /= pdim_it->width();
			      NetExpr* idx_expr = elab_and_eval(des, scope, idx_it->msb, -1, false);
			      if (idx_expr == 0) {
				    cerr << get_fileline() << ": error: "
					 << "Failed to elaborate index expression." << endl;
				    des->errors += 1;
				    return false;
			      }

				// Normalize index by subtracting lsb
			      long lsb = pdim_it->get_lsb();
			      if (lsb != 0) {
				    NetEConst* lsb_c = new NetEConst(verinum(-lsb));
				    lsb_c->set_line(*this);
				    idx_expr = new NetEBAdd('+', idx_expr, lsb_c,
				                            idx_expr->expr_width(), true);
				    idx_expr->set_line(*this);
			      }

				// Multiply by stride
			      if (stride > 1) {
				    NetEConst* stride_c = new NetEConst(verinum((long)stride));
				    stride_c->set_line(*this);
				    idx_expr = new NetEBMult('*', idx_expr, stride_c,
				                             idx_expr->expr_width() + 16, false);
				    idx_expr->set_line(*this);
			      }

				// Add to accumulated base
			      if (base_expr) {
				    base_expr = new NetEBAdd('+', base_expr, idx_expr,
				                             base_expr->expr_width(), false);
				    base_expr->set_line(*this);
			      } else {
				    base_expr = idx_expr;
			      }
			}

			if (!base_expr) {
			      base_expr = new NetEConst(verinum(0L));
			      base_expr->set_line(*this);
			}

			lv->set_part(base_expr, 1);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
				   << "Added multi-dimensional bit-select to member '" << member_name << "'"
				   << endl;
			}
		  } else if (member_comp.index.size() == 1 && idx_comp.sel == index_component_t::SEL_BIT) {
			  // Single-dimensional select: member[idx]
			  // For 2D+ packed arrays, this selects a slice (e.g., data[0] on bit [3:0][7:0])
			const netranges_t& pdims = vec_type->packed_dims();
			NetExpr* idx_expr = elab_and_eval(des, scope, idx_comp.msb, -1, false);
			if (idx_expr == 0) {
			      cerr << get_fileline() << ": error: Failed to elaborate "
				   << "bit-select index." << endl;
			      des->errors += 1;
			      return false;
			}

			  // Calculate width and stride based on remaining dimensions
			unsigned long part_width = 1;
			if (pdims.size() > 1) {
			      // For multi-dimensional packed arrays, remaining dims contribute to width
			      // e.g., for bit [3:0][7:0], accessing [i] gives width 8
			      auto pdim_it = pdims.begin();
			      ++pdim_it; // Skip first dimension (the one we're indexing)
			      while (pdim_it != pdims.end()) {
				    part_width *= pdim_it->width();
				    ++pdim_it;
			      }
			}

			  // Compute offset: index * part_width
			if (part_width > 1) {
			      // Normalize index by outer dimension lsb
			      long lsb = pdims.front().get_lsb();
			      if (lsb != 0) {
				    NetEConst* lsb_c = new NetEConst(verinum(-lsb));
				    lsb_c->set_line(*this);
				    idx_expr = new NetEBAdd('+', idx_expr, lsb_c,
				                            idx_expr->expr_width(), true);
				    idx_expr->set_line(*this);
			      }
			      NetEConst* stride_c = new NetEConst(verinum((long)part_width));
			      stride_c->set_line(*this);
			      idx_expr = new NetEBMult('*', idx_expr, stride_c,
			                              idx_expr->expr_width() + 16, false);
			      idx_expr->set_line(*this);
			}

			lv->set_part(idx_expr, part_width);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
				   << "Added index-select to member '" << member_name << "'"
				   << ", width=" << part_width
				   << endl;
			}
		  } else if (member_comp.index.size() > 1 && idx_comp.sel == index_component_t::SEL_PART) {
			  // Multi-dimensional with part select: member[i][3:0]
			  // Compute the base for prefix indices, then add part select offset
			const netranges_t& pdims = vec_type->packed_dims();
			if (member_comp.index.size() > pdims.size()) {
			      cerr << get_fileline() << ": error: "
				   << "Too many indices for packed dimensions." << endl;
			      des->errors += 1;
			      return false;
			}

			  // Build the base expression for prefix indices
			NetExpr* base_expr = 0;
			auto pdim_it = pdims.begin();
			auto idx_it = member_comp.index.begin();
			unsigned long stride = vec_type->packed_width();
			size_t prefix_count = member_comp.index.size() - 1;

			for (size_t i = 0; i < prefix_count; ++i, ++pdim_it, ++idx_it) {
			      stride /= pdim_it->width();
			      NetExpr* idx_expr = elab_and_eval(des, scope, idx_it->msb, -1, false);
			      if (idx_expr == 0) {
				    cerr << get_fileline() << ": error: "
					 << "Failed to elaborate index expression." << endl;
				    des->errors += 1;
				    return false;
			      }

				// Normalize index by subtracting lsb
			      long lsb = pdim_it->get_lsb();
			      if (lsb != 0) {
				    NetEConst* lsb_c = new NetEConst(verinum(-lsb));
				    lsb_c->set_line(*this);
				    idx_expr = new NetEBAdd('+', idx_expr, lsb_c,
				                            idx_expr->expr_width(), true);
				    idx_expr->set_line(*this);
			      }

				// Multiply by stride
			      if (stride > 1) {
				    NetEConst* stride_c = new NetEConst(verinum((long)stride));
				    stride_c->set_line(*this);
				    idx_expr = new NetEBMult('*', idx_expr, stride_c,
				                             idx_expr->expr_width() + 16, false);
				    idx_expr->set_line(*this);
			      }

				// Add to accumulated base
			      if (base_expr) {
				    base_expr = new NetEBAdd('+', base_expr, idx_expr,
				                             base_expr->expr_width(), false);
				    base_expr->set_line(*this);
			      } else {
				    base_expr = idx_expr;
			      }
			}

			if (!base_expr) {
			      base_expr = new NetEConst(verinum(0L));
			      base_expr->set_line(*this);
			}

			  // Get the part select range
			NetExpr* msb_expr = elab_and_eval(des, scope, idx_comp.msb, -1, true);
			NetExpr* lsb_expr = elab_and_eval(des, scope, idx_comp.lsb, -1, true);
			if (msb_expr == 0 || lsb_expr == 0) {
			      cerr << get_fileline() << ": error: Failed to elaborate "
				   << "part-select bounds." << endl;
			      des->errors += 1;
			      return false;
			}
			const NetEConst* msb_const = dynamic_cast<const NetEConst*>(msb_expr);
			const NetEConst* lsb_const = dynamic_cast<const NetEConst*>(lsb_expr);
			if (msb_const == 0 || lsb_const == 0) {
			      cerr << get_fileline() << ": error: Part-select bounds must "
				   << "be constant." << endl;
			      des->errors += 1;
			      return false;
			}
			long msb_val = msb_const->value().as_long();
			long lsb_val = lsb_const->value().as_long();
			unsigned long wid = (msb_val >= lsb_val) ? msb_val - lsb_val + 1 : lsb_val - msb_val + 1;
			long base_off = (msb_val >= lsb_val) ? lsb_val : msb_val;

			  // Add part select offset to base expression
			if (base_off != 0) {
			      NetEConst* off_c = new NetEConst(verinum(base_off));
			      off_c->set_line(*this);
			      base_expr = new NetEBAdd('+', base_expr, off_c,
			                               base_expr->expr_width(), false);
			      base_expr->set_line(*this);
			}

			lv->set_part(base_expr, wid);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
				   << "Added multi-dimensional part-select to member '" << member_name << "'"
				   << endl;
			}
		  } else if (member_comp.index.size() == 1 && idx_comp.sel == index_component_t::SEL_PART) {
			  // Constant part-select: member[msb:lsb]
			NetExpr* msb_expr = elab_and_eval(des, scope, idx_comp.msb, -1, true);
			NetExpr* lsb_expr = elab_and_eval(des, scope, idx_comp.lsb, -1, true);
			if (msb_expr == 0 || lsb_expr == 0) {
			      cerr << get_fileline() << ": error: Failed to elaborate "
				   << "part-select bounds." << endl;
			      des->errors += 1;
			      return false;
			}
			const NetEConst* msb_const = dynamic_cast<const NetEConst*>(msb_expr);
			const NetEConst* lsb_const = dynamic_cast<const NetEConst*>(lsb_expr);
			if (msb_const == 0 || lsb_const == 0) {
			      cerr << get_fileline() << ": error: Part-select bounds must "
				   << "be constant." << endl;
			      des->errors += 1;
			      return false;
			}
			long msb_val = msb_const->value().as_long();
			long lsb_val = lsb_const->value().as_long();
			unsigned long wid = (msb_val >= lsb_val) ? msb_val - lsb_val + 1 : lsb_val - msb_val + 1;
			long base_val = (msb_val >= lsb_val) ? lsb_val : msb_val;
			verinum base_ver(base_val);
			base_ver.has_sign(true);
			lv->set_part(new NetEConst(base_ver), wid);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
				   << "Added part-select [" << msb_val << ":" << lsb_val
				   << "] to member '" << member_name << "'" << endl;
			}
		  } else if (idx_comp.sel == index_component_t::SEL_IDX_UP ||
			     idx_comp.sel == index_component_t::SEL_IDX_DO) {
			  // Indexed part-select: member[base +: width] or member[base -: width]
			NetExpr* base_expr = elab_and_eval(des, scope, idx_comp.msb, -1, false);
			NetExpr* wid_expr = elab_and_eval(des, scope, idx_comp.lsb, -1, true);
			if (base_expr == 0 || wid_expr == 0) {
			      cerr << get_fileline() << ": error: Failed to elaborate "
				   << "indexed part-select." << endl;
			      des->errors += 1;
			      return false;
			}
			const NetEConst* wid_const = dynamic_cast<const NetEConst*>(wid_expr);
			if (wid_const == 0) {
			      cerr << get_fileline() << ": error: Indexed part-select width "
				   << "must be constant." << endl;
			      des->errors += 1;
			      return false;
			}
			unsigned long wid = wid_const->value().as_ulong();
			ivl_select_type_t sel_type = (idx_comp.sel == index_component_t::SEL_IDX_UP)
			      ? IVL_SEL_IDX_UP : IVL_SEL_IDX_DOWN;
			lv->set_part(base_expr, wid, sel_type);

			if (debug_elaborate) {
			      cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
				   << "Added indexed part-select to member '" << member_name << "'"
				   << endl;
			}
		  } else {
			cerr << get_fileline() << ": sorry: Unsupported select type on struct "
			     << "member." << endl;
			des->errors += 1;
			return false;
		  }
	    } else if (const netuarray_t* uarray = dynamic_cast<const netuarray_t*>(member->net_type)) {
		    // Member is an unpacked array - handle array indexing
		    // e.g., my_struct.arr[i] where arr is bit[31:0] arr[4]
		  const netranges_t& dims = uarray->static_dimensions();

		  if (member_comp.index.size() > dims.size()) {
			cerr << get_fileline() << ": error: "
			     << "Too many indices for unpacked array member "
			     << member_name << "." << endl;
			des->errors += 1;
			return false;
		  }

		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
			     << "Member '" << member_name << "' is netuarray_t with "
			     << dims.size() << " dimensions, got " << member_comp.index.size()
			     << " indices." << endl;
		  }

		    // Create canonical index for the unpacked array
		  NetExpr* canon_index = make_canonical_index(des, scope, this,
							      member_comp.index,
							      uarray, false);
		  if (canon_index == 0) {
			cerr << get_fileline() << ": error: "
			     << "Failed to elaborate array index for member "
			     << member_name << "." << endl;
			des->errors += 1;
			return false;
		  }

		    // Set the word index for the array access
		  lv->set_word(canon_index);

		  if (debug_elaborate) {
			cerr << get_fileline() << ": PEIdent::elaborate_lval_net_unpacked_member_: "
			     << "Set word index=" << *canon_index
			     << " for unpacked array member '" << member_name << "'" << endl;
		  }

	    } else {
		    // Member is not a packed vector or unpacked array - can't do indexed access
		  cerr << get_fileline() << ": sorry: Indexed access to non-packed "
		       << "struct members not yet supported (type: "
		       << typeid(*(member->net_type)).name() << ")." << endl;
		  des->errors += 1;
		  return false;
	    }
      }

      return true;
}

NetAssign_* PENumber::elaborate_lval(Design*des, NetScope*, bool, bool, bool) const
{
      cerr << get_fileline() << ": error: Constant values not allowed "
	   << "in l-value expressions." << endl;
      des->errors += 1;
      return 0;
}
