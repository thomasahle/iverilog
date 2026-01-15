/*
 * Copyright (c) 2012-2017 Stephen Williams (steve@icarus.com)
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

# include  "netclass.h"
# include  "netlist.h"
# include  "PClass.h"
# include  "PTask.h"
# include  "compiler.h"
# include  <iostream>

using namespace std;

netclass_t::netclass_t(perm_string name, const netclass_t*super)
: name_(name), super_(super), class_scope_(0), definition_scope_(0), virtual_class_(false), pclass_(0)
{
}

netclass_t::~netclass_t()
{
}

bool netclass_t::set_property(perm_string pname, property_qualifier_t qual,
			      ivl_type_t ptype)
{
      map<perm_string,size_t>::const_iterator cur;
      cur = properties_.find(pname);
      if (cur != properties_.end())
	    return false;

      prop_t tmp;
      tmp.name = pname;
      tmp.qual = qual;
      tmp.type = ptype;
      tmp.initialized_flag = false;
      property_table_.push_back(tmp);

      properties_[pname] = property_table_.size()-1;
      return true;
}

void netclass_t::set_property_type_override(perm_string pname, ivl_type_t ptype)
{
      // Store a specialized type for a property that will exist in the parent.
      // This is used by parameterized class specializations to provide
      // specialized types while keeping the same property indices.
      overridden_prop_types_[pname] = ptype;
}

void netclass_t::set_type_param_override(perm_string param_name, ivl_type_t type)
{
      type_param_overrides_[param_name] = type;
}

void netclass_t::set_value_param_override(perm_string param_name)
{
      (void)param_name;
      has_value_param_overrides_ = true;
}

bool netclass_t::get_type_param_override(perm_string param_name, ivl_type_t &type) const
{
      auto it = type_param_overrides_.find(param_name);
      if (it != type_param_overrides_.end()) {
	    type = it->second;
	    return true;
      }
      return false;
}

NetScope* netclass_t::get_specialized_method(perm_string method_name) const
{
      auto it = specialized_method_scopes_.find(method_name);
      if (it != specialized_method_scopes_.end())
	    return it->second;
      return nullptr;
}

void netclass_t::set_specialized_method(perm_string method_name, NetScope* scope) const
{
      specialized_method_scopes_[method_name] = scope;
}

bool netclass_t::has_class_type_property_overrides() const
{
      // Check if any PROPERTY type overrides are class types.
      // This is different from checking type_param_overrides_ because:
      // - type_param_overrides_ tracks what type T became (e.g., T=MyClass)
      // - overridden_prop_types_ tracks what the actual property types are
      //
      // A class like Container#(Item) has:
      //   - type_param_overrides_["T"] = Item (class type)
      //   - overridden_prop_types_["data"] = Item (class type) because data is of type T
      //
      // A class like uvm_tlm_fifo#(axi4_tx) has:
      //   - type_param_overrides_["T"] = axi4_tx (class type)
      //   - NO class-type property overrides (m_count is int, etc.)
      //
      // We only need to re-elaborate methods if they might store class objects
      // to class properties.
      for (auto const& override_pair : overridden_prop_types_) {
            ivl_type_t prop_type = override_pair.second;
            if (prop_type && prop_type->base_type() == IVL_VT_CLASS) {
                  return true;
            }
      }
      return false;
}

bool netclass_t::has_class_type_param_overrides() const
{
      // Check if any type parameter override is a class type.
      // This catches cases like uvm_tlm_analysis_fifo#(my_transaction) where:
      //   - T = my_transaction (a class type)
      //   - Methods might have local variables of type T (e.g., "T item;" in $cast)
      // These methods need re-elaboration even if no PROPERTY is of class type.
      for (auto const& override_pair : type_param_overrides_) {
            ivl_type_t param_type = override_pair.second;
            if (param_type && param_type->base_type() == IVL_VT_CLASS) {
                  return true;
            }
      }
      return false;
}

NetScope* netclass_t::get_method_for_call(Design* des, perm_string method_name) const
{
      // Always use the inherited method first. Only do re-elaboration for
      // specialized parameterized classes that have methods using type parameters.
      // For most classes (including UVM TLM classes), the inherited methods work fine.
      NetScope* inherited = method_from_name(method_name);

      // If not a specialized class, or if we don't have an inherited method,
      // just return whatever we have
      if (!inherited) {
	    return inherited;
      }
      if (!has_type_param_overrides() && !has_value_param_overrides()) {
	    return inherited;
      }

      // DEBUG: Check what's happening
      if (debug_elaborate) {
	    cerr << "get_method_for_call: class=" << get_name()
	         << " method=" << method_name
	         << " has_type_param_overrides=" << has_type_param_overrides()
	         << " has_value_param_overrides=" << has_value_param_overrides()
	         << " has_class_type_property_overrides=" << has_class_type_property_overrides()
	         << " has_class_type_param_overrides=" << has_class_type_param_overrides()
	         << " class_scope_=" << (class_scope_ ? "set" : "null")
	         << endl;
      }

      // For specialized parameterized classes, check if the class has any PROPERTY
      // type overrides that are class types, OR if any type parameter override
      // is a class type. Methods need re-elaboration when:
      //
      // 1. Properties are class types: methods may store/load class objects to properties
      //    e.g., Container#(Item) has "T data" property
      //
      // 2. Type parameters are class types: methods may declare local variables of type T
      //    e.g., uvm_tlm_analysis_fifo#(my_transaction).tlm_write has "T item" local var
      //    This is needed for $cast(item, t) to work correctly with the specialized type
      //
      // If neither condition is true, the inherited methods work fine.
      if (!has_value_param_overrides()
          && !has_class_type_property_overrides()
          && !has_class_type_param_overrides()) {
	    return inherited;
      }

      // We have class-typed property overrides. Check if we can safely re-elaborate.
      // We need a valid class_scope_ to create the re-elaborated method in.
      if (!class_scope_) {
	    // No class scope - can't re-elaborate, use inherited
	    if (debug_elaborate) {
		  cerr << "get_method_for_call: class_scope_ is null, using inherited" << endl;
	    }
	    return inherited;
      }

      // Check cache first
      NetScope* cached = get_specialized_method(method_name);
      if (cached) {
	    return cached;
      }

      // We need to re-elaborate the method with specialized types.
      // Get the PClass from the base class (specialized classes inherit from template)
      PClass* pclass = nullptr;
      for (const netclass_t* c = super_; c && !pclass; c = c->get_super()) {
	    pclass = c->get_pclass();
      }

      if (!pclass) {
	    // Fall back to inherited method if we can't find PClass
	    return inherited;
      }

      // Find the task or function definition
      PTask* ptask = nullptr;
      PFunction* pfunc = nullptr;
      auto task_it = pclass->tasks.find(method_name);
      if (task_it != pclass->tasks.end()) {
	    ptask = task_it->second;
      } else {
	    auto func_it = pclass->funcs.find(method_name);
	    if (func_it != pclass->funcs.end()) {
		  pfunc = func_it->second;
	    }
      }

      if (!ptask && !pfunc) {
	    // Method not found in PClass, use inherited
	    return inherited;
      }

      // Create a new method scope as a child of this (specialized) class scope.
      // The type parameters will be found via the type_param_overrides_ lookup
      // in type_parameter_t::elaborate_type_raw().
      hname_t use_name(method_name);
      NetScope* method_scope = nullptr;

      // Save and reset the in_fork state. Method bodies are not actually inside
      // fork blocks even if the method CALL is. The in_fork counter is used to
      // check that return statements aren't inside fork blocks, but a called
      // method is a separate scope that can have return statements.
      unsigned saved_in_fork = des->in_fork;
      des->in_fork = 0;

      if (ptask) {
	    method_scope = new NetScope(class_scope_, use_name, NetScope::TASK);
	    method_scope->is_auto(true);
	    method_scope->is_virtual(ptask->is_virtual());
	    method_scope->set_line(ptask);
	    method_scope->add_imports(&ptask->explicit_imports);

	    ptask->elaborate_scope(des, method_scope);
	    ptask->elaborate_sig(des, method_scope);
	    ptask->elaborate(des, method_scope);
      } else {
	    method_scope = new NetScope(class_scope_, use_name, NetScope::FUNC);
	    method_scope->is_auto(true);
	    method_scope->is_virtual(pfunc->is_virtual());
	    method_scope->set_line(pfunc);
	    method_scope->add_imports(&pfunc->explicit_imports);

	    pfunc->elaborate_scope(des, method_scope);
	    pfunc->elaborate_sig(des, method_scope);
	    pfunc->elaborate(des, method_scope);
      }

      // Restore in_fork state
      des->in_fork = saved_in_fork;

      // Cache the specialized method
      set_specialized_method(method_name, method_scope);

      return method_scope;
}

void netclass_t::set_class_scope(NetScope*class_scope__)
{
      assert(class_scope_ == 0);
      class_scope_ = class_scope__;
}

void netclass_t::set_definition_scope(NetScope*use_definition_scope)
{
      assert(definition_scope_ == 0);
      definition_scope_ = use_definition_scope;
}

ivl_variable_type_t netclass_t::base_type() const
{
      return IVL_VT_CLASS;
}

/*
 * Two classes are considered equivalent if they have the same name.
 * This is important for parameterized class specializations, where
 * multiple instances of the same specialization may be created but
 * should be considered equivalent types.
 */
bool netclass_t::test_equivalence(ivl_type_t that) const
{
      const netclass_t*that_class = dynamic_cast<const netclass_t*>(that);
      if (that_class == nullptr)
	    return false;

      return name_ == that_class->name_;
}

size_t netclass_t::get_properties(void) const
{
      size_t res = properties_.size();
      if (super_) res += super_->get_properties();
      return res;
}

int netclass_t::property_idx_from_name(perm_string pname) const
{
      map<perm_string,size_t>::const_iterator cur;
      cur = properties_.find(pname);
      if (cur == properties_.end()) {
	    if (super_)
		  return super_->property_idx_from_name(pname);
	    else
		  return -1;
      }

      int pidx = cur->second;
      if (super_) pidx += super_->get_properties();
      return pidx;
}

const char*netclass_t::get_prop_name(size_t idx) const
{
      size_t super_size = 0;
      if (super_) super_size = super_->get_properties();

      assert(idx < (super_size + property_table_.size()));
      if (idx < super_size)
	    return super_->get_prop_name(idx);
      else
	    return property_table_[idx-super_size].name;
}

property_qualifier_t netclass_t::get_prop_qual(size_t idx) const
{
      size_t super_size = 0;
      if (super_) super_size = super_->get_properties();

      assert(idx < (super_size+property_table_.size()));
      if (idx < super_size)
	    return super_->get_prop_qual(idx);
      else
	    return property_table_[idx-super_size].qual;
}

ivl_type_t netclass_t::get_prop_type(size_t idx) const
{
      size_t super_size = 0;
      if (super_) super_size = super_->get_properties();

      assert(idx < (super_size+property_table_.size()));
      if (idx < super_size) {
	    // Check if we have an overridden type for this parent property.
	    // This is used by parameterized class specializations to provide
	    // specialized types while keeping the same property indices.
	    const char* pname = super_->get_prop_name(idx);
	    if (pname) {
		  auto it = overridden_prop_types_.find(perm_string::literal(pname));
		  if (it != overridden_prop_types_.end()) {
			return it->second;
		  }
	    }
	    return super_->get_prop_type(idx);
      } else {
	    return property_table_[idx-super_size].type;
      }
}

bool netclass_t::get_prop_initialized(size_t idx) const
{
      size_t super_size = 0;
      if (super_) super_size = super_->get_properties();

      assert(idx < (super_size+property_table_.size()));
      if (idx < super_size)
	    return super_->get_prop_initialized(idx);
      else
	    return property_table_[idx].initialized_flag;
}

void netclass_t::set_prop_initialized(size_t idx) const
{
      size_t super_size = 0;
      if (super_) super_size = super_->get_properties();

      assert(idx >= super_size && idx < (super_size+property_table_.size()));
      idx -= super_size;

      assert(! property_table_[idx].initialized_flag);
      property_table_[idx].initialized_flag = true;
}

bool netclass_t::test_for_missing_initializers() const
{
      for (size_t idx = 0 ; idx < property_table_.size() ; idx += 1) {
	    if (property_table_[idx].initialized_flag)
		  continue;
	    if (property_table_[idx].qual.test_const())
		  return true;
      }

      return false;
}

NetScope*netclass_t::method_from_name(perm_string name) const
{
      NetScope*task = class_scope_->child( hname_t(name) );
      if ((task == 0) && super_)
	    task = super_->method_from_name(name);
      return task;

}

NetScope* netclass_t::get_constructor() const
{
      auto task = class_scope_->child(hname_t(perm_string::literal("new")));
      if (task)
	    return task;

      task = class_scope_->child(hname_t(perm_string::literal("new@")));
      if (task)
	    return task;

      if (super_)
	    return super_->get_constructor();

      return nullptr;
}

NetNet* netclass_t::find_static_property(perm_string name) const
{
      NetNet *net = class_scope_->find_signal(name);
      if (net)
	    return net;

      if (super_)
	    return super_->find_static_property(name);

      return nullptr;
}

bool netclass_t::test_scope_is_method(const NetScope*scope) const
{
      while (scope && scope != class_scope_) {
	    scope = scope->parent();
      }

      if (scope == 0)
	    return false;
      else
	    return true;
}

const NetExpr* netclass_t::get_parameter(Design *des, perm_string name,
					 ivl_type_t &par_type) const
{
      return class_scope_->get_parameter(des, name, par_type);
}

bool netclass_t::test_compatibility(ivl_type_t that) const
{
      for (const netclass_t *class_type = dynamic_cast<const netclass_t *>(that);
	    class_type; class_type = class_type->get_super()) {
	    // Use test_equivalence instead of pointer comparison to handle
	    // different instances of the same parameterized class specialization
	    if (test_equivalence(class_type))
		  return true;
      }

      return false;
}

/*
 * Constraint support methods for SystemVerilog constrained randomization.
 */
void netclass_t::add_constraint(perm_string name, bool is_soft, NetExpr* expr)
{
      constraint_t tmp;
      tmp.name = name;
      tmp.is_soft = is_soft;
      tmp.expr = expr;
      constraints_.push_back(tmp);
}

perm_string netclass_t::get_constraint_name(size_t idx) const
{
      assert(idx < constraints_.size());
      return constraints_[idx].name;
}

bool netclass_t::get_constraint_soft(size_t idx) const
{
      assert(idx < constraints_.size());
      return constraints_[idx].is_soft;
}

NetExpr* netclass_t::get_constraint_expr(size_t idx) const
{
      assert(idx < constraints_.size());
      return constraints_[idx].expr;
}

/*
 * Simple bounds are extracted from constraint expressions during elaboration.
 * They represent efficient runtime-checkable bounds like: value > 0, value < limit
 */
void netclass_t::add_simple_bound(perm_string constraint_name, size_t prop_idx, char op, bool is_soft,
                                  bool has_const, int64_t const_val, size_t bound_prop,
                                  sysfunc_type_t sysfunc, size_t sysfunc_arg,
                                  int64_t weight, bool weight_per_value,
                                  bool has_cond, size_t cond_prop, char cond_op,
                                  bool cond_has_const, int64_t cond_const, size_t cond_prop2,
                                  bool is_foreach, size_t array_size, bool has_prop_offset)
{
      simple_bound_t bound;
      bound.constraint_name = constraint_name;
      bound.property_idx = prop_idx;
      bound.op = op;
      bound.is_soft = is_soft;
      bound.has_const_bound = has_const;
      bound.const_bound = const_val;
      bound.bound_prop_idx = bound_prop;
      // has_prop_offset is true when we have both a constant offset AND a property reference
      bound.has_prop_offset = has_prop_offset;
      bound.is_foreach = is_foreach;
      bound.array_size = array_size;
      bound.sysfunc_type = sysfunc;
      bound.sysfunc_arg_idx = sysfunc_arg;
      bound.weight = weight;
      bound.weight_per_value = weight_per_value;
      bound.has_condition = has_cond;
      bound.cond_prop_idx = cond_prop;
      bound.cond_op = cond_op;
      bound.cond_has_const = cond_has_const;
      bound.cond_const = cond_const;
      bound.cond_prop2_idx = cond_prop2;
      bound.is_excluded_range = false;
      bound.excluded_range_low = 0;
      bound.excluded_range_high = 0;
      bound.has_element_idx = false;
      bound.element_idx = 0;
      simple_bounds_.push_back(bound);
}

void netclass_t::add_excluded_range_bound(perm_string constraint_name, size_t prop_idx,
                                          int64_t low_bound, int64_t high_bound, bool is_soft)
{
      simple_bound_t bound;
      bound.constraint_name = constraint_name;
      bound.property_idx = prop_idx;
      bound.op = 'R';  // Excluded range operator
      bound.is_soft = is_soft;
      bound.has_const_bound = false;
      bound.const_bound = 0;
      bound.bound_prop_idx = 0;
      bound.has_prop_offset = false;
      bound.is_foreach = false;
      bound.array_size = 0;
      bound.sysfunc_type = SYSFUNC_NONE;
      bound.sysfunc_arg_idx = 0;
      bound.weight = 1;
      bound.weight_per_value = true;
      bound.has_condition = false;
      bound.cond_prop_idx = 0;
      bound.cond_op = '=';
      bound.cond_has_const = true;
      bound.cond_const = 0;
      bound.cond_prop2_idx = 0;
      bound.is_excluded_range = true;
      bound.excluded_range_low = low_bound;
      bound.excluded_range_high = high_bound;
      bound.has_element_idx = false;
      bound.element_idx = 0;
      simple_bounds_.push_back(bound);
}

void netclass_t::add_indexed_element_bound(perm_string constraint_name, size_t prop_idx, char op, bool is_soft,
                                           bool has_const, int64_t const_val, int64_t elem_idx)
{
      simple_bound_t bound;
      bound.constraint_name = constraint_name;
      bound.property_idx = prop_idx;
      bound.op = op;
      bound.is_soft = is_soft;
      bound.has_const_bound = has_const;
      bound.const_bound = const_val;
      bound.bound_prop_idx = 0;
      bound.has_prop_offset = false;
      bound.is_foreach = false;  // Not a foreach - specific element only
      bound.array_size = 0;
      bound.sysfunc_type = SYSFUNC_NONE;
      bound.sysfunc_arg_idx = 0;
      bound.weight = 1;
      bound.weight_per_value = true;
      bound.has_condition = false;
      bound.cond_prop_idx = 0;
      bound.cond_op = '=';
      bound.cond_has_const = true;
      bound.cond_const = 0;
      bound.cond_prop2_idx = 0;
      bound.is_excluded_range = false;
      bound.excluded_range_low = 0;
      bound.excluded_range_high = 0;
      bound.has_element_idx = true;
      bound.element_idx = elem_idx;
      simple_bounds_.push_back(bound);
}

const netclass_t::simple_bound_t& netclass_t::get_simple_bound(size_t idx) const
{
      assert(idx < simple_bounds_.size());
      return simple_bounds_[idx];
}

perm_string netclass_t::get_simple_bound_constraint_name(size_t idx) const
{
      assert(idx < simple_bounds_.size());
      return simple_bounds_[idx].constraint_name;
}

void netclass_t::add_unique_constraint(perm_string constraint_name, size_t prop_idx)
{
      (void)constraint_name;  // For future use with constraint_mode
      unique_props_.push_back(prop_idx);
}

size_t netclass_t::get_unique_constraint_prop(size_t idx) const
{
      assert(idx < unique_props_.size());
      return unique_props_[idx];
}
