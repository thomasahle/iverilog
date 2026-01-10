#ifndef IVL_class_type_H
#define IVL_class_type_H
/*
 * Copyright (c) 2012-2025 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version
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

# include  <string>
# include  <vector>
# include  <map>
# include  "vpi_priv.h"

class __vpiScope;

class class_property_t;
class vvp_vector4_t;

/*
 * This represents the TYPE information for a class. A %new operator
 * uses this information to figure out how to construct an actual
 * instance.
 */
class class_type : public __vpiHandle {

    public:
      struct inst_x;
      typedef inst_x*inst_t;

    public:
      explicit class_type(const std::string&nam, size_t nprop);
      ~class_type() override;

	// Set/get the parent class for inheritance hierarchy
      void set_parent(class_type*parent) { parent_ = parent; }
      class_type* get_parent() const { return parent_; }

	// Check if this class is the same as or derived from target_class
      bool is_derived_from(const class_type*target_class) const;

	// This is the name of the class type.
      inline const std::string&class_name(void) const { return class_name_; }
	// Number of properties in the class definition.
      inline size_t property_count(void) const { return properties_.size(); }

	// Set the details about the property. This is used during
	// parse of the .vvp file to fill in the details of the
	// property for the class definition.
	// rand_flag: 0=normal, 1=rand, 2=randc
      void set_property(size_t idx, const std::string&name, const std::string&type, uint64_t array_size, int rand_flag = 0);

	// Check if property is rand/randc (for randomize())
      bool property_is_rand(size_t pid) const;
	// Check if property is specifically randc (cyclic)
      bool property_is_randc(size_t pid) const;

	// This method is called after all the properties are
	// defined. This calculates information about the definition.
      void finish_setup(void);

    public:
	// Constructors and destructors for making instances.
      inst_t instance_new() const;
      void instance_delete(inst_t) const;

      void set_vec4(inst_t inst, size_t pid, const vvp_vector4_t&val, uint64_t idx = 0) const;
      void get_vec4(inst_t inst, size_t pid, vvp_vector4_t&val, uint64_t idx = 0) const;
      void set_real(inst_t inst, size_t pid, double val) const;
      double get_real(inst_t inst, size_t pid) const;
      void set_string(inst_t inst, size_t pid, const std::string&val) const;
      std::string get_string(inst_t inst, size_t pid) const;
      void set_object(inst_t inst, size_t pid, const vvp_object_t&val, size_t idx) const;
      void get_object(inst_t inst, size_t pid, vvp_object_t&val, size_t idx) const;

      void copy_property(inst_t dst, size_t idx, inst_t src) const;

	// Check if property supports vec4 operations (for randomize())
      bool property_supports_vec4(size_t pid) const;
	// Get array size for a property (1 for scalars)
      uint64_t property_array_size(size_t pid) const;

    public: // Virtual method dispatch
      struct method_info {
	    __vpiScope* scope;
	    struct vvp_code_s* entry;  // Code entry point (TD_ label)
      };
      // Register a method scope for virtual dispatch
      void register_method(const std::string& name, __vpiScope* scope, struct vvp_code_s* entry = 0);
      // Set the code entry point for a method (called after TD_ is parsed)
      void set_method_entry(const std::string& name, struct vvp_code_s* entry);
      // Look up a method by name (for virtual dispatch)
      const method_info* get_method(const std::string& name) const;

    public: // VPI related methods
      int get_type_code(void) const override;

    public: // Constraint bounds for randomize()
      // System function types for constraints (e.g., $countones(x) == 1)
      enum sysfunc_type_t {
	    SYSFUNC_NONE = 0,     // Not a system function constraint
	    SYSFUNC_COUNTONES,    // $countones(arg)
	    SYSFUNC_ONEHOT,       // $onehot(arg)
	    SYSFUNC_ONEHOT0,      // $onehot0(arg)
	    SYSFUNC_ISUNKNOWN,    // $isunknown(arg)
	    SYSFUNC_CLOG2         // $clog2(arg)
      };

      struct simple_bound_t {
	    std::string constraint_name; // Name of the constraint block this bound belongs to
	    size_t property_idx;  // Index of constrained rand property
	    char op;              // '>' | '<' | 'G' (>=) | 'L' (<=) | '=' | '!'
	    bool is_soft;         // Soft constraint (doesn't cause failure)
	    bool has_const_bound; // true if bound includes a constant
	    int64_t const_bound;  // Constant bound value or offset (if has_const_bound)
	    size_t bound_prop_idx;// Property index for property reference
	    bool has_prop_offset; // true if bound is property + constant (e.g., y <= x + 10)
	    int64_t weight;       // Weight for dist constraints (default 1)
	    bool weight_per_value;// true for := (per value), false for :/ (per range)
	    // System function constraint support
	    sysfunc_type_t sysfunc_type; // Type of system function (SYSFUNC_NONE if not applicable)
	    size_t sysfunc_arg_idx;      // Property index that is argument to system function
	    // Implication constraint condition support
	    // For "cond -> body": bound only applies when condition is true
	    bool has_condition;   // true if this bound has a guard condition
	    size_t cond_prop_idx; // Property index for condition expression
	    char cond_op;         // Condition comparison operator ('=' for ==, '!' for !=, etc.)
	    bool cond_has_const;  // true if condition compares to constant
	    int64_t cond_const;   // Constant value for condition (if cond_has_const)
	    size_t cond_prop2_idx;// Property index for condition (if !cond_has_const)
      };
      void add_constraint_bound(const simple_bound_t& bound);
	// Get constraint index from name, return -1 if not found
      int constraint_idx_from_name(const std::string& name) const;
      size_t constraint_bound_count() const { return constraint_bounds_.size(); }
      const simple_bound_t& get_constraint_bound(size_t idx) const;
	// Check if this class or any parent class has constraints
      bool has_any_constraints() const;
	// Check if all constraints are satisfied for current property values
      bool check_constraints(inst_t inst) const;
	// Generate constrained random value for a property
	// Returns value within the computed valid range from constraint bounds
      int64_t generate_constrained_random(inst_t inst, size_t prop_idx, unsigned wid) const;

    private:
      std::string class_name_;
      class_type*parent_;  // Parent class for inheritance hierarchy (nullptr if no parent)

      struct prop_t {
	    std::string name;
	    class_property_t*type;
	    int rand_flag;  // 0=normal, 1=rand, 2=randc
      };
      std::vector<prop_t> properties_;
      size_t instance_size_;

      // Virtual method dispatch table: method name -> method_info
      std::map<std::string, method_info> methods_;

      // Constraint bounds for randomize()
      std::vector<simple_bound_t> constraint_bounds_;
};

#endif /* IVL_class_type_H */
