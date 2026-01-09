#ifndef IVL_vvp_cobject_H
#define IVL_vvp_cobject_H
/*
 * Copyright (c) 2012-2025 Stephen Williams (steve@icarus.com)
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

# include  <string>
# include  <stdint.h>
# include  <vector>
# include  <set>
# include  <map>
# include  "vvp_object.h"
# include  "class_type.h"

class vvp_vector4_t;

class vvp_cobject : public vvp_object {

    public:
      explicit vvp_cobject(const class_type*defn);
      ~vvp_cobject() override;

      void set_vec4(size_t pid, const vvp_vector4_t&val, uint64_t idx = 0);
      void get_vec4(size_t pid, vvp_vector4_t&val, uint64_t idx = 0);

      void set_real(size_t pid, double val);
      double get_real(size_t pid);

      void set_string(size_t pid, const std::string&val);
      std::string get_string(size_t pid);

      void set_object(size_t pid, const vvp_object_t&val, size_t idx);
      void get_object(size_t pid, vvp_object_t&val, size_t idx);

      void shallow_copy(const vvp_object*that) override;

      // Get the class type definition for virtual dispatch
      const class_type* get_class_type() const { return defn_; }

      // Get the instance for constraint checking
      class_type::inst_t get_instance() const { return properties_; }

      // rand_mode support: control randomization per property per instance
      // mode=1 means randomization enabled (default), mode=0 means disabled
      void set_rand_mode(size_t pid, int mode);
      int get_rand_mode(size_t pid) const;
      // Check if property should be randomized (respects rand_mode)
      bool should_randomize(size_t pid) const;

      // constraint_mode support: control named constraints per instance
      // mode=1 means constraint enabled (default), mode=0 means disabled
      void set_constraint_mode(const std::string& constraint_name, int mode);
      int get_constraint_mode(const std::string& constraint_name) const;
      // Check if a constraint is enabled (for use in check_constraints)
      bool is_constraint_enabled(const std::string& constraint_name) const;

      // randc support: track used values for cyclic randomization
      // Returns true if value has been used in this cycle
      bool randc_value_used(size_t pid, int64_t value) const;
      // Mark a value as used for this property
      void randc_mark_used(size_t pid, int64_t value);
      // Get the set of used values for a randc property
      const std::set<int64_t>& randc_get_used(size_t pid) const;
      // Clear used values (start new cycle) for a property
      void randc_clear(size_t pid);
      // Check if property is randc (vs rand)
      bool is_randc(size_t pid) const;

    private:
      const class_type* defn_;
	// For now, only support 32bit bool signed properties.
      class_type::inst_t properties_;
      // Per-property rand_mode: empty means all enabled
      // Only properties that have been explicitly disabled are tracked
      std::vector<bool> rand_mode_disabled_;
      // Per-constraint constraint_mode: tracks disabled constraint names
      std::set<std::string> constraint_mode_disabled_;
      // Per-property randc used values: tracks values used in current cycle
      mutable std::map<size_t, std::set<int64_t>> randc_used_values_;
      // Empty set for returning when no values used
      static const std::set<int64_t> empty_set_;
};

#endif /* IVL_vvp_cobject_H */
