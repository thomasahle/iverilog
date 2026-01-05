/*
 * Copyright (c) 2012-2013 Stephen Williams (steve@icarus.com)
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

# include  "vvp_cobject.h"
# include  "class_type.h"
# include  <iostream>
# include  <cassert>

using namespace std;

vvp_cobject::vvp_cobject(const class_type*defn)
: defn_(defn), properties_(defn->instance_new())
{
}

vvp_cobject::~vvp_cobject()
{
      defn_->instance_delete(properties_);
      properties_ = 0;
}

void vvp_cobject::set_vec4(size_t pid, const vvp_vector4_t&val, uint64_t idx)
{
      defn_->set_vec4(properties_, pid, val, idx);
}

void vvp_cobject::get_vec4(size_t pid, vvp_vector4_t&val, uint64_t idx)
{
      defn_->get_vec4(properties_, pid, val, idx);
}

void vvp_cobject::set_real(size_t pid, double val)
{
      defn_->set_real(properties_, pid, val);
}

double vvp_cobject::get_real(size_t pid)
{
      return defn_->get_real(properties_, pid);
}

void vvp_cobject::set_string(size_t pid, const string&val)
{
      defn_->set_string(properties_, pid, val);
}

string vvp_cobject::get_string(size_t pid)
{
      return defn_->get_string(properties_, pid);
}

void vvp_cobject::set_object(size_t pid, const vvp_object_t&val, size_t idx)
{
      defn_->set_object(properties_, pid, val, idx);
}

void vvp_cobject::get_object(size_t pid, vvp_object_t&val, size_t idx)
{
      return defn_->get_object(properties_, pid, val, idx);
}

void vvp_cobject::shallow_copy(const vvp_object*obj)
{
      const vvp_cobject*that = dynamic_cast<const vvp_cobject*>(obj);
      assert(that);

      assert(defn_ == that->defn_);

      for (size_t idx = 0 ; idx < defn_->property_count() ; idx += 1)
	    defn_->copy_property(properties_, idx, that->properties_);

      // Copy rand_mode state
      rand_mode_disabled_ = that->rand_mode_disabled_;
}

void vvp_cobject::set_rand_mode(size_t pid, int mode)
{
      size_t nprop = defn_->property_count();
      if (pid >= nprop) return;

      // Ensure vector is sized properly
      if (rand_mode_disabled_.size() < nprop)
	    rand_mode_disabled_.resize(nprop, false);

      // mode=0 means disabled, mode=1 means enabled
      rand_mode_disabled_[pid] = (mode == 0);
}

int vvp_cobject::get_rand_mode(size_t pid) const
{
      size_t nprop = defn_->property_count();
      if (pid >= nprop) return 1;  // Default: enabled

      if (rand_mode_disabled_.size() <= pid)
	    return 1;  // Not in vector = enabled

      return rand_mode_disabled_[pid] ? 0 : 1;
}

bool vvp_cobject::should_randomize(size_t pid) const
{
      // Check class definition: is property rand/randc?
      if (!defn_->property_is_rand(pid))
	    return false;

      // Check instance rand_mode
      return get_rand_mode(pid) != 0;
}

void vvp_cobject::set_constraint_mode(const std::string& constraint_name, int mode)
{
      if (mode == 0) {
	    // Disable constraint
	    constraint_mode_disabled_.insert(constraint_name);
      } else {
	    // Enable constraint
	    constraint_mode_disabled_.erase(constraint_name);
      }
}

int vvp_cobject::get_constraint_mode(const std::string& constraint_name) const
{
      // Default: enabled (1), disabled if in set (0)
      if (constraint_mode_disabled_.count(constraint_name) > 0)
	    return 0;
      return 1;
}

bool vvp_cobject::is_constraint_enabled(const std::string& constraint_name) const
{
      return get_constraint_mode(constraint_name) != 0;
}
