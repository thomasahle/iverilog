#ifndef IVL_netscalar_H
#define IVL_netscalar_H
/*
 * Copyright (c) 2013-2025 Stephen Williams (steve@icarus.com)
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

# include  "nettypes.h"
# include  "StringHeap.h"

class netreal_t : public ivl_type_s {

    public:
      inline explicit netreal_t() { }
      ~netreal_t() override;

      ivl_variable_type_t base_type() const override;
      bool get_signed() const override { return true; }
      bool get_scalar() const override { return true; }

      std::ostream& debug_dump(std::ostream&) const override;

    public:
      static netreal_t type_real;
      static netreal_t type_shortreal;
};

class netstring_t : public ivl_type_s {

    public:
      inline explicit netstring_t() { }
      ~netstring_t() override;

      ivl_variable_type_t base_type() const override;
      // Strings don't have a fixed packed width - return -1 to indicate this
      long packed_width() const override;

      std::ostream& debug_dump(std::ostream&) const override;

    public:
      static netstring_t type_string;
};

class NetScope;  // Forward declaration

/*
 * The netevent_type_t represents an event type as a class property.
 * Events in classes can be triggered and waited on. This type is used
 * during elaboration to represent event class properties.
 */
class netevent_type_t : public ivl_type_s {

    public:
      inline explicit netevent_type_t() { }
      ~netevent_type_t() override;

      ivl_variable_type_t base_type() const override;

      std::ostream& debug_dump(std::ostream&) const override;

    public:
      static netevent_type_t type_event;
};

/*
 * The netsemaphore_t represents the SystemVerilog semaphore built-in class.
 * Semaphores are counting semaphores with get(), put(), and try_get() methods.
 */
class netsemaphore_t : public ivl_type_s {

    public:
      inline explicit netsemaphore_t() { }
      ~netsemaphore_t() override;

      ivl_variable_type_t base_type() const override;

      std::ostream& debug_dump(std::ostream&) const override;

    public:
      static netsemaphore_t type_semaphore;
};

/*
 * The netvirtual_interface_t represents an elaborated virtual interface.
 * Virtual interfaces are class properties that reference interface instances.
 * The interface binding happens at runtime, but we store a pointer to the
 * interface definition scope for member lookup during elaboration.
 */
class netvirtual_interface_t : public ivl_type_s {

    public:
      inline explicit netvirtual_interface_t(perm_string iname, const NetScope* iface_def = nullptr)
            : interface_name_(iname), interface_def_(iface_def) { }
      ~netvirtual_interface_t() override;

      ivl_variable_type_t base_type() const override;

      // Override type equivalence to compare interface names
      bool test_equivalence(ivl_type_t that) const override;

      std::ostream& debug_dump(std::ostream&) const override;

      inline perm_string interface_name() const { return interface_name_; }

      // Get the interface definition scope (may be null if not resolved)
      inline const NetScope* interface_def() const { return interface_def_; }

    private:
      perm_string interface_name_;
      const NetScope* interface_def_;  // Pointer to interface scope definition
};

#endif /* IVL_netscalar_H */
