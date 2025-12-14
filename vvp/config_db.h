#ifndef IVL_config_db_H
#define IVL_config_db_H
/*
 * Copyright (c) 2024 Stephen Williams (steve@icarus.com)
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

/*
 * This file defines the UVM config_db runtime storage.
 * The config_db stores values (objects, virtual interfaces, etc.) indexed
 * by hierarchical path and field name, allowing UVM components to pass
 * configuration data between components.
 */

#include <map>
#include <string>
#include "vvp_object.h"
#include "vvp_net.h"

// Entry in the config database - can hold either vec4 or object
struct config_db_entry {
      enum { VEC4_TYPE, OBJECT_TYPE } type;
      vvp_vector4_t vec4_value;
      vvp_object_t obj_value;

      config_db_entry() : type(VEC4_TYPE) {}
      config_db_entry(const vvp_vector4_t& v) : type(VEC4_TYPE), vec4_value(v) {}
      config_db_entry(const vvp_object_t& o) : type(OBJECT_TYPE), obj_value(o) {}
};

class vvp_config_db {
    public:
      // Get the singleton instance
      static vvp_config_db& instance();

      // Store a vec4 value in the config database
      void set_vec4(const std::string& context_path,
                    const std::string& inst_name,
                    const std::string& field_name,
                    const vvp_vector4_t& value);

      // Store an object value in the config database
      void set_object(const std::string& context_path,
                      const std::string& inst_name,
                      const std::string& field_name,
                      const vvp_object_t& value);

      // Retrieve a vec4 value from the config database
      // Returns true if found and type matches, false otherwise
      bool get_vec4(const std::string& context_path,
                    const std::string& inst_name,
                    const std::string& field_name,
                    vvp_vector4_t& value) const;

      // Retrieve an object value from the config database
      // Returns true if found and type matches, false otherwise
      bool get_object(const std::string& context_path,
                      const std::string& inst_name,
                      const std::string& field_name,
                      vvp_object_t& value) const;

      // Check if a value exists
      bool exists(const std::string& context_path,
                  const std::string& inst_name,
                  const std::string& field_name) const;

      // Debug: dump all entries
      void dump() const;

      // Build the lookup key from path components (public for helper function)
      static std::string make_key(const std::string& context_path,
                                  const std::string& inst_name,
                                  const std::string& field_name);

    private:
      vvp_config_db() {}

      // Storage: key -> entry
      std::map<std::string, config_db_entry> db_;
};

#endif /* IVL_config_db_H */
