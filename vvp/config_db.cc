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

#include "config_db.h"
#include <cstdio>

vvp_config_db& vvp_config_db::instance()
{
      static vvp_config_db inst;
      return inst;
}

std::string vvp_config_db::make_key(const std::string& context_path,
                                     const std::string& inst_name,
                                     const std::string& field_name)
{
      // Key format: context_path::inst_name::field_name
      // If context_path is empty or "null", use just inst_name
      // This matches UVM's hierarchical lookup behavior
      std::string key;

      if (context_path.empty() || context_path == "null") {
            key = inst_name;
      } else if (inst_name.empty()) {
            key = context_path;
      } else {
            key = context_path + "." + inst_name;
      }

      key += "::" + field_name;
      return key;
}

void vvp_config_db::set_vec4(const std::string& context_path,
                              const std::string& inst_name,
                              const std::string& field_name,
                              const vvp_vector4_t& value)
{
      std::string key = make_key(context_path, inst_name, field_name);
      db_[key] = config_db_entry(value);
}

void vvp_config_db::set_object(const std::string& context_path,
                                const std::string& inst_name,
                                const std::string& field_name,
                                const vvp_object_t& value)
{
      std::string key = make_key(context_path, inst_name, field_name);
      db_[key] = config_db_entry(value);
}

// Helper to find an entry with wildcard matching
const config_db_entry* vvp_config_db_find_entry(
      const std::map<std::string, config_db_entry>& db,
      const std::string& context_path,
      const std::string& inst_name,
      const std::string& field_name)
{
      std::string key = vvp_config_db::make_key(context_path, inst_name, field_name);

      auto it = db.find(key);
      if (it != db.end()) {
            return &it->second;
      }

      // Try with wildcard matching for inst_name containing "*"
      // UVM allows wildcards in the instance path
      for (auto& entry : db) {
            // Simple wildcard match: if stored key ends with same field
            // and the inst_name pattern matches
            size_t field_pos = entry.first.rfind("::");
            if (field_pos != std::string::npos) {
                  std::string stored_field = entry.first.substr(field_pos + 2);
                  if (stored_field == field_name) {
                        std::string stored_path = entry.first.substr(0, field_pos);
                        // Check if our requested path matches stored path
                        // For now, simple prefix matching
                        std::string req_path;
                        if (context_path.empty() || context_path == "null") {
                              req_path = inst_name;
                        } else if (inst_name.empty()) {
                              req_path = context_path;
                        } else {
                              req_path = context_path + "." + inst_name;
                        }

                        // Direct match or stored path is prefix of requested
                        // Also match if stored path is "*" (wildcard)
                        if (req_path == stored_path ||
                            stored_path == "*" ||
                            (req_path.length() > stored_path.length() &&
                             req_path.substr(0, stored_path.length()) == stored_path &&
                             req_path[stored_path.length()] == '.')) {
                              return &entry.second;
                        }
                  }
            }
      }

      return nullptr;
}

bool vvp_config_db::get_vec4(const std::string& context_path,
                              const std::string& inst_name,
                              const std::string& field_name,
                              vvp_vector4_t& value) const
{
      const config_db_entry* entry = vvp_config_db_find_entry(db_, context_path, inst_name, field_name);
      if (entry && entry->type == config_db_entry::VEC4_TYPE) {
            value = entry->vec4_value;
            return true;
      }
      return false;
}

bool vvp_config_db::get_object(const std::string& context_path,
                                const std::string& inst_name,
                                const std::string& field_name,
                                vvp_object_t& value) const
{
      const config_db_entry* entry = vvp_config_db_find_entry(db_, context_path, inst_name, field_name);
      if (entry && entry->type == config_db_entry::OBJECT_TYPE) {
            value = entry->obj_value;
            return true;
      }
      return false;
}

bool vvp_config_db::exists(const std::string& context_path,
                           const std::string& inst_name,
                           const std::string& field_name) const
{
      return vvp_config_db_find_entry(db_, context_path, inst_name, field_name) != nullptr;
}

void vvp_config_db::dump() const
{
      fprintf(stderr, "=== Config Database Contents ===\n");
      for (auto& entry : db_) {
            const char* type_str = (entry.second.type == config_db_entry::VEC4_TYPE) ? "vec4" : "object";
            fprintf(stderr, "  %s: (%s)\n", entry.first.c_str(), type_str);
      }
      fprintf(stderr, "================================\n");
}
