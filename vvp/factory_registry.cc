/*
 * Copyright (c) 2025 Stephen Williams (steve@icarus.com)
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

#include "factory_registry.h"
#include "class_type.h"
#include "vpi_priv.h"
#include <cstdio>

vvp_factory_registry& vvp_factory_registry::instance()
{
    static vvp_factory_registry singleton;
    return singleton;
}

void vvp_factory_registry::register_class(const std::string& type_name,
                                          class_type* class_def,
                                          __vpiScope* constructor_scope,
                                          vvp_code_s* constructor_entry)
{
    factory_entry entry;
    entry.class_def = class_def;
    entry.constructor_scope = constructor_scope;
    entry.constructor_entry = constructor_entry;

    // Check if already registered (warn but allow override)
    auto it = registry_.find(type_name);
    if (it != registry_.end()) {
        // UVM allows factory overrides, so just update
        it->second = entry;
    } else {
        registry_[type_name] = entry;
    }
}

class_type* vvp_factory_registry::find_class(const std::string& type_name) const
{
    auto it = registry_.find(type_name);
    if (it != registry_.end()) {
        return it->second.class_def;
    }
    return nullptr;
}

__vpiScope* vvp_factory_registry::get_constructor_scope(const std::string& type_name) const
{
    auto it = registry_.find(type_name);
    if (it != registry_.end()) {
        return it->second.constructor_scope;
    }
    return nullptr;
}

vvp_code_s* vvp_factory_registry::get_constructor_entry(const std::string& type_name) const
{
    auto it = registry_.find(type_name);
    if (it != registry_.end()) {
        return it->second.constructor_entry;
    }
    return nullptr;
}

bool vvp_factory_registry::is_registered(const std::string& type_name) const
{
    return registry_.find(type_name) != registry_.end();
}

void vvp_factory_registry::dump_registry() const
{
    fprintf(stderr, "VVP Factory Registry (%zu classes):\n", registry_.size());
    for (const auto& entry : registry_) {
        const std::string& class_name = entry.second.class_def
            ? entry.second.class_def->class_name()
            : "(null)";
        fprintf(stderr, "  \"%s\" -> %s (ctor=%s)\n",
                entry.first.c_str(),
                class_name.c_str(),
                entry.second.constructor_scope ? "yes" : "no");
    }
}

// ============================================================================
// Factory Type Override Implementation
// ============================================================================

void vvp_factory_registry::set_type_override(const std::string& original_type,
                                              const std::string& override_type)
{
    // Check that override type is registered (warn but allow - type might be registered later)
    if (!is_registered(override_type)) {
        fprintf(stderr, "UVM_WARNING: Override type '%s' not yet registered\n",
                override_type.c_str());
    }

    type_overrides_[original_type] = override_type;
}

void vvp_factory_registry::set_inst_override(const std::string& inst_path,
                                              const std::string& original_type,
                                              const std::string& override_type)
{
    // Check that override type is registered (warn but allow - type might be registered later)
    if (!is_registered(override_type)) {
        fprintf(stderr, "UVM_WARNING: Override type '%s' not yet registered\n",
                override_type.c_str());
    }

    inst_overrides_[std::make_pair(inst_path, original_type)] = override_type;
}

bool vvp_factory_registry::path_matches(const std::string& pattern, const std::string& path)
{
    // Simple wildcard matching: * matches any substring
    // Uses fnmatch-style matching
    size_t pi = 0, pj = 0;
    size_t star_i = std::string::npos, star_j = 0;

    while (pj < path.size()) {
        if (pi < pattern.size() && (pattern[pi] == path[pj] || pattern[pi] == '?')) {
            pi++;
            pj++;
        } else if (pi < pattern.size() && pattern[pi] == '*') {
            star_i = pi;
            star_j = pj;
            pi++;
        } else if (star_i != std::string::npos) {
            pi = star_i + 1;
            star_j++;
            pj = star_j;
        } else {
            return false;
        }
    }

    while (pi < pattern.size() && pattern[pi] == '*') {
        pi++;
    }

    return pi == pattern.size();
}

class_type* vvp_factory_registry::find_class_with_override(const std::string& type_name,
                                                            const std::string& inst_path) const
{
    std::string effective_type = get_override_type(type_name, inst_path);
    return find_class(effective_type);
}

bool vvp_factory_registry::has_type_override(const std::string& type_name) const
{
    return type_overrides_.find(type_name) != type_overrides_.end();
}

std::string vvp_factory_registry::get_override_type(const std::string& type_name,
                                                     const std::string& inst_path) const
{
    // First check instance overrides (if inst_path provided)
    if (!inst_path.empty()) {
        for (const auto& entry : inst_overrides_) {
            const std::string& pattern = entry.first.first;
            const std::string& orig_type = entry.first.second;
            if (orig_type == type_name && path_matches(pattern, inst_path)) {
                return entry.second;
            }
        }
    }

    // Then check type overrides
    auto it = type_overrides_.find(type_name);
    if (it != type_overrides_.end()) {
        return it->second;
    }

    // No override found, return original type
    return type_name;
}

void vvp_factory_registry::dump_overrides() const
{
    fprintf(stderr, "VVP Factory Type Overrides (%zu):\n", type_overrides_.size());
    for (const auto& entry : type_overrides_) {
        fprintf(stderr, "  %s -> %s\n", entry.first.c_str(), entry.second.c_str());
    }

    fprintf(stderr, "VVP Factory Instance Overrides (%zu):\n", inst_overrides_.size());
    for (const auto& entry : inst_overrides_) {
        fprintf(stderr, "  [%s] %s -> %s\n",
                entry.first.first.c_str(),
                entry.first.second.c_str(),
                entry.second.c_str());
    }
}
