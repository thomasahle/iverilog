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
