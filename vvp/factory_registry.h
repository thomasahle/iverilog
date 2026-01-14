#ifndef IVL_factory_registry_H
#define IVL_factory_registry_H
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

#include <map>
#include <string>

class class_type;
class __vpiScope;
struct vvp_code_s;

/*
 * Factory registry for UVM-style class creation by name.
 *
 * This singleton class maintains a mapping from type names (strings)
 * to class_type definitions. When UVM code calls run_test("test_name")
 * or type_id::create(), the factory looks up the class by name and
 * creates an instance.
 */
class vvp_factory_registry {
public:
    // Get the singleton instance
    static vvp_factory_registry& instance();

    // Register a class with the factory under the given type name.
    // The type_name is typically the class name as used in uvm_*_utils macro.
    void register_class(const std::string& type_name,
                        class_type* class_def,
                        __vpiScope* constructor_scope = nullptr,
                        vvp_code_s* constructor_entry = nullptr);

    // Look up a class by type name.
    // Returns nullptr if not found.
    class_type* find_class(const std::string& type_name) const;

    // Get constructor scope for a registered class.
    // Returns nullptr if class not found or has no constructor.
    __vpiScope* get_constructor_scope(const std::string& type_name) const;

    // Get constructor entry point for a registered class.
    // Returns nullptr if class not found or has no constructor.
    vvp_code_s* get_constructor_entry(const std::string& type_name) const;

    // Check if a class is registered
    bool is_registered(const std::string& type_name) const;

    // Debug: dump all registered classes to stdout
    void dump_registry() const;

    // Get the number of registered classes
    size_t size() const { return registry_.size(); }

    // ========================================================================
    // Factory Type Override Support
    // ========================================================================

    // Set a type override: when creating original_type, create override_type instead.
    // This is the core of UVM factory override functionality.
    void set_type_override(const std::string& original_type,
                           const std::string& override_type);

    // Set an instance override: only affects a specific instance path.
    // inst_path can contain wildcards (* matches any substring).
    void set_inst_override(const std::string& inst_path,
                           const std::string& original_type,
                           const std::string& override_type);

    // Find a class with override support.
    // First checks instance overrides (if inst_path is not empty),
    // then checks type overrides, then falls back to the original type.
    class_type* find_class_with_override(const std::string& type_name,
                                         const std::string& inst_path = "") const;

    // Check if a type has an override registered
    bool has_type_override(const std::string& type_name) const;

    // Get the override type name (or original if no override)
    std::string get_override_type(const std::string& type_name,
                                  const std::string& inst_path = "") const;

    // Debug: dump all overrides
    void dump_overrides() const;

private:
    // Private constructor for singleton
    vvp_factory_registry() = default;
    ~vvp_factory_registry() = default;

    // Non-copyable
    vvp_factory_registry(const vvp_factory_registry&) = delete;
    vvp_factory_registry& operator=(const vvp_factory_registry&) = delete;

    // Registry entry containing class info
    struct factory_entry {
        class_type* class_def;
        __vpiScope* constructor_scope;
        vvp_code_s* constructor_entry;
    };

    // Map from type name to factory entry
    std::map<std::string, factory_entry> registry_;

    // Map from original type name to override type name (for type overrides)
    std::map<std::string, std::string> type_overrides_;

    // Map from (inst_path, original_type) to override type name (for instance overrides)
    // inst_path can contain wildcards
    std::map<std::pair<std::string, std::string>, std::string> inst_overrides_;

    // Helper: check if inst_path matches a pattern (with * wildcards)
    static bool path_matches(const std::string& pattern, const std::string& path);
};

#endif /* IVL_factory_registry_H */
