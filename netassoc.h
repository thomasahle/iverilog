#ifndef IVL_netassoc_H
#define IVL_netassoc_H
/*
 * Copyright (c) 2025 Stephen Williams (steve@icarus.com)
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
# include  "ivl_target.h"

/*
 * An associative array type with an index type. The index type can be:
 * - A basic type (int, string, etc.)
 * - A class type
 * - A wildcard (indicated by index_type_ == nullptr)
 */
class netassoc_t : public netarray_t {

    public:
      explicit netassoc_t(ivl_type_t element_type, ivl_type_t index_type);
      ~netassoc_t() override;

	// This is the "base_type()" virtual method of the
	// nettype_base_t. The ivl_target api expects this to return
	// IVL_VT_ASSOC for associative arrays.
      ivl_variable_type_t base_type() const override;

	// A associative array may have an element type that is signed.
      inline bool get_signed() const override { return element_type()->get_signed(); }

	// Get the width of the element type.
      inline unsigned long element_width() const { return element_type()->packed_width(); }

	// Get the base type of the element.
      inline ivl_variable_type_t element_base_type() const { return element_type()->base_type(); }

	// Get the index type for this associative array.
	// Returns nullptr for wildcard index ([*]).
      inline ivl_type_t index_type() const { return index_type_; }

	// Check if this is a wildcard associative array
      inline bool is_wildcard() const { return index_type_ == nullptr; }

      std::ostream& debug_dump(std::ostream&) const override;

    private:
      ivl_type_t index_type_;
      bool test_compatibility(ivl_type_t that) const override;
      bool test_equivalence(ivl_type_t that) const override;
};

#endif /* IVL_netassoc_H */
