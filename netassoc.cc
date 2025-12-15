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

# include  "netassoc.h"
# include  <iostream>

using namespace std;

netassoc_t::netassoc_t(ivl_type_t element_type, ivl_type_t index_type)
: netarray_t(element_type), index_type_(index_type)
{
}

netassoc_t::~netassoc_t()
{
}

ivl_variable_type_t netassoc_t::base_type() const
{
      return IVL_VT_ASSOC;
}

bool netassoc_t::test_equivalence(ivl_type_t that) const
{
      const netassoc_t *that_aa = dynamic_cast<const netassoc_t*>(that);
      if (!that_aa)
	    return false;

      // Both must be wildcard or both must have equivalent index types
      if (is_wildcard() != that_aa->is_wildcard())
	    return false;

      if (!is_wildcard()) {
	    if (!index_type_->type_equivalent(that_aa->index_type_))
		  return false;
      }

      return element_type()->type_equivalent(that_aa->element_type());
}

bool netassoc_t::test_compatibility(ivl_type_t that) const
{
      // For now, require full equivalence for compatibility
      return test_equivalence(that);
}

ostream& netassoc_t::debug_dump(ostream&o) const
{
      o << "associative array ";
      if (element_type())
	    element_type()->debug_dump(o);
      else
	    o << "(nil element)";

      o << " [";
      if (is_wildcard()) {
	    o << "*";
      } else if (index_type_) {
	    index_type_->debug_dump(o);
      }
      o << "]";
      return o;
}
