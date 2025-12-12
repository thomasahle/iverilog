/*
 * Copyright (c) 2013 Stephen Williams (steve@icarus.com)
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

# include  "netscalar.h"

using namespace std;

netreal_t netreal_t::type_real;
netreal_t netreal_t::type_shortreal;
netstring_t netstring_t::type_string;

netreal_t::~netreal_t()
{
}

ivl_variable_type_t netreal_t::base_type() const
{
      return IVL_VT_REAL;
}

netstring_t::~netstring_t()
{
}

ivl_variable_type_t netstring_t::base_type() const
{
      return IVL_VT_STRING;
}

netvirtual_interface_t::~netvirtual_interface_t()
{
}

ivl_variable_type_t netvirtual_interface_t::base_type() const
{
      // Use IVL_VT_CLASS since virtual interfaces are references to interface instances
      return IVL_VT_CLASS;
}

bool netvirtual_interface_t::test_equivalence(ivl_type_t that) const
{
      const netvirtual_interface_t*that_vif = dynamic_cast<const netvirtual_interface_t*>(that);
      if (that_vif == nullptr)
            return false;
      // Two virtual interface types are equivalent if they have the same interface name
      return interface_name_ == that_vif->interface_name_;
}

ostream& netvirtual_interface_t::debug_dump(ostream&out) const
{
      out << "virtual interface " << interface_name_;
      return out;
}
