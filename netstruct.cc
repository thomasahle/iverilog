/*
 * Copyright (c) 2011-2022 Stephen Williams (steve@icarus.com)
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

# include  "netlist.h"
# include  "netstruct.h"
# include  "netvector.h"
# include  <iostream>

# include  "ivl_assert.h"

using namespace std;

netstruct_t::netstruct_t()
: union_(false), packed_(false), signed_(false)
{
}

netstruct_t::~netstruct_t()
{
}

void netstruct_t::union_flag(bool flag)
{
	// This MUST be called before any members are pushed into the
	// definition. This is because the append relies on this flag
	// being accurate.
      ivl_assert(*this, members_.empty());
      union_ = flag;
}

void netstruct_t::packed(bool flag)
{
      ivl_assert(*this, members_.empty());
      packed_ = flag;
}

void netstruct_t::append_member(Design*des, const netstruct_t::member_t&val)
{
      ivl_assert(*this, val.net_type);

      members_.push_back(val);
      if (packed_) {
	    if (! members_.back().net_type->packed()) {
		  cerr << get_fileline() << ": error: "
		       << "Member " << members_.back().name
		       << " of packed struct/union"
		       << " must be packed." << endl;
		  des->errors += 1;
	    }
      }
      if (union_ && packed_ && members_.size() > 1) {
	    unsigned long expect_wid = members_.front().net_type->packed_width();
	    unsigned long got_wid = members_.back().net_type->packed_width();
	    if (expect_wid != got_wid) {
		  cerr << get_fileline() << ": error: "
		       << "Member " << val.name
		       << " of packed union"
		       << " is " << got_wid
		       << " bits, expecting " << expect_wid << " bits." << endl;
		  des->errors += 1;
	    }
      }
}

const netstruct_t::member_t* netstruct_t::packed_member(perm_string name, unsigned long&off) const
{
      unsigned long count_off = 0;
      for (size_t idx = members_.size() ; idx > 0 ; idx -= 1) {
	    if (members_[idx-1].name == name) {
		  off = count_off;
		  return &members_[idx-1];
	    }
	      // If this is not a union, then the members are lined up
	      // from LSB to MSB.  If this is a union, then all
	      // members are at offset 0.
	    if (!union_)
		  count_off += members_[idx-1].net_type->packed_width();
      }

      return 0;
}

long netstruct_t::packed_width(void) const
{
	// If this is a packed union, then all the members are the
	// same width, so it is sufficient to return the width of any
	// single member.
      if (union_)
	    return members_.front().net_type->packed_width();

	// The width of a struct (packed or unpacked) is the sum of member widths.
	// For unpacked structs, this gives the total storage required when
	// members are stored contiguously (as packed vectors).
      long res = 0;
      for (size_t idx = 0 ; idx < members_.size() ; idx += 1) {
	    long mwid = members_[idx].net_type->packed_width();
	    if (mwid < 0) {
		    // If any member has unpacked type, can't compute total width
		  return -1;
	    }
	    res += mwid;
      }

      return res;
}

netranges_t netstruct_t::slice_dimensions() const
{
      netranges_t tmp;
      tmp .push_back(netrange_t(packed_width()-1, 0));
      return tmp;
}

ivl_variable_type_t netstruct_t::base_type() const
{
      if (! packed_) {
	      // For unpacked structs, check if all members have packed types.
	      // If so, we can treat it as IVL_VT_LOGIC since it's stored as
	      // a contiguous bit vector.
	    long pw = packed_width();
	    if (pw > 0) {
		    // Has a valid packed width - all members are packed
		    // Return the most specific type found in members
		  for (size_t idx = 0 ; idx < members_.size() ; idx += 1) {
			if (members_[idx].data_type() != IVL_VT_BOOL)
			      return members_[idx].data_type();
		  }
		  return IVL_VT_BOOL;
	    }
	    return IVL_VT_NO_TYPE;
      }

      for (size_t idx = 0 ;  idx < members_.size() ; idx += 1) {
	    if (members_[idx].data_type() != IVL_VT_BOOL)
		  return members_[idx].data_type();
      }

      return IVL_VT_BOOL;
}

bool netstruct_t::test_compatibility(ivl_type_t that) const
{
      if (!packed_) {
	    // For unpacked structs, use structural equivalence
	    // This allows typedef'd structs from different scopes to match
	    return test_equivalence(that);
      }
      return packed_type_compatible(that);
}

bool netstruct_t::test_equivalence(ivl_type_t that) const
{
      if (!packed_) {
	    // For unpacked structs, implement structural equivalence
	    // This allows typedef'd structs from different scopes to match
	    const netstruct_t*that_s = dynamic_cast<const netstruct_t*>(that);
	    if (!that_s)
		  return false;

	    // Must also be unpacked
	    if (that_s->packed())
		  return false;

	    // Check union flag matches
	    if (union_ != that_s->union_flag())
		  return false;

	    // Check same number of members
	    if (members_.size() != that_s->member_count())
		  return false;

	    // Check each member has same name and equivalent type
	    for (size_t idx = 0; idx < members_.size(); ++idx) {
		  const member_t*m1 = &members_[idx];
		  const member_t*m2 = that_s->get_member(idx);
		  if (!m2)
			return false;

		  // Names must match
		  if (m1->name != m2->name)
			return false;

		  // Types must be equivalent
		  if (!m1->net_type->type_equivalent(m2->net_type))
			return false;
	    }

	    return true;
      }

      return packed_types_equivalent(this, that);
}

/*
 * Member indexing for unpacked struct support.
 * Get member index from name, returns -1 if not found.
 */
int netstruct_t::member_idx_from_name(perm_string name) const
{
      for (size_t idx = 0; idx < members_.size(); idx++) {
	    if (members_[idx].name == name) {
		  return static_cast<int>(idx);
	    }
      }
      return -1;
}

/*
 * Get member by index. Returns null if index is out of range.
 */
const netstruct_t::member_t* netstruct_t::get_member(size_t idx) const
{
      if (idx >= members_.size())
	    return 0;
      return &members_[idx];
}
