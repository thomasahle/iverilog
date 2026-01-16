/*
 * Copyright (c) 2007-2019 Stephen Williams (steve@icarus.com)
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


# include  "pform_types.h"

data_type_t::~data_type_t()
{
}

PNamedItem::SymbolType data_type_t::symbol_type() const
{
      return TYPE;
}

string_type_t::~string_type_t()
{
}

event_type_t::~event_type_t()
{
}

semaphore_type_t::~semaphore_type_t()
{
}

mailbox_type_t::~mailbox_type_t()
{
      delete element_type_;
}

virtual_interface_type_t::~virtual_interface_type_t()
{
}

pform_coverpoint_t::~pform_coverpoint_t()
{
      for (pform_bin_t* bin : bins) {
            delete bin;
      }
}

covergroup_type_t::~covergroup_type_t()
{
      for (pform_coverpoint_t* cp : coverpoints) {
            delete cp;
      }
      for (pform_cross_t* cross : crosses) {
            delete cross;
      }
}

/*
 * Calculate the total number of bins from all coverpoints.
 * Each explicit bin counts as 1 (or array_count if bin[N] form).
 * If a coverpoint has no explicit bins, it's assumed to have auto bins
 * which we estimate at 16 for now (typical default).
 */
int covergroup_type_t::calculate_bins_count() const
{
      int total_bins = 0;

      for (pform_coverpoint_t* cp : coverpoints) {
            if (cp->bins.empty()) {
                  // No explicit bins - use auto bins default
                  total_bins += 16;
            } else {
                  for (pform_bin_t* bin : cp->bins) {
                        // Skip ignore_bins and illegal_bins as they don't contribute to coverage
                        if (bin->kind == pform_bin_t::IGNORE_BIN ||
                            bin->kind == pform_bin_t::ILLEGAL_BIN)
                              continue;
                        // Count the bin(s)
                        if (bin->array_count > 0) {
                              total_bins += bin->array_count;
                        } else {
                              // Single bin or auto-sized array bin
                              total_bins += 1;
                        }
                  }
            }
      }

      // Cross coverage bins are product of crossed coverpoint bins
      // For now, just add a placeholder count for each cross
      for (pform_cross_t* cross : crosses) {
            (void)cross; // Unused for now
            total_bins += 16; // Placeholder
      }

      // Ensure at least 1 bin
      if (total_bins == 0)
            total_bins = 1;

      return total_bins;
}

atom_type_t size_type (atom_type_t::INT, true);

PNamedItem::SymbolType enum_type_t::symbol_type() const
{
      return ENUM;
}

PNamedItem::SymbolType class_type_t::symbol_type() const
{
      return CLASS;
}

bool typedef_t::set_data_type(data_type_t *t)
{
      if (data_type.get())
	    return false;

      data_type.reset(t);

      return true;
}

bool typedef_t::set_basic_type(enum basic_type bt)
{
      if (bt == ANY)
	    return true;
      if (basic_type != ANY && bt != basic_type)
	    return false;

      basic_type = bt;

      return true;
}

std::ostream& operator<< (std::ostream&out, enum typedef_t::basic_type bt)
{
	switch (bt) {
	case typedef_t::ANY:
		out << "any";
		break;
	case typedef_t::ENUM:
		out << "enum";
		break;
	case typedef_t::STRUCT:
		out << "struct";
		break;
	case typedef_t::UNION:
		out << "union";
		break;
	case typedef_t::CLASS:
		out << "class";
		break;
	}

	return out;
}
