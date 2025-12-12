/*
 * Copyright (c) 2012 Stephen Williams (steve@icarus.com)
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


# include  "vvp_priv.h"
# include  <stdlib.h>
# include  <string.h>
# include  <assert.h>
# include  <inttypes.h>

static void show_prop_type_vector(ivl_type_t ptype)
{
      ivl_variable_type_t data_type = ivl_type_base(ptype);
      unsigned packed_dimensions = ivl_type_packed_dimensions(ptype);
      assert(packed_dimensions < 2);

      const char*signed_flag = ivl_type_signed(ptype)? "s" : "";
      char code = data_type==IVL_VT_BOOL? 'b' : 'L';

      if (packed_dimensions == 0) {
	    fprintf(vvp_out, "\"%s%c1\"", signed_flag, code);

      } else {
	    assert(packed_dimensions == 1);
	    /* LSB may be non-zero for vectors like bit [7:4] */
	    int msb = ivl_type_packed_msb(ptype,0);
	    int lsb = ivl_type_packed_lsb(ptype,0);
	    int width = msb >= lsb ? msb - lsb + 1 : lsb - msb + 1;
	    assert(width > 0);

	    fprintf(vvp_out, "\"%s%c%d\"", signed_flag, code, width);
      }
}

static void show_prop_type(ivl_type_t ptype)
{
      ivl_variable_type_t data_type = ivl_type_base(ptype);
      unsigned packed_dimensions = ivl_type_packed_dimensions(ptype);

      switch (data_type) {
	  case IVL_VT_REAL:
	    fprintf(vvp_out, "\"r\"");
	    break;
	  case IVL_VT_STRING:
	    fprintf(vvp_out, "\"S\"");
	    break;
	  case IVL_VT_BOOL:
	  case IVL_VT_LOGIC:
	    show_prop_type_vector(ptype);
	    break;
	  case IVL_VT_DARRAY:
	  case IVL_VT_QUEUE:
	  case IVL_VT_CLASS:
	    fprintf(vvp_out, "\"o\"");
	    if (packed_dimensions > 0) {
		  unsigned idx;
		  fprintf(vvp_out, " ");
		  for (idx = 0 ; idx < packed_dimensions ; idx += 1) {
			fprintf(vvp_out, "[%d:%d]",
				ivl_type_packed_msb(ptype,idx),
				ivl_type_packed_lsb(ptype,idx));
		  }
	    }
	    break;
	  case IVL_VT_NO_TYPE:
	    // Struct types return IVL_VT_NO_TYPE - treat as object
	    fprintf(vvp_out, "\"o\"");
	    break;
	  default:
	    fprintf(vvp_out, "\"<ERROR-no-type>\"");
	    assert(0);
	    break;
      }
}

void draw_class_in_scope(ivl_type_t classtype)
{
      int idx;
      ivl_type_t super = ivl_type_super(classtype);

      fprintf(vvp_out, "C%p  .class \"%s\" [%d]",
	      classtype, ivl_type_name(classtype), ivl_type_properties(classtype));

      /* If there is a parent class, emit reference to it */
      if (super) {
	    fprintf(vvp_out, " <C%p", super);
      }
      fprintf(vvp_out, "\n");

      for (idx = 0 ; idx < ivl_type_properties(classtype) ; idx += 1) {
	    fprintf(vvp_out, " %3d: \"%s\", ", idx, ivl_type_prop_name(classtype,idx));
	    show_prop_type(ivl_type_prop_type(classtype,idx));
	    fprintf(vvp_out, "\n");
      }

      fprintf(vvp_out, " ;\n");

      /* Register class with factory for UVM-style creation by name.
       * This allows run_test("classname") and type_id::create() to work. */
      fprintf(vvp_out, ".factory \"%s\", C%p ;\n", ivl_type_name(classtype), classtype);
}
