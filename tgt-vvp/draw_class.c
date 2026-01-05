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

/*
 * Helper to emit unpacked array dimensions like [3:0][7:0]
 */
static void show_unpacked_dims(ivl_type_t ptype)
{
      unsigned ndims = ivl_type_uarray_dimensions(ptype);
      unsigned idx;
      for (idx = 0; idx < ndims; idx++) {
	    fprintf(vvp_out, " [%d:%d]",
		    ivl_type_uarray_msb(ptype, idx),
		    ivl_type_uarray_lsb(ptype, idx));
      }
}

static void show_prop_type(ivl_type_t ptype)
{
      ivl_variable_type_t data_type = ivl_type_base(ptype);
      unsigned packed_dimensions = ivl_type_packed_dimensions(ptype);

      /* Handle unpacked arrays by unwrapping to get element type */
      if (ivl_type_is_uarray(ptype)) {
	    ivl_type_t element = ivl_type_uarray_element(ptype);
	    /* Emit element type first */
	    show_prop_type(element);
	    /* Then emit unpacked dimensions */
	    show_unpacked_dims(ptype);
	    return;
      }

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
	  case IVL_VT_ASSOC:
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
	    int rand_flag = ivl_type_prop_rand(classtype, idx);
	    const char* rand_str = "";
	    if (rand_flag == 1) rand_str = " rand";
	    else if (rand_flag == 2) rand_str = " randc";
	    fprintf(vvp_out, " %3d: \"%s\", ", idx, ivl_type_prop_name(classtype,idx));
	    show_prop_type(ivl_type_prop_type(classtype,idx));
	    fprintf(vvp_out, "%s\n", rand_str);
      }

      fprintf(vvp_out, " ;\n");

      /* Emit constraint information if any constraints exist.
       * Constraints are stored but not yet enforced at runtime. */
      unsigned ncons = ivl_type_constraints(classtype);
      if (ncons > 0) {
	    unsigned cidx;
	    fprintf(vvp_out, "; Class %s has %u constraint(s):\n",
		    ivl_type_name(classtype), ncons);
	    for (cidx = 0; cidx < ncons; cidx++) {
		  const char* cname = ivl_type_constraint_name(classtype, cidx);
		  int soft = ivl_type_constraint_soft(classtype, cidx);
		  fprintf(vvp_out, ";   %s: %s\n", cname, soft ? "soft" : "hard");
	    }
      }

      /* Emit simple bounds for constraint solver.
       * Format: .constraint_bound <classptr>, "<constraint_name>", <prop_idx>, "<op>", <soft>, <has_const>, <value/prop2_idx> ;
       * These are runtime-enforceable bounds like: value > 0, value < limit
       */
      unsigned nbounds = ivl_type_simple_bounds(classtype);
      for (unsigned bidx = 0; bidx < nbounds; bidx++) {
	    const char* cons_name = ivl_type_simple_bound_constraint_name(classtype, bidx);
	    unsigned prop_idx = ivl_type_simple_bound_prop(classtype, bidx);
	    char op = ivl_type_simple_bound_op(classtype, bidx);
	    int soft = ivl_type_simple_bound_soft(classtype, bidx);
	    int has_const = ivl_type_simple_bound_has_const(classtype, bidx);

	    fprintf(vvp_out, ".constraint_bound C%p, \"%s\", %u, \"%c\", %d, %d, ",
		    classtype, cons_name ? cons_name : "", prop_idx, op, soft, has_const);
	    if (has_const) {
		  int64_t const_val = ivl_type_simple_bound_const(classtype, bidx);
		  fprintf(vvp_out, "%" PRId64 " ;\n", const_val);
	    } else {
		  unsigned prop2_idx = ivl_type_simple_bound_prop2(classtype, bidx);
		  fprintf(vvp_out, "%u ;\n", prop2_idx);
	    }
      }

      /* Register class with factory for UVM-style creation by name.
       * This allows run_test("classname") and type_id::create() to work. */
      fprintf(vvp_out, ".factory \"%s\", C%p ;\n", ivl_type_name(classtype), classtype);
}
