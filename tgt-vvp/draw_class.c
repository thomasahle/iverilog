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
       * Format: .constraint_bound <classptr>, "<constraint_name>", <prop_idx>, "<op>", <soft>, <has_const>, <value/prop2_idx>, <sysfunc_type>, <sysfunc_arg>, <weight>, <weight_per_value>, <has_cond>, <cond_prop>, "<cond_op>", <cond_has_const>, <cond_value> ;
       * These are runtime-enforceable bounds like: value > 0, value < limit
       * For system function constraints (e.g., $countones(x) == 1):
       *   sysfunc_type: 0=NONE, 1=COUNTONES, 2=ONEHOT, 3=ONEHOT0, 4=ISUNKNOWN, 5=CLOG2
       *   sysfunc_arg: property index that is the function argument
       * For weighted dist constraints:
       *   weight: the weight value (default 1)
       *   weight_per_value: 1 for := (per value), 0 for :/ (per range)
       * For implication constraints (cond -> body):
       *   has_cond: 1 if this bound has a guard condition
       *   cond_prop: property index for condition expression
       *   cond_op: condition comparison operator
       *   cond_has_const: 1 if condition compares to constant
       *   cond_value: constant value or property index for condition
       */
      unsigned nbounds = ivl_type_simple_bounds(classtype);
      for (unsigned bidx = 0; bidx < nbounds; bidx++) {
	    const char* cons_name = ivl_type_simple_bound_constraint_name(classtype, bidx);
	    unsigned prop_idx = ivl_type_simple_bound_prop(classtype, bidx);
	    char op = ivl_type_simple_bound_op(classtype, bidx);
	    int soft = ivl_type_simple_bound_soft(classtype, bidx);
	    int has_const = ivl_type_simple_bound_has_const(classtype, bidx);
	    unsigned sysfunc_type = ivl_type_simple_bound_sysfunc_type(classtype, bidx);
	    unsigned sysfunc_arg = ivl_type_simple_bound_sysfunc_arg(classtype, bidx);
	    int64_t weight = ivl_type_simple_bound_weight(classtype, bidx);
	    int weight_per_value = ivl_type_simple_bound_weight_per_value(classtype, bidx);
	    int has_cond = ivl_type_simple_bound_has_cond(classtype, bidx);
	    unsigned cond_prop = ivl_type_simple_bound_cond_prop(classtype, bidx);
	    char cond_op = ivl_type_simple_bound_cond_op(classtype, bidx);
	    int cond_has_const = ivl_type_simple_bound_cond_has_const(classtype, bidx);

	    int has_prop_offset = ivl_type_simple_bound_has_prop_offset(classtype, bidx);

	    /* For property+offset constraints (e.g., y <= x + 10), use lowercase operator
	     * to signal that the value contains packed prop_idx and offset:
	     * 'g' = >= with offset, 'l' = <= with offset, 'e' = == with offset, etc.
	     */
	    char effective_op = op;
	    if (has_prop_offset) {
		  switch (op) {
			case 'G': effective_op = 'g'; break;  /* >= with offset */
			case 'L': effective_op = 'l'; break;  /* <= with offset */
			case '>': effective_op = 'h'; break;  /* > with offset (h = higher) */
			case '<': effective_op = 'j'; break;  /* < with offset (j = junior/less) */
			case '=': effective_op = 'e'; break;  /* == with offset */
			case '!': effective_op = 'n'; break;  /* != with offset */
			default: break;
		  }
	    }

	    fprintf(vvp_out, ".constraint_bound C%p, \"%s\", %u, \"%c\", %d, %d, ",
		    classtype, cons_name ? cons_name : "", prop_idx, effective_op, soft, has_const);
	    if (op == 's' || has_prop_offset) {
		  /* Property-based constraint with optional offset:
		   * For 's' operator: arr.size() == src_prop + offset
		   * For property+offset: y <= x + 10
		   * We need both:
		   * - prop2_idx (source property to read value from)
		   * - const_val (offset to add to source property value)
		   * We pack these together: lower 32 bits = signed offset, upper 32 bits = src_prop_idx
		   */
		  unsigned prop2_idx = ivl_type_simple_bound_prop2(classtype, bidx);
		  int64_t offset_val = 0;
		  if (has_const) {
			offset_val = ivl_type_simple_bound_const(classtype, bidx);
		  }
		  /* Pack: offset in lower 32 bits (signed), prop2_idx in upper 32 bits */
		  int64_t packed_val = ((int64_t)prop2_idx << 32) | (offset_val & 0xFFFFFFFF);
		  fprintf(vvp_out, "%" PRId64 ", %u, %u, %" PRId64 ", %d, ",
			  packed_val, sysfunc_type, sysfunc_arg, weight, weight_per_value);
	    } else if (has_const) {
		  int64_t const_val = ivl_type_simple_bound_const(classtype, bidx);
		  fprintf(vvp_out, "%" PRId64 ", %u, %u, %" PRId64 ", %d, ",
			  const_val, sysfunc_type, sysfunc_arg, weight, weight_per_value);
	    } else {
		  unsigned prop2_idx = ivl_type_simple_bound_prop2(classtype, bidx);
		  fprintf(vvp_out, "%u, %u, %u, %" PRId64 ", %d, ",
			  prop2_idx, sysfunc_type, sysfunc_arg, weight, weight_per_value);
	    }
	    /* Emit condition fields */
	    if (cond_has_const) {
		  int64_t cond_const = ivl_type_simple_bound_cond_const(classtype, bidx);
		  fprintf(vvp_out, "%d, %u, \"%c\", %d, %" PRId64 " ;\n",
			  has_cond, cond_prop, cond_op, cond_has_const, cond_const);
	    } else {
		  unsigned cond_prop2 = ivl_type_simple_bound_cond_prop2(classtype, bidx);
		  fprintf(vvp_out, "%d, %u, \"%c\", %d, %u ;\n",
			  has_cond, cond_prop, cond_op, cond_has_const, cond_prop2);
	    }
      }

      /* Emit unique constraints - ensure array elements have distinct values.
       * Format: .constraint_unique <classptr>, <prop_idx> ;
       */
      unsigned unique_count = ivl_type_unique_constraints(classtype);
      for (unsigned uidx = 0; uidx < unique_count; uidx++) {
	    unsigned prop_idx = ivl_type_unique_constraint_prop(classtype, uidx);
	    fprintf(vvp_out, ".constraint_unique C%p, %u ;\n",
		    classtype, prop_idx);
      }

      /* Emit enum constraints for rand enum properties.
       * Format: .enum_bound <classptr>, <prop_idx>, <num_values>, <value1>, <value2>, ... ;
       * This ensures randomization picks from valid enum values.
       */
      for (idx = 0; idx < ivl_type_properties(classtype); idx++) {
	    int rand_flag = ivl_type_prop_rand(classtype, idx);
	    if (rand_flag == 0) continue;  /* Only for rand/randc properties */

	    ivl_type_t ptype = ivl_type_prop_type(classtype, idx);
	    ivl_enumtype_t enum_type = ivl_type_enumtype(ptype);
	    if (enum_type == NULL) continue;  /* Only for enum types */

	    unsigned num_values = ivl_enum_names(enum_type);
	    if (num_values == 0) continue;

	    fprintf(vvp_out, ".enum_bound C%p, %d, %u",
		    classtype, idx, num_values);
	    for (unsigned vidx = 0; vidx < num_values; vidx++) {
		  const char* bits = ivl_enum_bits(enum_type, vidx);
		  /* Convert bits string to integer value.
		   * NOTE: The bits string is LSB-first (bit 0 at index 0),
		   * so we iterate from end to start to build the value correctly.
		   */
		  int64_t val = 0;
		  if (bits) {
			size_t len = strlen(bits);
			for (size_t i = len; i > 0; i--) {
			      char c = bits[i-1];
			      val = (val << 1) | (c == '1' ? 1 : 0);
			}
		  }
		  fprintf(vvp_out, ", %" PRId64, val);
	    }
	    fprintf(vvp_out, " ;\n");
      }

      /* Register class with factory for UVM-style creation by name.
       * This allows run_test("classname") and type_id::create() to work. */
      fprintf(vvp_out, ".factory \"%s\", C%p ;\n", ivl_type_name(classtype), classtype);
}
