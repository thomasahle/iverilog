/*
 * Copyright (c) 2012-2025 Stephen Williams (steve@icarus.com)
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
# include  <string.h>
# include  <assert.h>

void darray_new(ivl_type_t element_type, unsigned size_reg)
{
      int wid;
      const char*signed_char;
      ivl_variable_type_t type = ivl_type_base(element_type);

      if ((type == IVL_VT_BOOL) || (type == IVL_VT_LOGIC)) {
	    wid = ivl_type_packed_width(element_type);
	    signed_char = ivl_type_signed(element_type) ? "s" : "";
      } else {
	      // REAL or STRING objects are not packable.
	    assert(ivl_type_packed_dimensions(element_type) == 0);
	    wid = 0;
	    signed_char = "";
      }

      switch (type) {
	  case IVL_VT_REAL:
	    fprintf(vvp_out, "    %%new/darray %u, \"r\";\n",
	                     size_reg);
	    break;

	  case IVL_VT_STRING:
	    fprintf(vvp_out, "    %%new/darray %u, \"S\";\n",
	                     size_reg);
	    break;

	  case IVL_VT_BOOL:
	    fprintf(vvp_out, "    %%new/darray %u, \"%sb%d\";\n",
	                     size_reg, signed_char, wid);
	    break;

	  case IVL_VT_LOGIC:
	    fprintf(vvp_out, "    %%new/darray %u, \"%sv%d\";\n",
	                     size_reg, signed_char, wid);
	    break;

	  case IVL_VT_CLASS:
	  case IVL_VT_DARRAY:
	  case IVL_VT_QUEUE:
	    // Dynamic arrays, queues, and class objects are all stored as objects
	    fprintf(vvp_out, "    %%new/darray %u, \"o\";\n",
	                     size_reg);
	    break;

	  default:
	    assert(0);
	    break;
      }

      clr_word(size_reg);
}

static int eval_darray_new(ivl_expr_t ex)
{
      int errors = 0;
      unsigned size_reg = allocate_word();
      ivl_expr_t size_expr = ivl_expr_oper1(ex);
      ivl_expr_t init_expr = ivl_expr_oper2(ex);
      draw_eval_expr_into_integer(size_expr, size_reg);

	// The new function has a net_type that contains the details
	// of the type.
      ivl_type_t net_type = ivl_expr_net_type(ex);
      assert(net_type);

      ivl_type_t element_type = ivl_type_element(net_type);
      assert(element_type);

      darray_new(element_type, size_reg);

      if (init_expr && ivl_expr_type(init_expr)==IVL_EX_ARRAY_PATTERN) {
	    unsigned idx;
	    switch (ivl_type_base(element_type)) {
		case IVL_VT_BOOL:
		case IVL_VT_LOGIC:
		  for (idx = 0 ; idx < ivl_expr_parms(init_expr) ; idx += 1) {
			draw_eval_vec4(ivl_expr_parm(init_expr,idx));
			fprintf(vvp_out, "    %%ix/load 3, %u, 0;\n", idx);
			fprintf(vvp_out, "    %%set/dar/obj/vec4 3;\n");
			// Note: %set/dar/obj/vec4 pops the vec4 value, no %pop/vec4 needed
		  }
		  break;
		case IVL_VT_REAL:
		  for (idx = 0 ; idx < ivl_expr_parms(init_expr) ; idx += 1) {
			draw_eval_real(ivl_expr_parm(init_expr,idx));
			fprintf(vvp_out, "    %%ix/load 3, %u, 0;\n", idx);
			fprintf(vvp_out, "    %%set/dar/obj/real 3;\n");
			// Note: %set/dar/obj/real pops the real value, no %pop/real needed
		  }
		  break;
		case IVL_VT_STRING:
		  for (idx = 0 ; idx < ivl_expr_parms(init_expr) ; idx += 1) {
			draw_eval_string(ivl_expr_parm(init_expr,idx));
			fprintf(vvp_out, "    %%ix/load 3, %u, 0;\n", idx);
			fprintf(vvp_out, "    %%set/dar/obj/str 3;\n");
			// Note: %set/dar/obj/str pops the string value, no %pop/str needed
		  }
		  break;
		default:
		  fprintf(vvp_out, "; ERROR: Sorry, this type not supported here.\n");
		  errors += 1;
		  break;
	    }
      } else if (init_expr) {
	    if (ivl_expr_value(init_expr) == IVL_VT_DARRAY ||
		ivl_expr_value(init_expr) == IVL_VT_QUEUE) {
		  /* Copy from another dynamic array or queue */
		  ivl_signal_t sig = ivl_expr_signal(init_expr);
		  if (sig) {
			fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
			fprintf(vvp_out, "    %%scopy;\n");
		  } else {
			/* Handle the case where init_expr is not a simple signal */
			draw_eval_object(init_expr);
			fprintf(vvp_out, "    %%scopy;\n");
		  }
	    } else if (number_is_immediate(size_expr,32,0)) {
	      /* In this case, there is an init expression, the
		 expression is NOT an array_pattern, and the size
		 expression used to calculate the size of the array is
		 a constant. Generate an unrolled set of assignments. */
	    long idx;
	    long cnt = get_number_immediate(size_expr);
	    unsigned wid;
	    switch (ivl_type_base(element_type)) {
		case IVL_VT_BOOL:
		case IVL_VT_LOGIC:
		  wid = ivl_type_packed_width(element_type);
		  for (idx = 0 ; idx < cnt ; idx += 1) {
			draw_eval_vec4(init_expr);
			fprintf(vvp_out, "    %%parti/%c %u, %ld, 6;\n",
                                ivl_expr_signed(init_expr) ? 's' : 'u', wid, idx * wid);
			fprintf(vvp_out, "    %%ix/load 3, %ld, 0;\n", cnt - idx - 1);
			fprintf(vvp_out, "    %%set/dar/obj/vec4 3;\n");
			// Note: %parti modifies in-place, %set pops - stack empty
		  }
		  break;
		case IVL_VT_REAL:
		  for (idx = 0 ; idx < cnt ; idx += 1) {
			draw_eval_real(init_expr);
			fprintf(vvp_out, "    %%ix/load 3, %ld, 0;\n", idx);
			fprintf(vvp_out, "    %%set/dar/obj/real 3;\n");
			// Note: %set/dar/obj/real pops the real value
		  }
		  break;
		case IVL_VT_STRING:
		  for (idx = 0 ; idx < cnt ; idx += 1) {
			draw_eval_string(init_expr);
			fprintf(vvp_out, "    %%ix/load 3, %ld, 0;\n", idx);
			fprintf(vvp_out, "    %%set/dar/obj/str 3;\n");
			// Note: %set/dar/obj/str pops the string value
		  }
		  break;
		default:
		  fprintf(vvp_out, "; ERROR: Sorry, this type not supported here.\n");
		  errors += 1;
		  break;
	    }
	    } else {
		fprintf(vvp_out, "; ERROR: Sorry, I don't know how to work with this size expr.\n");
		errors += 1;
	    }
      }

      return errors;
}

static int eval_class_new(ivl_expr_t ex)
{
      ivl_type_t class_type = ivl_expr_net_type(ex);
      fprintf(vvp_out, "    %%new/cobj C%p;\n", class_type);
      return 0;
}

static int eval_object_null(ivl_expr_t ex)
{
      (void)ex; /* Parameter is not used. */
      fprintf(vvp_out, "    %%null;\n");
      return 0;
}

/*
 * Evaluate a virtual interface property access as an object.
 * This loads the class object stored in a virtual interface member.
 */
static int eval_object_vifprop(ivl_expr_t expr)
{
      ivl_expr_t vif_expr = ivl_expr_vifprop_base(expr);
      const char* member_name = ivl_expr_vifprop_member(expr);

      /* Evaluate the virtual interface expression to get scope on object stack */
      draw_eval_object(vif_expr);

      /* Load the object from the vif member */
      fprintf(vvp_out, "    %%vif/load/obj \"%s\";\n", member_name);

      /* Pop the vif scope but keep the loaded object */
      fprintf(vvp_out, "    %%pop/obj 1, 1;\n");

      return 0;
}

static int eval_object_property(ivl_expr_t expr)
{
      ivl_signal_t sig = ivl_expr_signal(expr);
      ivl_expr_t base = ivl_expr_property_base(expr);
      unsigned pidx = ivl_expr_property_idx(expr);

      int idx = 0;
      ivl_expr_t idx_expr = 0;

	/* If there is an array index expression, then this is an
	   array'ed property, and we need to calculate the index for
	   the expression. */
      if ( (idx_expr = ivl_expr_oper1(expr)) ) {
	    idx = allocate_word();
	    draw_eval_expr_into_integer(idx_expr, idx);
      }

      if (base) {
	    // Nested property access - evaluate base expression first
	    draw_eval_object(base);
      } else {
	    // Direct property access - load signal
	    fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
      }

      /* Check if this is a darray property with an index.
         For darray properties, we need to load the darray first,
         then access the element separately. */
      ivl_type_t class_type = NULL;
      if (sig) {
	    class_type = ivl_signal_net_type(sig);
      } else if (base) {
	    class_type = ivl_expr_net_type(base);
      }
      ivl_type_t prop_type = class_type ? ivl_type_prop_type(class_type, pidx) : NULL;

      ivl_variable_type_t prop_base = prop_type ? ivl_type_base(prop_type) : IVL_VT_NO_TYPE;
      if ((prop_base == IVL_VT_DARRAY || prop_base == IVL_VT_QUEUE) && idx != 0) {
	    /* Load the darray/queue property without index */
	    fprintf(vvp_out, "    %%prop/obj %u, 0; Load %s property\n", pidx,
		    prop_base == IVL_VT_QUEUE ? "queue" : "darray");
	    fprintf(vvp_out, "    %%pop/obj 1, 1;\n");
	    /* Access element at index */
	    fprintf(vvp_out, "    %%get/dar/obj/o %d; Load %s element\n", idx,
		    prop_base == IVL_VT_QUEUE ? "queue" : "darray");
      } else {
	    /* Normal property access (with or without index for static arrays) */
	    fprintf(vvp_out, "    %%prop/obj %u, %d; eval_object_property\n", pidx, idx);
	    fprintf(vvp_out, "    %%pop/obj 1, 1;\n");
      }

      if (idx != 0) clr_word(idx);
      return 0;
}

static int eval_object_shallowcopy(ivl_expr_t ex)
{
      int errors = 0;
      ivl_expr_t dest = ivl_expr_oper1(ex);
      ivl_expr_t src  = ivl_expr_oper2(ex);

      errors += draw_eval_object(dest);
      errors += draw_eval_object(src);

	/* The %scopy opcode pops the top of the object stack as the
	   source object, and shallow-copies it to the new top, the
	   destination object. The destination is left on the top of
	   the stack. */
      fprintf(vvp_out, "    %%scopy;\n");

      return errors;
}

static int eval_object_signal(ivl_expr_t expr)
{
      ivl_signal_t sig = ivl_expr_signal(expr);
      ivl_expr_t word_ex = ivl_expr_oper1(expr);

	/* Check if this is a queue/darray with an index expression */
      ivl_variable_type_t sig_type = ivl_signal_data_type(sig);
      if ((sig_type == IVL_VT_QUEUE || sig_type == IVL_VT_DARRAY) && word_ex) {
	    /* Load element from queue/darray at index */
	    draw_eval_expr_into_integer(word_ex, 3);
	    fprintf(vvp_out, "    %%load/dar/o v%p_0;\n", sig);
	    return 0;
      }

	/* Simple case: This is a simple variable. Generate a load
	   statement to load the string into the stack. */
      if (ivl_signal_dimensions(sig) == 0) {
	    fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
	    return 0;
      }

	/* There is a word select expression, so load the index into a
	   register and load from the array. */
      int word_ix = allocate_word();
      draw_eval_expr_into_integer(word_ex, word_ix);
      fprintf(vvp_out, "    %%load/obja v%p, %d;\n", sig, word_ix);
      clr_word(word_ix);

      return 0;
}

static int eval_object_ufunc(ivl_expr_t ex)
{
      draw_ufunc_object(ex);
      return 0;
}

/*
 * Handle scope expressions - used for virtual interface assignment
 * where an interface instance (scope) is assigned to a VIF property.
 * Emit a %load/scope opcode to push the scope reference onto the object stack.
 */
static int eval_object_scope(ivl_expr_t ex)
{
      ivl_scope_t scope = ivl_expr_scope(ex);
      fprintf(vvp_out, "    %%load/scope S_%p; virtual interface scope\n", scope);
      return 0;
}

/*
 * Handle pop_back/pop_front for queues of objects.
 */
static int draw_darray_pop_object(ivl_expr_t expr)
{
      const char*fb;

      if (strcmp(ivl_expr_name(expr), "$ivl_queue_method$pop_back")==0)
	    fb = "b";
      else
	    fb = "f";

      ivl_expr_t arg = ivl_expr_parm(expr, 0);

      /* Handle property expressions - load the containing object and
         use a property queue pop opcode. For objects, this returns the
         object on the object stack. */
      if (ivl_expr_type(arg) == IVL_EX_PROPERTY) {
	    ivl_signal_t sig = ivl_expr_signal(arg);
	    ivl_expr_t base = ivl_expr_property_base(arg);
	    unsigned prop_idx = ivl_expr_property_idx(arg);

	    if (base) {
		  /* Nested property access - evaluate base expression */
		  draw_eval_object(base);
	    } else {
		  /* Direct property access - load the 'this' signal */
		  fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
	    }

	    /* Pop from the queue property and push result to object stack */
	    fprintf(vvp_out, "    %%prop/q/pop%s/o %u;\n", fb, prop_idx);
	    /* Pop the base object but keep the popped element */
	    fprintf(vvp_out, "    %%pop/obj 1, 1;\n");
	    return 0;
      }

      /* Simple signal case - the signal is a queue variable */
      assert(ivl_expr_type(arg) == IVL_EX_SIGNAL);
      fprintf(vvp_out, "    %%qpop/%s/obj v%p_0;\n", fb, ivl_expr_signal(arg));
      return 0;
}

/*
 * Handle $ivl_factory_create system function.
 * This creates a class object by looking up the class type name in the
 * UVM factory registry at runtime.
 */
static int eval_object_sfunc(ivl_expr_t ex)
{
      const char*name = ivl_expr_name(ex);

      /* Handle queue pop methods for object queues */
      if (strcmp(name, "$ivl_queue_method$pop_back") == 0 ||
          strcmp(name, "$ivl_queue_method$pop_front") == 0) {
	    return draw_darray_pop_object(ex);
      }

      if (strcmp(name, "$ivl_factory_create") == 0) {
	    /* $ivl_factory_create(type_name)
	     * - Evaluate the string argument (type name)
	     * - Call %factory/create to look up and create the object
	     */
	    ivl_expr_t arg = ivl_expr_parm(ex, 0);
	    draw_eval_string(arg);
	    fprintf(vvp_out, "    %%factory/create;\n");
	    return 0;
      }

      /* Array locator methods - return a queue of indices or elements */
      if (strncmp(name, "$ivl_array_locator$", 19) == 0) {
	    const char* method = name + 19; /* Skip "$ivl_array_locator$" prefix */
	    ivl_expr_t queue_arg = ivl_expr_parm(ex, 0);
	    unsigned nparms = ivl_expr_parms(ex);

	    /* Handle "inside" variants: find_index_inside, find_first_index_inside, etc.
	     * Args: queue, count, val1, val2, ..., valN
	     * These check if item is in the set {val1, val2, ..., valN}
	     */
	    if (strstr(method, "_inside") != NULL) {
		  int mode = 0;
		  if (strncmp(method, "find_first_index_inside", 23) == 0) mode = 1;
		  else if (strncmp(method, "find_last_index_inside", 22) == 0) mode = 2;
		  else if (strncmp(method, "find_inside", 11) == 0) mode = 3;
		  else if (strncmp(method, "find_first_inside", 17) == 0) mode = 4;
		  else if (strncmp(method, "find_last_inside", 16) == 0) mode = 5;

		  /* Get the count of values (second parameter) */
		  ivl_expr_t count_arg = ivl_expr_parm(ex, 1);
		  unsigned count = 0;
		  if (ivl_expr_type(count_arg) == IVL_EX_NUMBER) {
			const char*bits = ivl_expr_bits(count_arg);
			unsigned wid = ivl_expr_width(count_arg);
			for (unsigned i = 0; i < wid; i++) {
			      if (bits[i] == '1') count |= (1 << i);
			}
		  }

		  /* Evaluate the queue onto object stack */
		  draw_eval_object(queue_arg);

		  /* Push each value in the set onto vec4 stack */
		  for (unsigned i = 0; i < count; i++) {
			ivl_expr_t val_arg = ivl_expr_parm(ex, 2 + i);
			draw_eval_vec4(val_arg);
		  }

		  /* Emit qfind_inside opcode with mode and count */
		  fprintf(vvp_out, "    %%qfind_inside %d, %u; // %s\n", mode, count, method);
		  return 0;
	    }

	    /* Determine the locator mode:
	     * 0=find_index, 1=find_first_index, 2=find_last_index (return indices)
	     * 3=find, 4=find_first, 5=find_last (return elements)
	     */
	    int mode = 0;
	    if (strcmp(method, "find_first_index") == 0) mode = 1;
	    else if (strcmp(method, "find_last_index") == 0) mode = 2;
	    else if (strcmp(method, "find") == 0) mode = 3;
	    else if (strcmp(method, "find_first") == 0) mode = 4;
	    else if (strcmp(method, "find_last") == 0) mode = 5;

	    if (nparms >= 4) {
		  /* item.property OP value pattern - use %qfind_prop opcode */
		  /* Args: queue, prop_idx, cmp_op, value */
		  ivl_expr_t prop_idx_arg = ivl_expr_parm(ex, 1);
		  ivl_expr_t cmp_op_arg = ivl_expr_parm(ex, 2);
		  ivl_expr_t cmp_arg = ivl_expr_parm(ex, 3);

		  /* Evaluate the queue onto object stack */
		  draw_eval_object(queue_arg);

		  /* Evaluate the comparison value onto vec4 stack */
		  draw_eval_vec4(cmp_arg);

		  /* Get the property index (should be a constant) */
		  int prop_idx = 0;
		  if (ivl_expr_type(prop_idx_arg) == IVL_EX_NUMBER) {
			const char*bits = ivl_expr_bits(prop_idx_arg);
			unsigned wid = ivl_expr_width(prop_idx_arg);
			for (unsigned i = 0; i < wid; i++) {
			      if (bits[i] == '1') prop_idx |= (1 << i);
			}
		  }

		  /* Get the comparison operator (should be a constant) */
		  int cmp_op = 0;  /* 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge */
		  if (ivl_expr_type(cmp_op_arg) == IVL_EX_NUMBER) {
			const char*bits = ivl_expr_bits(cmp_op_arg);
			unsigned wid = ivl_expr_width(cmp_op_arg);
			for (unsigned i = 0; i < wid; i++) {
			      if (bits[i] == '1') cmp_op |= (1 << i);
			}
		  }

		  /* Emit the find_prop opcode with mode, property index, and cmp_op */
		  fprintf(vvp_out, "    %%qfind_prop %d, %d, %d; // %s (item.property pattern)\n", mode, prop_idx, cmp_op, method);
		  return 0;
	    }

	    if (nparms >= 3) {
		  /* item OP value pattern - use %qfind opcode with cmp_op */
		  /* Args: queue, cmp_op, value */
		  ivl_expr_t cmp_op_arg = ivl_expr_parm(ex, 1);
		  ivl_expr_t cmp_arg = ivl_expr_parm(ex, 2);

		  /* Evaluate the queue onto object stack */
		  draw_eval_object(queue_arg);

		  /* Evaluate the comparison value onto vec4 stack */
		  draw_eval_vec4(cmp_arg);

		  /* Get the comparison operator (should be a constant) */
		  int cmp_op = 0;  /* 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge */
		  if (ivl_expr_type(cmp_op_arg) == IVL_EX_NUMBER) {
			const char*bits = ivl_expr_bits(cmp_op_arg);
			unsigned wid = ivl_expr_width(cmp_op_arg);
			for (unsigned i = 0; i < wid; i++) {
			      if (bits[i] == '1') cmp_op |= (1 << i);
			}
		  }

		  /* Emit the find opcode with mode and cmp_op */
		  fprintf(vvp_out, "    %%qfind %d, %d; // %s\n", mode, cmp_op, method);
		  return 0;
	    }

	    if (nparms >= 2) {
		  /* Legacy: item == value (no cmp_op parameter) - use default equality */
		  ivl_expr_t cmp_arg = ivl_expr_parm(ex, 1);

		  /* Evaluate the queue onto object stack */
		  draw_eval_object(queue_arg);

		  /* Evaluate the comparison value onto vec4 stack */
		  draw_eval_vec4(cmp_arg);

		  /* Emit the find opcode with mode and default cmp_op=0 (equality) */
		  fprintf(vvp_out, "    %%qfind %d, 0; // %s (equality)\n", mode, method);
		  return 0;
	    }

	    /* No comparison value - complex 'with' clause not supported */
	    /* Return empty queue */
	    fprintf(vvp_out, "    %%new/darray 32, \"sb32\"; array locator (complex with clause)\n");
	    return 0;
      }

      /* Queue min/max methods - return a queue with min/max element(s) */
      if (strcmp(name, "$ivl_queue_method$min") == 0 ||
          strcmp(name, "$ivl_queue_method$max") == 0) {
	    ivl_expr_t arg = ivl_expr_parm(ex, 0);
	    const char* op = (strcmp(name, "$ivl_queue_method$min") == 0) ? "min" : "max";

	    /* Handle property expressions (obj.queue_prop.min()) */
	    if (ivl_expr_type(arg) == IVL_EX_PROPERTY) {
		  draw_eval_object(arg);
		  fprintf(vvp_out, "    %%qprop/%s; // Queue property %s\n", op, op);
		  return 0;
	    }

	    /* Simple signal case - the signal is a queue variable */
	    assert(ivl_expr_type(arg) == IVL_EX_SIGNAL);
	    fprintf(vvp_out, "    %%q%s v%p_0;\n", op, ivl_expr_signal(arg));
	    return 0;
      }

      /* Queue unique() method - returns queue with unique elements */
      if (strcmp(name, "$ivl_queue_method$unique") == 0) {
	    ivl_expr_t arg = ivl_expr_parm(ex, 0);

	    /* Handle property expressions (obj.queue_prop.unique()) */
	    if (ivl_expr_type(arg) == IVL_EX_PROPERTY) {
		  draw_eval_object(arg);
		  fprintf(vvp_out, "    %%qprop/unique; // Queue property unique\n");
		  return 0;
	    }

	    /* Simple signal case - the signal is a queue variable */
	    assert(ivl_expr_type(arg) == IVL_EX_SIGNAL);
	    fprintf(vvp_out, "    %%qunique v%p_0;\n", ivl_expr_signal(arg));
	    return 0;
      }

      fprintf(vvp_out, "; ERROR: eval_object_sfunc: Unknown system function '%s'\n", name);
      return 1;
}

/*
 * Handle select expressions (e.g., q[i]) where q is a queue of class objects.
 * This is used when a queue element is passed as an object argument, such as
 * the 'this' parameter when calling q[i].method().
 */
static int eval_object_select(ivl_expr_t ex)
{
      ivl_expr_t subexpr = ivl_expr_oper1(ex);
      ivl_expr_t base = ivl_expr_oper2(ex);

      /* Get the signal from the subexpression (the queue/darray variable) */
      ivl_signal_t sig = ivl_expr_signal(subexpr);
      if (sig) {
	    ivl_variable_type_t sig_type = ivl_signal_data_type(sig);
	    /* Check if the signal is a queue or darray */
	    if (sig_type == IVL_VT_QUEUE || sig_type == IVL_VT_DARRAY) {
		  /* Evaluate the index into register 3 */
		  draw_eval_expr_into_integer(base, 3);

		  /* Load the queue/darray onto the object stack */
		  fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);

		  /* Get the element at the index (pops queue, pushes element) */
		  fprintf(vvp_out, "    %%get/dar/obj/o 3;\n");

		  return 0;
	    }
      }

      fprintf(vvp_out, "; ERROR: eval_object_select: Unsupported - sig=%p, subexpr_type=%d\n",
              (void*)sig, subexpr ? ivl_expr_type(subexpr) : -1);
      return 1;
}

int draw_eval_object(ivl_expr_t ex)
{
      switch (ivl_expr_type(ex)) {

	  case IVL_EX_SFUNC:
	    return eval_object_sfunc(ex);

	  case IVL_EX_NEW:
	    switch (ivl_expr_value(ex)) {
		case IVL_VT_CLASS:
		  return eval_class_new(ex);
		case IVL_VT_DARRAY:
		  return eval_darray_new(ex);
		default:
		  fprintf(vvp_out, "; ERROR: draw_eval_object: Invalid type (%d) for <new>\n",
			  ivl_expr_value(ex));
		  return 0;
	    }

	  case IVL_EX_NULL:
	    return eval_object_null(ex);

	  case IVL_EX_PROPERTY:
	    return eval_object_property(ex);

	  case IVL_EX_VIFPROP:
	    return eval_object_vifprop(ex);

	  case IVL_EX_SHALLOWCOPY:
	    return eval_object_shallowcopy(ex);

	  case IVL_EX_SIGNAL:
	    return eval_object_signal(ex);

	  case IVL_EX_UFUNC:
	    return eval_object_ufunc(ex);

	  case IVL_EX_SCOPE:
	    return eval_object_scope(ex);

	  case IVL_EX_SELECT:
	    return eval_object_select(ex);

	  default:
	    fprintf(vvp_out, "; ERROR: draw_eval_object: Invalid expression type %d\n", ivl_expr_type(ex));
	    return 1;

      }
}
