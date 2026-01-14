/*
 * Copyright (c) 2005-2016 Stephen Williams (steve@icarus.com)
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
# include  <stdlib.h>
# include  <assert.h>

/*
 * Handle passing an entire unpacked array to a function port.
 * We generate code to copy each element from the source array
 * to the port array element by element.
 */
static void function_argument_array(ivl_signal_t port, ivl_expr_t expr)
{
      unsigned count = ivl_signal_array_count(port);
      unsigned idx;

      /* The expression should be a signal reference to an array.
       * IVL_EX_ARRAY is the special case where an array is passed as a whole. */
      if (ivl_expr_type(expr) != IVL_EX_SIGNAL &&
	  ivl_expr_type(expr) != IVL_EX_ARRAY) {
	    fprintf(stderr, "XXXX function array argument is not a signal (type=%d)?!\n",
		    ivl_expr_type(expr));
	    vvp_errors += 1;
	    return;
      }

      ivl_signal_t src_sig = ivl_expr_signal(expr);
      if (ivl_signal_dimensions(src_sig) == 0) {
	    fprintf(stderr, "XXXX function array argument has no dimensions?!\n");
	    vvp_errors += 1;
	    return;
      }

      /* Copy element by element from source to port */
      for (idx = 0; idx < count; idx++) {
	    /* Load source element */
	    fprintf(vvp_out, "    %%ix/load 3, %u, 0;\n", idx);
	    fprintf(vvp_out, "    %%flag_set/imm 4, 0;\n");
	    fprintf(vvp_out, "    %%load/vec4a v%p, 3;\n", src_sig);

	    /* Store to port element */
	    fprintf(vvp_out, "    %%store/vec4a v%p, 3, 0;\n", port);
      }
}

static void function_argument_logic(ivl_signal_t port, ivl_expr_t expr)
{
      unsigned ewidth, pwidth;

      /* If port is an array, use the array copy helper */
      if (ivl_signal_dimensions(port) > 0) {
	    function_argument_array(port, expr);
	    return;
      }

      ewidth = ivl_expr_width(expr);
      pwidth = ivl_signal_width(port);

      draw_eval_vec4(expr);
      if (ewidth < pwidth)
	    fprintf(vvp_out, "    %%pad/u %u;\n", pwidth);

}

static void function_argument_real(ivl_signal_t port, ivl_expr_t expr)
{
      /* Array ports of real type are not supported for now */
      if (ivl_signal_dimensions(port) > 0) {
	    fprintf(stderr, "XXXX real array function arguments not supported\n");
	    vvp_errors += 1;
	    return;
      }

      draw_eval_real(expr);
}

static void draw_eval_function_argument(ivl_signal_t port, ivl_expr_t expr)
{
      ivl_variable_type_t dtype = ivl_signal_data_type(port);
      ivl_variable_type_t etype = ivl_expr_value(expr);

      /* Special case: if port expects scalar but expression is class,
       * this is likely a type parameter mismatch from specialized class
       * (method inherited from base class with default type param).
       * Use the expression's actual type instead. */
      if ((dtype == IVL_VT_BOOL || dtype == IVL_VT_LOGIC) &&
          etype == IVL_VT_CLASS) {
	    vvp_errors += draw_eval_object(expr);
	    return;
      }

      /* Special case: if port expects scalar but expression is string,
       * this is likely a type parameter mismatch from specialized class
       * where T was specialized to 'string' but method params still show
       * the default type (int). Use string handling instead. */
      if ((dtype == IVL_VT_BOOL || dtype == IVL_VT_LOGIC) &&
          etype == IVL_VT_STRING) {
	    draw_eval_string(expr);
	    return;
      }

      /* Special case: if port expects class but expression is scalar,
       * this is likely a type parameter mismatch from specialized class
       * (method inherited from base class with default type param).
       * Use scalar handling instead of object handling. */
      if (dtype == IVL_VT_CLASS &&
          (etype == IVL_VT_BOOL || etype == IVL_VT_LOGIC)) {
	    function_argument_logic(port, expr);
	    return;
      }

      switch (dtype) {
	  case IVL_VT_BOOL:
	      /* For now, treat bit2 variables as bit4 variables. */
	  case IVL_VT_LOGIC:
	    function_argument_logic(port, expr);
	    break;
	  case IVL_VT_REAL:
	    function_argument_real(port, expr);
	    break;
	  case IVL_VT_CLASS:
	    vvp_errors += draw_eval_object(expr);
	    break;
	  case IVL_VT_STRING:
	    draw_eval_string(expr);
	    break;
	  case IVL_VT_DARRAY:
	    vvp_errors += draw_eval_object(expr);
	    break;
	  default:
	    fprintf(stderr, "XXXX function argument %s type=%d?!\n",
		    ivl_signal_basename(port), dtype);
	    assert(0);
      }
}

static void draw_send_function_argument(ivl_signal_t port, ivl_expr_t expr)
{
      ivl_variable_type_t dtype = ivl_signal_data_type(port);
      ivl_variable_type_t etype = expr ? ivl_expr_value(expr) : IVL_VT_NO_TYPE;

      /* Array ports are handled directly by function_argument_array which
       * does element-by-element copy. Skip them here. */
      if (ivl_signal_dimensions(port) > 0)
	    return;

      /* Special case: if port expects scalar but expression is class,
       * this is likely a type parameter mismatch from specialized class
       * (method inherited from base class with default type param).
       * Use object store instead of vec4 store. */
      if ((dtype == IVL_VT_BOOL || dtype == IVL_VT_LOGIC) &&
          etype == IVL_VT_CLASS) {
	    fprintf(vvp_out, "    %%store/obj v%p_0;\n", port);
	    return;
      }

      /* Special case: if port expects scalar but expression is string,
       * this is likely a type parameter mismatch from specialized class
       * where T was specialized to 'string' but method params still show
       * the default type (int). Use string store instead of vec4 store. */
      if ((dtype == IVL_VT_BOOL || dtype == IVL_VT_LOGIC) &&
          etype == IVL_VT_STRING) {
	    fprintf(vvp_out, "    %%store/str v%p_0;\n", port);
	    return;
      }

      /* Special case: if port expects class but expression is scalar,
       * this is likely a type parameter mismatch from specialized class
       * (method inherited from base class with default type param).
       * Use vec4 store instead of object store. */
      if (dtype == IVL_VT_CLASS &&
          (etype == IVL_VT_BOOL || etype == IVL_VT_LOGIC)) {
	    fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n",
				      port, ivl_signal_width(port));
	    return;
      }

      switch (dtype) {
	  case IVL_VT_BOOL:
	      /* For now, treat bit2 variables as bit4 variables. */
	  case IVL_VT_LOGIC:
	    fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n",
				      port, ivl_signal_width(port));
	    break;
	  case IVL_VT_REAL:
	    fprintf(vvp_out, "    %%store/real v%p_0;\n", port);
	    break;
	  case IVL_VT_CLASS:
	    fprintf(vvp_out, "    %%store/obj v%p_0;\n", port);
	    break;
	  case IVL_VT_STRING:
	    fprintf(vvp_out, "    %%store/str v%p_0;\n", port);
	    break;
	  case IVL_VT_DARRAY:
	    fprintf(vvp_out, "    %%store/obj v%p_0;\n", port);
	    break;
	  default:
	    fprintf(stderr, "XXXX function argument %s type=%d?!\n",
		    ivl_signal_basename(port), dtype);
	    assert(0);
      }
}

static void draw_ufunc_preamble(ivl_expr_t expr)
{
      ivl_scope_t def = ivl_expr_def(expr);
      unsigned idx;

        /* If this is an automatic function, allocate the local storage. */
      if (ivl_scope_is_auto(def)) {
            fprintf(vvp_out, "    %%alloc S_%p;\n", def);
      }

	/* Evaluate the expressions and send the results to the
	   function ports. Do this in two passes - evaluate,
	   then send - this avoids the function input variables
	   being overwritten if the same (non-automatic) function
	   is called in one of the expressions. */

      assert(ivl_expr_parms(expr) == (ivl_scope_ports(def)-1));
      for (idx = 0 ;  idx < ivl_expr_parms(expr) ;  idx += 1) {
	    ivl_signal_t port = ivl_scope_port(def, idx+1);
	    draw_eval_function_argument(port, ivl_expr_parm(expr, idx));
      }
      for (idx = ivl_expr_parms(expr) ;  idx > 0 ;  idx -= 1) {
	    ivl_signal_t port = ivl_scope_port(def, idx);
	    ivl_expr_t parm_expr = ivl_expr_parm(expr, idx-1);
	    draw_send_function_argument(port, parm_expr);
      }

	/* Call the function. Use virtual dispatch if method is virtual. */
      int is_virtual = ivl_expr_ufunc_is_virtual(expr);
      switch (ivl_expr_value(expr)) {
	  case IVL_VT_VOID:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%callf/virt/void TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%callf/void TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    break;
	  case IVL_VT_REAL:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%callf/virt/real TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%callf/real TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    break;
	  case IVL_VT_BOOL:
	  case IVL_VT_LOGIC:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%callf/virt/vec4 TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%callf/vec4 TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    break;
	  case IVL_VT_STRING:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%callf/virt/str TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%callf/str TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    break;
	  case IVL_VT_CLASS:
	  case IVL_VT_DARRAY:
	  case IVL_VT_QUEUE:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%callf/virt/obj TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%callf/obj TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    break;
	  default:
	    if (is_virtual) {
		fprintf(vvp_out, "    %%fork/virt TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    } else {
		fprintf(vvp_out, "    %%fork TD_%s", vvp_mangle_id(ivl_scope_name(def)));
	    }
	    fprintf(vvp_out, ", S_%p;\n", def);
	    fprintf(vvp_out, "    %%join;\n");
	    break;
      }
}

/*
 * Copy output/inout arguments back to the caller's variables.
 * This must be done after the function call but before freeing
 * the function's local storage.
 */
static void draw_ufunc_output_args(ivl_expr_t expr)
{
      ivl_scope_t def = ivl_expr_def(expr);
      unsigned idx;

      for (idx = 0; idx < ivl_expr_parms(expr); idx += 1) {
	    ivl_signal_t port = ivl_scope_port(def, idx+1);
	    ivl_signal_port_t port_dir = ivl_signal_port(port);

	    /* Only process output and inout ports */
	    if (port_dir != IVL_SIP_OUTPUT && port_dir != IVL_SIP_INOUT)
		  continue;

	    ivl_expr_t parm_expr = ivl_expr_parm(expr, idx);
	    if (!parm_expr)
		  continue;

	    /* The expression must be a signal reference for output args */
	    if (ivl_expr_type(parm_expr) != IVL_EX_SIGNAL)
		  continue;

	    ivl_signal_t caller_sig = ivl_expr_signal(parm_expr);
	    if (!caller_sig)
		  continue;

	    /* Load from function port and store to caller's variable */
	    ivl_variable_type_t dtype = ivl_signal_data_type(port);
	    switch (dtype) {
		case IVL_VT_BOOL:
		case IVL_VT_LOGIC:
		    fprintf(vvp_out, "    %%load/vec4 v%p_0;\n", port);
		    fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n",
					caller_sig, ivl_signal_width(caller_sig));
		    break;
		case IVL_VT_REAL:
		    fprintf(vvp_out, "    %%load/real v%p_0;\n", port);
		    fprintf(vvp_out, "    %%store/real v%p_0;\n", caller_sig);
		    break;
		case IVL_VT_STRING:
		    fprintf(vvp_out, "    %%load/str v%p_0;\n", port);
		    fprintf(vvp_out, "    %%store/str v%p_0;\n", caller_sig);
		    break;
		case IVL_VT_CLASS:
		case IVL_VT_DARRAY:
		    fprintf(vvp_out, "    %%load/obj v%p_0;\n", port);
		    fprintf(vvp_out, "    %%store/obj v%p_0;\n", caller_sig);
		    break;
		default:
		    /* Other types not yet supported */
		    break;
	    }
      }
}

static void draw_ufunc_epilogue(ivl_expr_t expr)
{
      ivl_scope_t def = ivl_expr_def(expr);

        /* Copy output/inout arguments back to caller before freeing */
      draw_ufunc_output_args(expr);

        /* If this is an automatic function, free the local storage. */
      if (ivl_scope_is_auto(def)) {
            fprintf(vvp_out, "    %%free S_%p;\n", def);
      }
}

/*
 * A call to a user defined function generates a result that is the
 * result of this expression.
 *
 * The result of the function is placed by the function execution into
 * a signal within the scope of the function that also has a basename
 * the same as the function. The ivl_target API handled the result
 * mapping already, and we get the name of the result signal as
 * parameter 0 of the function definition.
 */

void draw_ufunc_vec4(ivl_expr_t expr)
{

	/* Take in arguments to function and call function code. */
      draw_ufunc_preamble(expr);

	/* If the function returns a string but we're in a vec4 context,
	   convert the string result to vec4. This happens when a string
	   function is used in a concatenation. Use a large width since
	   we don't know the string length at compile time. The actual
	   conversion will use the string's actual length. */
      if (ivl_expr_value(expr) == IVL_VT_STRING) {
	    unsigned wid = ivl_expr_width(expr);
	    /* String expressions often have 0 or invalid width. Use a
	       reasonable default that handles typical strings. 2048 bits
	       allows strings up to 256 characters. */
	    if (wid == 0 || wid > 0x80000000) wid = 2048;
	    fprintf(vvp_out, "    %%cast/vec4/str %u; Convert string to vec4\n", wid);
      }

      draw_ufunc_epilogue(expr);
}

void draw_ufunc_real(ivl_expr_t expr)
{

	/* Take in arguments to function and call the function code. */
      draw_ufunc_preamble(expr);

	/* The %callf/real function emitted by the preamble leaves
	   the result in the stack for us. */

      draw_ufunc_epilogue(expr);
}

void draw_ufunc_string(ivl_expr_t expr)
{

	/* Take in arguments to function and call the function code. */
      draw_ufunc_preamble(expr);

	/* The %callf/str function emitted by the preamble leaves
	   the result in the stack for us. */

      draw_ufunc_epilogue(expr);
}

void draw_ufunc_object(ivl_expr_t expr)
{
      ivl_scope_t def = ivl_expr_def(expr);
      ivl_signal_t retval = ivl_scope_port(def, 0);

	/* Take in arguments to function and call the function code. */
      draw_ufunc_preamble(expr);

	/* Load the result into the object stack. */
      fprintf(vvp_out, "    %%load/obj v%p_0;\n", retval);

      draw_ufunc_epilogue(expr);
}
