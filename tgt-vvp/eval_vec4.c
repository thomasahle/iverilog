/*
 * Copyright (c) 2013-2020 Stephen Williams (steve@icarus.com)
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

/*
 * This file includes functions for evaluating VECTOR expressions.
 */
# include  "vvp_priv.h"
# include  <string.h>
# include  <stdlib.h>
# include  <math.h>
# include  <assert.h>
# include  <stdbool.h>

void resize_vec4_wid(ivl_expr_t expr, unsigned wid)
{
      if (ivl_expr_width(expr) == wid)
	    return;

      if (ivl_expr_signed(expr))
	    fprintf(vvp_out, "    %%pad/s %u;\n", wid);
      else
	    fprintf(vvp_out, "    %%pad/u %u;\n", wid);
}

/*
 * Test if the draw_immediate_vec4 instruction can be used.
 */
int test_immediate_vec4_ok(ivl_expr_t re)
{
      const char*bits;
      unsigned idx;

      if (ivl_expr_type(re) != IVL_EX_NUMBER)
	    return 0;

      if (ivl_expr_width(re) <= 32)
	    return 1;

      bits = ivl_expr_bits(re);

      for (idx = 32 ; idx < ivl_expr_width(re) ; idx += 1) {
	    if (bits[idx] != '0')
		  return 0;
      }

      return 1;
}

static void make_immediate_vec4_words(ivl_expr_t re, unsigned long*val0p, unsigned long*valxp, unsigned*widp)
{
      unsigned long val0 = 0;
      unsigned long valx = 0;
      unsigned wid = ivl_expr_width(re);
      const char*bits = ivl_expr_bits(re);

      unsigned idx;

      for (idx = 0 ; idx < wid ; idx += 1) {
	    assert( ((val0|valx)&0x80000000UL) == 0UL );
	    val0 <<= 1;
	    valx <<= 1;
	    switch (bits[wid-idx-1]) {
		case '0':
		  break;
		case '1':
		  val0 |= 1;
		  break;
		case 'x':
		  val0 |= 1;
		  valx |= 1;
		  break;
		case 'z':
		  val0 |= 0;
		  valx |= 1;
		  break;
		default:
		  assert(0);
		  break;
	    }
      }

      *val0p = val0;
      *valxp = valx;
      *widp = wid;
}

void draw_immediate_vec4(ivl_expr_t re, const char*opcode)
{
      unsigned long val0, valx;
      unsigned wid;
      make_immediate_vec4_words(re, &val0, &valx, &wid);
      fprintf(vvp_out, "    %s %lu, %lu, %u;\n", opcode, val0, valx, wid);
}

static void draw_binary_vec4_arith(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      unsigned lwid = ivl_expr_width(le);
      unsigned rwid = ivl_expr_width(re);
      unsigned ewid = ivl_expr_width(expr);

      int is_power_op = ivl_expr_opcode(expr) == 'p' ? 1 : 0;

	/* The power operation differs from the other arithmetic operations
	   in that we only use the signed version of the operation if the
	   right hand operand (the exponent) is signed. */
      int signed_flag = (ivl_expr_signed(le) || is_power_op) && ivl_expr_signed(re) ? 1 : 0;
      const char*signed_string = signed_flag? "/s" : "";

	/* All the arithmetic operations handled here (except for the power
	   operation) require that the operands (and the result) be the same
	   width. We further assume that the core has not given us an operand
	   wider then the expression width. So pad operands as needed. */
      draw_eval_vec4(le);
      if (lwid != ewid) {
	    fprintf(vvp_out, "    %%pad/%c %u;\n", ivl_expr_signed(le)? 's' : 'u', ewid);
      }

	/* Special case: If the re expression can be collected into an
	   immediate operand, and the instruction supports it, then
	   generate an immediate instruction instead of the generic
	   version. */
      if (rwid==ewid && test_immediate_vec4_ok(re)) {
	    switch (ivl_expr_opcode(expr)) {
		case '+':
		  draw_immediate_vec4(re, "%addi");
		  return;
		case '-':
		  draw_immediate_vec4(re, "%subi");
		  return;
		case '*':
		  draw_immediate_vec4(re, "%muli");
		  return;
		default:
		  break;
	    }
      }

      draw_eval_vec4(re);
      if ((rwid != ewid) && !is_power_op) {
	    fprintf(vvp_out, "    %%pad/%c %u;\n", ivl_expr_signed(re)? 's' : 'u', ewid);
      }

      switch (ivl_expr_opcode(expr)) {
	  case '+':
	    fprintf(vvp_out, "    %%add;\n");
	    break;
	  case '-':
	    fprintf(vvp_out, "    %%sub;\n");
	    break;
	  case '*':
	    fprintf(vvp_out, "    %%mul;\n");
	    break;
	  case '/':
	    fprintf(vvp_out, "    %%div%s;\n", signed_string);
	    break;
	  case '%':
	    fprintf(vvp_out, "    %%mod%s;\n", signed_string);
	    break;
	  case 'p':
	    fprintf(vvp_out, "    %%pow%s;\n", signed_string);
	    break;

	  default:
	    assert(0);
	    break;
      }
}

static void draw_binary_vec4_bitwise(ivl_expr_t expr)
{
      draw_eval_vec4(ivl_expr_oper1(expr));
      draw_eval_vec4(ivl_expr_oper2(expr));

      switch (ivl_expr_opcode(expr)) {
	  case '&':
	    fprintf(vvp_out, "    %%and;\n");
	    break;
	  case '|':
	    fprintf(vvp_out, "    %%or;\n");
	    break;
	  case '^':
	    fprintf(vvp_out, "    %%xor;\n");
	    break;
	  case 'A': /* ~& */
	    fprintf(vvp_out, "    %%nand;\n");
	    break;
	  case 'O': /* ~| */
	    fprintf(vvp_out, "    %%nor;\n");
	    break;
	  case 'X': /* ~^ */
	    fprintf(vvp_out, "    %%xnor;\n");
	    break;
	  default:
	    assert(0);
	    break;
      }
}

static void draw_binary_vec4_compare_real(ivl_expr_t expr)
{
      draw_eval_real(ivl_expr_oper1(expr));
      draw_eval_real(ivl_expr_oper2(expr));

      switch (ivl_expr_opcode(expr)) {
	  case 'e': /* == */
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  case 'n': /* != */
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_inv 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  default:
	    assert(0);
      }
}

static void draw_binary_vec4_compare_string(ivl_expr_t expr)
{
      draw_eval_string(ivl_expr_oper1(expr));
      draw_eval_string(ivl_expr_oper2(expr));

      switch (ivl_expr_opcode(expr)) {
	  case 'e': /* == */
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  case 'n': /* != */
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_inv 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  default:
	    assert(0);
      }
}

static void draw_binary_vec4_compare_class(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      if (ivl_expr_type(le) == IVL_EX_NULL) {
	    ivl_expr_t tmp = le;
	    le = re;
	    re = tmp;
      }

	/* Special case: If both operands are null, then the
	   expression has a constant value. */
      if (ivl_expr_type(le)==IVL_EX_NULL && ivl_expr_type(re)==IVL_EX_NULL) {
	    switch (ivl_expr_opcode(expr)) {
		case 'e': /* == */
		  fprintf(vvp_out, "    %%pushi/vec4 1, 0, 1;\n");
		  break;
		case 'n': /* != */
		  fprintf(vvp_out, "    %%pushi/vec4 0, 0, 1;\n");
		  break;
		default:
		  assert(0);
		  break;
	    }
	    return;
      }

	/* A signal/variable is compared to null. Implement this with
	   the %test_nul statement, which peeks at the variable
	   contents directly. */
      if (ivl_expr_type(re)==IVL_EX_NULL && ivl_expr_type(le)==IVL_EX_SIGNAL) {
	    ivl_signal_t sig= ivl_expr_signal(le);

	    if (ivl_signal_dimensions(sig) == 0) {
		  fprintf(vvp_out, "    %%test_nul v%p_0;\n", sig);
	    } else {
		  ivl_expr_t word_ex = ivl_expr_oper1(le);
		  int word_ix = allocate_word();
		  draw_eval_expr_into_integer(word_ex, word_ix);
		  fprintf(vvp_out, "    %%test_nul/a v%p, %d;\n", sig, word_ix);
		  clr_word(word_ix);
	    }
	    if (ivl_expr_opcode(expr) == 'n')
		  fprintf(vvp_out, "    %%flag_inv 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    return;
      }

      if (ivl_expr_type(re)==IVL_EX_NULL && ivl_expr_type(le)==IVL_EX_PROPERTY) {
	    ivl_signal_t sig = ivl_expr_signal(le);
	    ivl_expr_t base = ivl_expr_property_base(le);
	    unsigned pidx = ivl_expr_property_idx(le);
	    ivl_expr_t idx_expr = ivl_expr_oper1(le);
	    ivl_expr_t arr_idx = ivl_expr_property_array_idx(le);
	    int idx = 0;

	      /* If the property has an array index (for property arrays),
		 then evaluate it into an index register. */
	    if ( idx_expr ) {
		  idx = allocate_word();
		  draw_eval_expr_into_integer(idx_expr, idx);
	    }

	    if (base) {
		  /* Nested property access - evaluate base expression first */
		  draw_eval_object(base);
	    } else {
		  /* Direct property access - load signal */
		  fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
	    }

	    if (arr_idx) {
		  /* Darray element null test: property[arr_idx] == null
		     Load the darray property (using 0 as prop array index since
		     a darray property is scalar), then test element at arr_idx */
		  fprintf(vvp_out, "    %%prop/obj %u, 0; Load darray property\n", pidx);
		  fprintf(vvp_out, "    %%pop/obj 1, 1;\n");
		  int arr_reg = allocate_word();
		  draw_eval_expr_into_integer(arr_idx, arr_reg);
		  fprintf(vvp_out, "    %%test_nul/dar %d;\n", arr_reg);
		  fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
		  clr_word(arr_reg);
	    } else {
		  fprintf(vvp_out, "    %%test_nul/prop %u, %d;\n", pidx, idx);
		  fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
	    }
	    if (ivl_expr_opcode(expr) == 'n')
		  fprintf(vvp_out, "    %%flag_inv 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");

	    if (idx != 0) clr_word(idx);
	    return;
      }

	/* Compare virtual interface property (class member through vif) to null. */
      if (ivl_expr_type(re)==IVL_EX_NULL && ivl_expr_type(le)==IVL_EX_VIFPROP) {
	    ivl_expr_t vif_expr = ivl_expr_vifprop_base(le);
	    const char* member_name = ivl_expr_vifprop_member(le);

	    /* Evaluate the vif expression to get scope on object stack */
	    draw_eval_object(vif_expr);

	    /* Load the object from the vif member */
	    fprintf(vvp_out, "    %%vif/load/obj \"%s\";\n", member_name);

	    /* Test if the loaded object is null */
	    fprintf(vvp_out, "    %%test_nul/obj;\n");

	    /* Pop both the loaded object and the vif scope */
	    fprintf(vvp_out, "    %%pop/obj 2, 0;\n");

	    if (ivl_expr_opcode(expr) == 'n')
		  fprintf(vvp_out, "    %%flag_inv 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    return;
      }

      fprintf(stderr, "SORRY: Compare class handles not implemented\n");
      fprintf(vvp_out, " ; XXXX compare class handles. re-type=%d, le-type=%d\n",
	      ivl_expr_type(re), ivl_expr_type(le));
      vvp_errors += 1;
}

static void draw_binary_vec4_compare(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      if ((ivl_expr_value(le) == IVL_VT_REAL)
	  || (ivl_expr_value(re) == IVL_VT_REAL)) {
	    draw_binary_vec4_compare_real(expr);
	    return;
      }

      if ((ivl_expr_value(le)==IVL_VT_STRING)
	  && (ivl_expr_value(re)==IVL_VT_STRING)) {
	    draw_binary_vec4_compare_string(expr);
	    return;
      }

      if ((ivl_expr_value(le)==IVL_VT_STRING)
	  && (ivl_expr_type(re)==IVL_EX_STRING)) {
	    draw_binary_vec4_compare_string(expr);
	    return;
      }

      if ((ivl_expr_type(le)==IVL_EX_STRING)
	  && (ivl_expr_value(re)==IVL_VT_STRING)) {
	    draw_binary_vec4_compare_string(expr);
	    return;
      }

      if ((ivl_expr_value(le)==IVL_VT_CLASS)
	  && (ivl_expr_value(re)==IVL_VT_CLASS)) {
	    draw_binary_vec4_compare_class(expr);
	    return;
      }

      unsigned use_wid = ivl_expr_width(le);
      if (ivl_expr_width(re) > use_wid)
	    use_wid = ivl_expr_width(re);

      draw_eval_vec4(le);
      resize_vec4_wid(le, use_wid);

      draw_eval_vec4(re);
      resize_vec4_wid(re, use_wid);

      switch (ivl_expr_opcode(expr)) {
	  case 'e': /* == */
	    fprintf(vvp_out, "    %%cmp/e;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  case 'n': /* != */
	    fprintf(vvp_out, "    %%cmp/ne;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  case 'E': /* === */
	    fprintf(vvp_out, "    %%cmp/e;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 6;\n");
	    break;
	  case 'N': /* !== */
	    fprintf(vvp_out, "    %%cmp/ne;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 6;\n");
	    break;
	  case 'w': /* ==? */
	    fprintf(vvp_out, "    %%cmp/we;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  case 'W': /* !=? */
	    fprintf(vvp_out, "    %%cmp/wne;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    break;
	  default:
	    assert(0);
      }
}

/*
 * Handle the logical implication:
 *    <le> -> <re>
 * which is the same as the expression
 *    !<le> || <re>
 *
 */
static void draw_binary_vec4_limpl(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      /* The arguments should have alreacy been reduced. */
      assert(ivl_expr_width(le) == 1);
      assert(ivl_expr_width(re) == 1);

      draw_eval_vec4(le);
      fprintf(vvp_out, "    %%inv;\n");
      draw_eval_vec4(re);
      fprintf(vvp_out, "    %%or;\n");
}

static void draw_binary_vec4_lequiv(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

	/* The arguments should have already been reduced. */
      assert(ivl_expr_width(le) == 1);
      draw_eval_vec4(le);
      assert(ivl_expr_width(re) == 1);
      draw_eval_vec4(re);

      fprintf(vvp_out, "    %%xnor;\n");

      assert(ivl_expr_width(expr) == 1);
}

static void draw_binary_vec4_logical(ivl_expr_t expr, char op)
{
      const char *opcode;
      const char *jmp_type;

      switch (op) {
	  case 'a':
	    opcode = "and";
	    jmp_type = "0";
	    break;
	  case 'o':
	    opcode = "or";
	    jmp_type = "1";
	    break;
	  default:
	    assert(0);
	    break;
      }

      unsigned label_out = local_count++;

      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      /* Evaluate the left expression as a conditon and skip the right expression
       * if the left is false. */
      int flag = draw_eval_condition(le);
      fprintf(vvp_out, "    %%flag_get/vec4 %d;\n", flag);
      fprintf(vvp_out, "    %%jmp/%s T_%u.%u, %d;\n", jmp_type, thread_count,
	      label_out, flag);
      clr_flag(flag);
      /* Now push the right expression. Reduce to a single bit if necessary. */
      draw_eval_vec4(re);
      if (ivl_expr_width(re) > 1)
	    fprintf(vvp_out, "    %%or/r;\n");

      fprintf(vvp_out, "    %%%s;\n", opcode);

      fprintf(vvp_out, "T_%u.%u;\n", thread_count, label_out);
      if (ivl_expr_width(expr) > 1)
	    fprintf(vvp_out, "    %%pad/u %u;\n", ivl_expr_width(expr));
}

static void draw_binary_vec4_le_real(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      switch (ivl_expr_opcode(expr)) {
	  case '<':
	    draw_eval_real(le);
	    draw_eval_real(re);
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    break;

	  case 'L': /* <= */
	    draw_eval_real(le);
	    draw_eval_real(re);
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    fprintf(vvp_out, "    %%or;\n");
	    break;

	  case '>':
	    draw_eval_real(re);
	    draw_eval_real(le);
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    break;

	  case 'G': /* >= */
	    draw_eval_real(re);
	    draw_eval_real(le);
	    fprintf(vvp_out, "    %%cmp/wr;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    fprintf(vvp_out, "    %%or;\n");
	    break;

	  default:
	    assert(0);
	    break;
      }
}

static void draw_binary_vec4_le_string(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

      switch (ivl_expr_opcode(expr)) {
	  case '<':
	    draw_eval_string(le);
	    draw_eval_string(re);
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    break;

	  case 'L': /* <= */
	    draw_eval_string(le);
	    draw_eval_string(re);
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    fprintf(vvp_out, "    %%or;\n");
	    break;

	  case '>':
	    draw_eval_string(re);
	    draw_eval_string(le);
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    break;

	  case 'G': /* >= */
	    draw_eval_string(re);
	    draw_eval_string(le);
	    fprintf(vvp_out, "    %%cmp/str;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    fprintf(vvp_out, "    %%or;\n");
	    break;

	  default:
	    assert(0);
	    break;
      }
}

static void draw_binary_vec4_le(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);
      ivl_expr_t tmp;

      if ((ivl_expr_value(le) == IVL_VT_REAL)
	  || (ivl_expr_value(re) == IVL_VT_REAL)) {
	    draw_binary_vec4_le_real(expr);
	    return;
      }

      char use_opcode = ivl_expr_opcode(expr);
      char s_flag = (ivl_expr_signed(le) && ivl_expr_signed(re)) ? 's' : 'u';

	/* If this is a > or >=, then convert it to < or <= by
	   swapping the operands. Adjust the opcode to match. */
      switch (use_opcode) {
	  case 'G':
	    tmp = le;
	    le = re;
	    re = tmp;
	    use_opcode = 'L';
	    break;
	  case '>':
	    tmp = le;
	    le = re;
	    re = tmp;
	    use_opcode = '<';
	    break;
      }

      if ((ivl_expr_value(le)==IVL_VT_STRING)
	  && (ivl_expr_value(re)==IVL_VT_STRING)) {
	    draw_binary_vec4_le_string(expr);
	    return;
      }

      if ((ivl_expr_value(le)==IVL_VT_STRING)
	  && (ivl_expr_type(re)==IVL_EX_STRING)) {
	    draw_binary_vec4_le_string(expr);
	    return;
      }

      if ((ivl_expr_type(le)==IVL_EX_STRING)
	  && (ivl_expr_value(re)==IVL_VT_STRING)) {
	    draw_binary_vec4_le_string(expr);
	    return;
      }

	/* NOTE: I think I would rather the elaborator handle the
	   operand widths. When that happens, take this code out. */

      unsigned use_wid = ivl_expr_width(le);
      if (ivl_expr_width(re) > use_wid)
	    use_wid = ivl_expr_width(re);

      draw_eval_vec4(le);
      resize_vec4_wid(le, use_wid);

      if (ivl_expr_width(re)==use_wid && test_immediate_vec4_ok(re)) {
	      /* Special case: If the right operand can be handled as
		 an immediate operand, then use that instead. */
	    char opcode[8];
	    snprintf(opcode, sizeof opcode, "%%cmpi/%c", s_flag);
	    draw_immediate_vec4(re, opcode);

      } else {
	    draw_eval_vec4(re);
	    resize_vec4_wid(re, use_wid);

	    fprintf(vvp_out, "    %%cmp/%c;\n", s_flag);
      }

      switch (use_opcode) {
	  case 'L':
	    fprintf(vvp_out, "    %%flag_get/vec4 4;\n");
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    fprintf(vvp_out, "    %%or;\n");
	    break;
	  case '<':
	    fprintf(vvp_out, "    %%flag_get/vec4 5;\n");
	    break;
	  default:
	    assert(0);
	    break;
      }
}

static void draw_binary_vec4_lrs(ivl_expr_t expr)
{
      ivl_expr_t le = ivl_expr_oper1(expr);
      ivl_expr_t re = ivl_expr_oper2(expr);

	// Push the left expression onto the stack.
      draw_eval_vec4(le);

	// Calculate the shift amount into an index register.
      int use_index_reg = allocate_word();
      assert(use_index_reg >= 0);
      draw_eval_expr_into_integer(re, use_index_reg);

	// Emit the actual shift instruction. This will pop the top of
	// the stack and replace it with the result of the shift.
      switch (ivl_expr_opcode(expr)) {
	  case 'l': /* << */
	    fprintf(vvp_out, "    %%shiftl %d;\n", use_index_reg);
	    break;
	  case 'r': /* >> */
	    fprintf(vvp_out, "    %%shiftr %d;\n", use_index_reg);
	    break;
	  case 'R': /* >>> */
	    if (ivl_expr_signed(le))
		  fprintf(vvp_out, "    %%shiftr/s %d;\n", use_index_reg);
	    else
		  fprintf(vvp_out, "    %%shiftr %d;\n", use_index_reg);
	    break;
	  default:
	    assert(0);
	    break;
      }

      clr_word(use_index_reg);
}

static void draw_binary_vec4(ivl_expr_t expr)
{
      switch (ivl_expr_opcode(expr)) {
	  case 'a': /* Logical && */
	  case 'o': /* || (logical or) */
	    draw_binary_vec4_logical(expr, ivl_expr_opcode(expr));
	    break;

	  case '+':
	  case '-':
	  case '*':
	  case '/':
	  case '%':
	  case 'p': /* ** (power) */
	    draw_binary_vec4_arith(expr);
	    break;

	  case '&':
	  case '|':
	  case '^':
	  case 'A': /* NAND (~&) */
	  case 'O': /* NOR  (~|) */
	  case 'X': /* exclusive nor (~^) */
	    draw_binary_vec4_bitwise(expr);
	    break;

	  case 'e': /* == */
	  case 'E': /* === */
	  case 'n': /* != */
	  case 'N': /* !== */
	  case 'w': /* ==? */
	  case 'W': /* !=? */
	    draw_binary_vec4_compare(expr);
	    break;

	  case 'G': /* >= */
	  case 'L': /* <= */
	  case '>':
	  case '<':
	    draw_binary_vec4_le(expr);
	    break;

	  case 'l': /* << */
	  case 'r': /* >> */
	  case 'R': /* >>> */
	    draw_binary_vec4_lrs(expr);
	    break;

	  case 'q': /* -> (logical implication) */
	    draw_binary_vec4_limpl(expr);
	    break;

	  case 'Q': /* <-> (logical equivalence) */
	    draw_binary_vec4_lequiv(expr);
	    break;

	  default:
	    fprintf(stderr, "vvp.tgt error: unsupported binary (%c)\n",
		    ivl_expr_opcode(expr));
	    assert(0);
      }
}

/*
 * This handles two special cases:
 *   1) Making a large IVL_EX_NUMBER as an immediate value. In this
 *   case, start with a %pushi/vec4 to get the stack started, then
 *   continue with %concati/vec4 instructions to build that number
 *   up.
 *
 *   2) Concatenating a large IVL_EX_NUMBER to the current top of the
 *   stack. In this case, start with %concati/vec4 and continue
 *   generating %concati/vec4 instructions to finish up the large number.
 */
static void draw_concat_number_vec4(ivl_expr_t expr, int as_concati)
{
      unsigned long val0 = 0;
      unsigned long valx = 0;
      unsigned wid = ivl_expr_width(expr);
      const char*bits = ivl_expr_bits(expr);

      unsigned idx;
      int accum = 0;
      int count_pushi = as_concati? 1 : 0;

	/* Scan the literal bits, MSB first. */
      for (idx = 0 ; idx < wid ; idx += 1) {
	    val0 <<= 1;
	    valx <<= 1;
	    switch (bits[wid-idx-1]) {
		case '0':
		  break;
		case '1':
		  val0 |= 1;
		  break;
		case 'x':
		  val0 |= 1;
		  valx |= 1;
		  break;
		case 'z':
		  val0 |= 0;
		  valx |= 1;
		  break;
		default:
		  assert(0);
		  break;
	    }
	    accum += 1;

	      /* Collect as many bits as can be written by a single
		 %pushi/vec4 instruction. This may be more than 32 if
		 the higher bits are zero, but if the currently
		 accumulated value fills what a %pushi/vec4 can do,
		 then write it out, generate a %concat/vec4, and set
		 up to handle more bits. */
	    if ( (val0|valx) & 0x80000000UL ) {
		  if (count_pushi) {
			fprintf(vvp_out, "    %%concati/vec4 %lu, %lu, %d;\n",
				val0, valx, accum);

		  } else {
			fprintf(vvp_out, "    %%pushi/vec4 %lu, %lu, %d;\n",
				val0, valx, accum);
		  }

		  accum = 0;
		  val0 = 0;
		  valx = 0;

		  count_pushi += 1;
	    }
      }

      if (accum) {
	    if (count_pushi) {
		  fprintf(vvp_out, "    %%concati/vec4 %lu, %lu, %d;\n",
			  val0, valx, accum);
	    } else {
		  fprintf(vvp_out, "    %%pushi/vec4 %lu, %lu, %d;\n",
			  val0, valx, accum);
	    }
      }
}

static void draw_concat_vec4(ivl_expr_t expr)
{
	/* Repeat the concatenation this many times to make a
	   super-concatenation. */
      unsigned repeat = ivl_expr_repeat(expr);
	/* This is the number of expressions that go into the
	   concatenation. */
      unsigned num_sube = ivl_expr_parms(expr);
      unsigned sub_idx = 0;
      ivl_expr_t sube;

      assert(num_sube > 0);

	/* Start with the most-significant bits. */
      sube = ivl_expr_parm(expr, sub_idx);
      draw_eval_vec4(sube);
	/* Evaluate, but skip any zero replication expressions at the
	 * head of this concatenation. */
      while ((ivl_expr_type(sube) == IVL_EX_CONCAT) &&
             (ivl_expr_repeat(sube) == 0)) {
	    fprintf(vvp_out, "    %%pop/vec4 1; skip zero replication\n");
	    sub_idx += 1;
	    sube = ivl_expr_parm(expr, sub_idx);
	    draw_eval_vec4(sube);
      }

      for ( sub_idx += 1 ; sub_idx < num_sube ; sub_idx += 1) {
	      /* Concatenate progressively lower parts. */
	    sube = ivl_expr_parm(expr, sub_idx);

	      /* Special case: The next expression is a NUMBER that
		 can be concatenated using %concati/vec4
		 instructions. */
	    if (ivl_expr_type(sube) == IVL_EX_NUMBER) {
		  draw_concat_number_vec4(sube, 1);
		  continue;
	    }

	    draw_eval_vec4(sube);
	      /* Evaluate, but skip any zero replication expressions in the
	       * rest of this concatenation. */
	    if ((ivl_expr_type(sube) == IVL_EX_CONCAT) &&
	        (ivl_expr_repeat(sube) == 0)) {
		  fprintf(vvp_out, "    %%pop/vec4 1; skip zero replication\n");
		  continue;
	    }
	    fprintf(vvp_out, "    %%concat/vec4; draw_concat_vec4\n");
      }

      if (repeat > 1) {
	    fprintf(vvp_out, "    %%replicate %u;\n", repeat);
      }
}

/*
 * Push a number into the vec4 stack using %pushi/vec4
 * instructions. The %pushi/vec4 instruction can only handle up to 32
 * non-zero bits, so if there are more than that, then generate
 * multiple %pushi/vec4 statements, and use %concat/vec4 statements to
 * concatenate the vectors into the desired result.
 */
static void draw_number_vec4(ivl_expr_t expr)
{
      draw_concat_number_vec4(expr, 0);
}

static void draw_property_vec4(ivl_expr_t expr)
{
      ivl_signal_t sig = ivl_expr_signal(expr);
      ivl_expr_t base = ivl_expr_property_base(expr);
      ivl_expr_t array_idx = ivl_expr_property_array_idx(expr);
      unsigned pidx = ivl_expr_property_idx(expr);

      if (base) {
	    // Nested property access - evaluate base expression first
	    draw_eval_object(base);
      } else {
	    // Direct property access - load signal
	    fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
      }

      if (array_idx) {
	    // Check if property is an associative array or dynamic array
	    // For nested access, get the class type from the base expression's net_type
	    ivl_type_t class_type;
	    if (base) {
		  class_type = ivl_expr_net_type(base);
	    } else {
		  class_type = sig ? ivl_signal_net_type(sig) : NULL;
	    }
	    ivl_type_t prop_type = class_type ? ivl_type_prop_type(class_type, pidx) : NULL;

	    if (prop_type && ivl_type_base(prop_type) == IVL_VT_ASSOC) {
		  // Associative array property - convert index to string and use assoc opcode
		  draw_eval_string(array_idx);
		  fprintf(vvp_out, "    %%prop/assoc/vec4 %u;\n", pidx);
		  fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
	    } else if (prop_type && ivl_type_base(prop_type) == IVL_VT_DARRAY) {
		  // Dynamic array property - load darray, then index into it
		  int idx_word = allocate_word();
		  draw_eval_expr_into_integer(array_idx, idx_word);
		  fprintf(vvp_out, "    %%prop/obj %u, 0; Load darray property\n", pidx);
		  fprintf(vvp_out, "    %%pop/obj 1, 1; Pop class obj, keep darray\n");
		  fprintf(vvp_out, "    %%get/dar/obj/vec4 %d;\n", idx_word);
		  clr_word(idx_word);
	    } else {
		  // Regular array property - use integer index
		  draw_eval_vec4(array_idx);
		  fprintf(vvp_out, "    %%prop/va %u;\n", pidx);
		  fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
	    }
      } else {
	    fprintf(vvp_out, "    %%prop/v %u;\n", pidx);
	    fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
      }
}

/*
 * Virtual interface property access: vif.signal_name
 * This evaluates the virtual interface expression (getting the scope pointer),
 * then loads the vector value from the named signal within that scope.
 */
static void draw_vifprop_vec4(ivl_expr_t expr)
{
      ivl_expr_t vif_expr = ivl_expr_vifprop_base(expr);
      const char* member_name = ivl_expr_vifprop_member(expr);
      ivl_signal_t member_sig = ivl_expr_vifprop_sig(expr);
      unsigned wid = ivl_expr_width(expr);

      /* Evaluate the virtual interface expression to get scope on object stack */
      draw_eval_object(vif_expr);

      /* Load vector from virtual interface member signal */
      fprintf(vvp_out, "    %%vif/load/v \"%s\", %u; // member_sig=v%p_0\n",
              member_name, wid, member_sig);
      fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
}

/*
 * Associative array method call: arr.exists(key), arr.first(key), etc.
 * This generates the appropriate VVP opcode for the method.
 */
static void draw_assoc_method_vec4(ivl_expr_t expr)
{
      ivl_signal_t sig = ivl_expr_assoc_signal(expr);
      ivl_expr_t base_expr = ivl_expr_assoc_base(expr);
      int pidx = ivl_expr_assoc_property_idx(expr);
      ivl_assoc_method_t method = ivl_expr_assoc_method(expr);
      ivl_expr_t key_expr = ivl_expr_assoc_key(expr);

      const char* method_name = "";
      switch (method) {
	  case IVL_ASSOC_EXISTS: method_name = "exists"; break;
	  case IVL_ASSOC_DELETE: method_name = "delete"; break;
	  case IVL_ASSOC_FIRST:  method_name = "first"; break;
	  case IVL_ASSOC_LAST:   method_name = "last"; break;
	  case IVL_ASSOC_NEXT:   method_name = "next"; break;
	  case IVL_ASSOC_PREV:   method_name = "prev"; break;
	  case IVL_ASSOC_NUM:    method_name = "num"; break;
      }

        // num() doesn't need a key argument
      int needs_key = (method != IVL_ASSOC_NUM);

      // first/last/next/prev update the key as a ref parameter
      int updates_key = (method == IVL_ASSOC_FIRST || method == IVL_ASSOC_LAST ||
                         method == IVL_ASSOC_NEXT || method == IVL_ASSOC_PREV);

      // For methods that update key, get the signal to store back to
      ivl_signal_t key_sig = NULL;
      unsigned key_wid = 32;
      if (updates_key && key_expr && ivl_expr_type(key_expr) == IVL_EX_SIGNAL) {
	    key_sig = ivl_expr_signal(key_expr);
	    key_wid = ivl_expr_width(key_expr);
      }

      if (base_expr) {
	    /* Nested property access: base_expr.assoc_prop.method() */
	    /* Evaluate the base expression to get the object */
	    draw_eval_object(base_expr);

	    /* If there's a key expression, evaluate it and convert to string */
	    if (key_expr) {
		  draw_eval_string(key_expr);
	    } else if (needs_key) {
		  /* For first/last/next/prev without argument, push empty string */
		  fprintf(vvp_out, "    %%pushi/str \"\";\n");
	    }

	    /* Emit the property associative array method opcode */
	    fprintf(vvp_out, "    %%prop/assoc/%s %d;\n", method_name, pidx);
	    fprintf(vvp_out, "    %%pop/obj 1, 0;\n");

	    /* For first/last/next/prev, store updated key back to variable */
	    if (key_sig) {
		  fprintf(vvp_out, "    %%cast/vec4/str %u;\n", key_wid);
		  fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n", key_sig, key_wid);
	    }
      } else if (pidx >= 0) {
	    /* Associative array is a direct class property */
	    fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);

	    /* If there's a key expression, evaluate it and convert to string */
	    if (key_expr) {
		  draw_eval_string(key_expr);
	    } else if (needs_key) {
		  /* For first/last/next/prev without argument, push empty string */
		  fprintf(vvp_out, "    %%pushi/str \"\";\n");
	    }

	    /* Emit the property associative array method opcode */
	    fprintf(vvp_out, "    %%prop/assoc/%s %d;\n", method_name, pidx);
	    fprintf(vvp_out, "    %%pop/obj 1, 0;\n");

	    /* For first/last/next/prev, store updated key back to variable */
	    if (key_sig) {
		  fprintf(vvp_out, "    %%cast/vec4/str %u;\n", key_wid);
		  fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n", key_sig, key_wid);
	    }
      } else {
	    /* Standalone associative array variable */
	    /* If there's a key expression, evaluate it and convert to string */
	    if (key_expr) {
		  draw_eval_string(key_expr);
	    } else if (needs_key) {
		  /* For first/last/next/prev without argument, push empty string */
		  fprintf(vvp_out, "    %%pushi/str \"\";\n");
	    }

	    /* Emit the standalone associative array method opcode */
	    fprintf(vvp_out, "    %%assoc/%s v%p_0;\n", method_name, sig);

	    /* For first/last/next/prev, store updated key back to variable */
	    if (key_sig) {
		  fprintf(vvp_out, "    %%cast/vec4/str %u;\n", key_wid);
		  fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n", key_sig, key_wid);
	    }
      }
}

static void draw_select_vec4(ivl_expr_t expr)
{
	// This is the sub-expression to part-select.
      ivl_expr_t subexpr = ivl_expr_oper1(expr);
	// This is the base of the part select
      ivl_expr_t base = ivl_expr_oper2(expr);
	// This is the part select width
      unsigned wid = ivl_expr_width(expr);
	// Is the select base expression signed or unsigned?
      char sign_suff = ivl_expr_signed(base)? 's' : 'u';

	// Special Case: If the sub-expression is a STRING, then this
	// is a select from that string.
      if (ivl_expr_value(subexpr)==IVL_VT_STRING) {
	    assert(base);
	    assert(wid==8);
	    draw_eval_string(subexpr);
	    int base_idx = allocate_word();
	    draw_eval_expr_into_integer(base, base_idx);
	    fprintf(vvp_out, "    %%substr/vec4 %d, %u;\n", base_idx, wid);
	    fprintf(vvp_out, "    %%pop/str 1;\n");
	    clr_word(base_idx);
	    return;
      }

      if (ivl_expr_value(subexpr)==IVL_VT_DARRAY ||
          ivl_expr_value(subexpr)==IVL_VT_QUEUE) {
	    ivl_signal_t sig = ivl_expr_signal(subexpr);
	    assert(sig);
	    assert( (ivl_signal_data_type(sig)==IVL_VT_DARRAY)
		    || (ivl_signal_data_type(sig)==IVL_VT_QUEUE) );

	    assert(base);
	    draw_eval_expr_into_integer(base, 3);
	    fprintf(vvp_out, "    %%load/dar/vec4 v%p_0;\n", sig);
	    if (ivl_expr_value(expr) == IVL_VT_BOOL)
		  fprintf(vvp_out, "    %%cast2;\n");

	    return;
      }

      if (ivl_expr_value(subexpr)==IVL_VT_ASSOC) {
	    ivl_signal_t sig = ivl_expr_signal(subexpr);
	    assert(sig);
	    assert(ivl_signal_data_type(sig)==IVL_VT_ASSOC);

	    assert(base);
	      /* Evaluate the index expression onto the string stack */
	    draw_eval_string(base);
	    fprintf(vvp_out, "    %%load/assoc/vec4 v%p_0;\n", sig);
	    if (ivl_expr_value(expr) == IVL_VT_BOOL)
		  fprintf(vvp_out, "    %%cast2;\n");

	    return;
      }

      if (test_immediate_vec4_ok(base)) {
	    unsigned long val0, valx;
	    unsigned base_wid;
	    make_immediate_vec4_words(base, &val0, &valx, &base_wid);
	    assert(valx == 0);

	    draw_eval_vec4(subexpr);
	    fprintf(vvp_out, "    %%parti/%c %u, %lu, %u;\n",
		    sign_suff, wid, val0, base_wid);

      } else {
	    draw_eval_vec4(subexpr);
	    draw_eval_vec4(base);
	    fprintf(vvp_out, "    %%part/%c %u;\n", sign_suff, wid);
      }
}

static void draw_select_pad_vec4(ivl_expr_t expr)
{
	// This is the sub-expression to pad/truncate
      ivl_expr_t subexpr = ivl_expr_oper1(expr);
	// This is the target width of the expression
      unsigned wid = ivl_expr_width(expr);

	// Push the sub-expression onto the stack.
      draw_eval_vec4(subexpr);

	// Special case: The expression is already the correct width,
	// so there is nothing to be done.
      if (wid == ivl_expr_width(subexpr))
	    return;

      if (ivl_expr_signed(expr))
	    fprintf(vvp_out, "    %%pad/s %u;\n", wid);
      else
	    fprintf(vvp_out, "    %%pad/u %u;\n", wid);
}

/*
 * This function handles the special case of a call to the internal
 * functions $ivl_queue_method$pop_back et al. The first (and only)
 * argument is the signal that represents a dynamic queue. Generate a
 * %qpop instruction to pop a value and push it to the vec4 stack.
 */
static void draw_darray_pop(ivl_expr_t expr)
{
      const char*fb;

      if (strcmp(ivl_expr_name(expr), "$ivl_queue_method$pop_back")==0)
	    fb = "b";
      else
	    fb = "f";

      ivl_expr_t arg = ivl_expr_parm(expr, 0);

      /* Handle property expressions - load the containing object and
         use %prop/q/popf or %prop/q/popb to pop from the queue property. */
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

	    /* Pop from the queue property and push result to vec4 stack */
	    fprintf(vvp_out, "    %%prop/q/pop%s %u, %u;\n", fb, prop_idx,
	            ivl_expr_width(expr));
	    /* Pop the object from the object stack */
	    fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
	    return;
      }

      assert(ivl_expr_type(arg) == IVL_EX_SIGNAL);

      fprintf(vvp_out, "    %%qpop/%s/v v%p_0, %u;\n", fb, ivl_expr_signal(arg),
                       ivl_expr_width(expr));
}

static void draw_sfunc_vec4(ivl_expr_t expr)
{
      unsigned parm_count = ivl_expr_parms(expr);

	/* Special case: If there are no arguments to print, then the
	   %vpi_call statement is easy to draw. */
      if (parm_count == 0) {
	    assert(ivl_expr_value(expr)==IVL_VT_LOGIC
		   || ivl_expr_value(expr)==IVL_VT_BOOL);

	    fprintf(vvp_out, "    %%vpi_func %u %u \"%s\" %u {0 0 0};\n",
		    ivl_file_table_index(ivl_expr_file(expr)),
		    ivl_expr_lineno(expr), ivl_expr_name(expr),
		    ivl_expr_width(expr));
	    return;
      }

      if (strcmp(ivl_expr_name(expr), "$ivl_queue_method$pop_back")==0) {
	    draw_darray_pop(expr);
	    return;
      }
      if (strcmp(ivl_expr_name(expr),"$ivl_queue_method$pop_front")==0) {
	    draw_darray_pop(expr);
	    return;
      }

      if (strcmp(ivl_expr_name(expr),"$size")==0) {
	    /* Special handling for $size on property expressions.
	       For property expressions, we need to load the containing
	       object and use %prop/dar/size to get the dynamic array size. */
	    ivl_expr_t arg = ivl_expr_parm(expr, 0);
	    if (arg && ivl_expr_type(arg) == IVL_EX_PROPERTY) {
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

		  /* Get the size of the darray property */
		  fprintf(vvp_out, "    %%prop/dar/size %u;\n", prop_idx);
		  /* Pop the object from the object stack */
		  fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
		  return;
	    }
	    /* Fall through to generic VPI handling for signals */
      }

      if (strcmp(ivl_expr_name(expr),"$ivl_randomize")==0) {
	      /* The argument is a class object expression. Push it to the object
	         stack, then call %randomize which will randomize its properties
	         and push the result (1=success) to the vec4 stack. */
	    ivl_expr_t arg = ivl_expr_parm(expr, 0);

	      /* Use draw_eval_object to handle any object expression type,
	         including signals and properties. */
	    draw_eval_object(arg);
	    fprintf(vvp_out, "    %%randomize;\n");
	    return;
      }

      if (strcmp(ivl_expr_name(expr),"$ivl_std_randomize")==0) {
	      /* std::randomize(var) - randomize a standalone variable
	         The argument is a signal expression. Generate random bits
	         and store them, then push 1 (success) to vec4 stack. */
	    ivl_expr_t arg = ivl_expr_parm(expr, 0);

	    if (ivl_expr_type(arg) == IVL_EX_SIGNAL) {
		  ivl_signal_t sig = ivl_expr_signal(arg);
		  unsigned wid = ivl_signal_width(sig);

		  /* Generate random value and store to signal */
		  fprintf(vvp_out, "    %%std_randomize v%p_0, %u;\n", sig, wid);
	    } else {
		  fprintf(vvp_out, "; WARNING: $ivl_std_randomize argument is not a simple signal\n");
		  /* Push 0 (failure) if we can't randomize */
		  fprintf(vvp_out, "    %%pushi/vec4 0, 0, 32;\n");
		  return;
	    }
	    /* Push 1 (success) */
	    fprintf(vvp_out, "    %%pushi/vec4 1, 0, 32;\n");
	    return;
      }

      if (strcmp(ivl_expr_name(expr),"$ivl_cast")==0) {
	      /* $cast(dest, src) - check if src's actual type is compatible
	         with dest's declared type. If yes, assign and return 1.
	         If no, return 0.
	         Arguments: arg0 = dest signal, arg1 = src expression */
	    ivl_expr_t dst_expr = ivl_expr_parm(expr, 0);
	    ivl_expr_t src_expr = ivl_expr_parm(expr, 1);

	    /* Get the destination signal and its declared class type */
	    ivl_signal_t dst_sig = NULL;
	    ivl_type_t dst_type = NULL;

	    if (ivl_expr_type(dst_expr) == IVL_EX_SIGNAL) {
		  dst_sig = ivl_expr_signal(dst_expr);
		  dst_type = ivl_signal_net_type(dst_sig);
	    } else if (ivl_expr_type(dst_expr) == IVL_EX_PROPERTY) {
		  /* Cast to property - need to:
		     1. Load the object containing the property
		     2. Evaluate source (as object for class, as vec4 for non-class)
		     3. Check compatibility and store to property
		  */
		  dst_type = ivl_expr_net_type(dst_expr);
		  int prop_idx = ivl_expr_property_idx(dst_expr);
		  ivl_signal_t sig = ivl_expr_signal(dst_expr);
		  ivl_expr_t base = ivl_expr_property_base(dst_expr);

		  /* Load the object that owns the property */
		  if (base) {
			draw_eval_object(base);
		  } else if (sig) {
			fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
		  } else {
			fprintf(vvp_out, "; ERROR: $cast to property - cannot find object\n");
			fprintf(vvp_out, "    %%pushi/vec4 0, 0, 32;\n");
			return;
		  }

		  /* Check if source is a class object or a vector type */
		  ivl_variable_type_t src_vt = ivl_expr_value(src_expr);
		  if (src_vt == IVL_VT_CLASS) {
			/* Source is a class object - use object cast */
			draw_eval_object(src_expr);
			/* Use %cast/prop opcode: checks type, stores if compatible */
			fprintf(vvp_out, "    %%cast/prop %d, C%p;\n", prop_idx, dst_type);
		  } else {
			/* Source is a vector/enum - use simple property store */
			draw_eval_vec4(src_expr);
			/* Store to property directly */
			fprintf(vvp_out, "    %%store/prop/v %d, %u;\n", prop_idx, ivl_expr_width(src_expr));
			fprintf(vvp_out, "    %%pop/obj 1, 0;\n");
			/* Push 1 (success) */
			fprintf(vvp_out, "    %%pushi/vec4 1, 0, 32;\n");
		  }
		  return;
	    } else if (ivl_expr_type(dst_expr) == IVL_EX_SELECT) {
		  /* Cast to struct member or bit/part select.
		   * For enum-to-bits cast (common in UVM), just copy the value.
		   * This is used for patterns like: if ($cast(struct_var.member, enum_prop))
		   */
		  ivl_expr_t base_expr = ivl_expr_oper1(dst_expr);
		  ivl_expr_t off_expr = ivl_expr_oper2(dst_expr);
		  unsigned wid = ivl_expr_width(dst_expr);

		  /* Get the underlying signal */
		  ivl_signal_t sig = NULL;
		  if (ivl_expr_type(base_expr) == IVL_EX_SIGNAL) {
			sig = ivl_expr_signal(base_expr);
		  }

		  if (sig) {
			/* Evaluate source expression to vec4 */
			draw_eval_vec4(src_expr);

			/* Store to signal at offset */
			int off_idx = allocate_word();
			if (off_expr) {
			      draw_eval_expr_into_integer(off_expr, off_idx);
			} else {
			      fprintf(vvp_out, "    %%ix/load %d, 0, 0;\n", off_idx);
			}
			fprintf(vvp_out, "    %%store/vec4 v%p_0, %d, %u;\n", sig, off_idx, wid);
			clr_word(off_idx);
			/* Push 1 (success) */
			fprintf(vvp_out, "    %%pushi/vec4 1, 0, 32;\n");
		  } else {
			fprintf(vvp_out, "; ERROR: $cast to select - base is not a signal\n");
			fprintf(vvp_out, "    %%pushi/vec4 0, 0, 32;\n");
		  }
		  return;
	    } else {
		  fprintf(vvp_out, "; ERROR: $cast destination must be signal or property (got type %d)\n", ivl_expr_type(dst_expr));
		  /* Push 0 (cast failed) */
		  fprintf(vvp_out, "    %%pushi/vec4 0, 0, 32;\n");
		  return;
	    }

	    /* Generate code:
	       1. Evaluate source expression onto object stack (handles any expression type)
	       2. Call %cast with dest signal and dest class type label
	       Result: If compatible, stores to dest and pushes 1 to vec4 stack
	               If not compatible, pushes 0 to vec4 stack */
	    draw_eval_object(src_expr);
	    fprintf(vvp_out, "    %%cast v%p_0, C%p;\n", dst_sig, dst_type);
	    return;
      }

      if (strcmp(ivl_expr_name(expr),"$ivl_config_db_get")==0) {
	    /* $ivl_config_db_get(inst_name, field_name, dest)
	     * - Push inst_name string to string stack
	     * - Push field_name string to string stack
	     * - Get destination (signal or property)
	     * - Call %config_db/get/v or %config_db/get/o depending on type
	     *   which pops strings, looks up value, stores to dest and
	     *   pushes 1/0 to vec4 stack */
	    ivl_expr_t inst_name_expr = ivl_expr_parm(expr, 0);
	    ivl_expr_t field_name_expr = ivl_expr_parm(expr, 1);
	    ivl_expr_t dest_expr = ivl_expr_parm(expr, 2);

	    /* Push inst_name string */
	    draw_eval_string(inst_name_expr);
	    /* Push field_name string */
	    draw_eval_string(field_name_expr);

	    /* Handle destination based on expression type */
	    if (ivl_expr_type(dest_expr) == IVL_EX_SIGNAL) {
		  /* Direct signal destination */
		  ivl_signal_t dst_sig = ivl_expr_signal(dest_expr);
		  ivl_type_t dst_type = ivl_signal_net_type(dst_sig);
		  if (dst_type && ivl_type_base(dst_type) == IVL_VT_CLASS) {
			/* Object type - use %config_db/get/o */
			fprintf(vvp_out, "    %%config_db/get/o v%p_0;\n", dst_sig);
		  } else {
			/* Vec4 type - use %config_db/get/v */
			fprintf(vvp_out, "    %%config_db/get/v v%p_0;\n", dst_sig);
		  }
	    } else if (ivl_expr_type(dest_expr) == IVL_EX_PROPERTY) {
		  /* Property destination - need to load base object first, then store */
		  ivl_signal_t sig = ivl_expr_signal(dest_expr);
		  unsigned pidx = ivl_expr_property_idx(dest_expr);
		  ivl_expr_t base = ivl_expr_property_base(dest_expr);
		  ivl_expr_t arr_idx = ivl_expr_property_array_idx(dest_expr);

		  /* Load the base object (the 'this' object containing the property) */
		  if (base) {
			draw_eval_object(base);
		  } else {
			fprintf(vvp_out, "    %%load/obj v%p_0;\n", sig);
		  }

		  if (arr_idx) {
			/* This is a darray element destination: prop[index]
			 * Stack at this point: [base object]
			 * Need to:
			 * 1. Load the darray property (without popping base)
			 * 2. Evaluate index
			 * 3. Use %config_db/get/dar to lookup and store to element
			 * Stack for opcode: [base object, darray] */
			fprintf(vvp_out, "    %%prop/obj %u, 0; Load darray property\n", pidx);
			/* Don't pop - keep both base and darray on stack */
			int idx_reg = allocate_word();
			draw_eval_expr_into_integer(arr_idx, idx_reg);
			fprintf(vvp_out, "    %%config_db/get/dar %d;\n", idx_reg);
			clr_word(idx_reg);
		  } else {
			/* Use %config_db/get/prop which:
			 * - Pops inst_name, field_name strings
			 * - Pops base object from object stack
			 * - Looks up value in config_db
			 * - Stores to property pidx of base object
			 * - Pushes 1/0 to vec4 stack */
			fprintf(vvp_out, "    %%config_db/get/prop %u;\n", pidx);
		  }
	    } else {
		  fprintf(vvp_out, "; ERROR: $ivl_config_db_get dest must be signal or property (got type %d)\n",
			  ivl_expr_type(dest_expr));
		  fprintf(vvp_out, "    %%pushi/vec4 0, 0, 32;\n");
	    }
	    return;
      }

      draw_vpi_func_call(expr);
}

static void draw_signal_vec4(ivl_expr_t expr)
{
      ivl_signal_t sig = ivl_expr_signal(expr);

	/* Special Case: If the signal is the return value of the function,
	   then use a different opcode to get the value. */
      if (signal_is_return_value(sig)) {
	    assert(ivl_signal_dimensions(sig) == 0);
	    fprintf(vvp_out, "    %%retload/vec4 0; Load %s (draw_signal_vec4)\n",
		    ivl_signal_basename(sig));
	    return;
      }

	/* Handle the simple case, a signal expression that is a
	   simple vector, no array dimensions. */
      if (ivl_signal_dimensions(sig) == 0) {
	    fprintf(vvp_out, "    %%load/vec4 v%p_0;\n", sig);
	    return;
      }

	/* calculate the array index... */
      int addr_index = allocate_word();
      draw_eval_expr_into_integer(ivl_expr_oper1(expr), addr_index);

      fprintf(vvp_out, "    %%load/vec4a v%p, %d;\n", sig, addr_index);
      clr_word(addr_index);
}

static void draw_string_vec4(ivl_expr_t expr)
{
      unsigned wid = ivl_expr_width(expr);
      char*fp = process_octal_codes(ivl_expr_string(expr), wid);
      char*p = fp;

      unsigned long tmp = 0;
      unsigned tmp_wid = 0;
      int push_flag = 0;

      for (unsigned idx = 0 ; idx < wid ; idx += 8) {
	    tmp <<= 8;
	    tmp |= (unsigned long)*p;
	    p += 1;
	    tmp_wid += 8;
	    if (tmp_wid == 32) {
		  fprintf(vvp_out, "    %%pushi/vec4 %lu, 0, 32; draw_string_vec4\n", tmp);
		  tmp = 0;
		  tmp_wid = 0;
		  if (push_flag == 0)
			push_flag += 1;
		  else
			fprintf(vvp_out, "    %%concat/vec4; draw_string_vec4\n");
	    }
      }

      if (tmp_wid > 0) {
	    fprintf(vvp_out, "    %%pushi/vec4 %lu, 0, %u; draw_string_vec4\n", tmp, tmp_wid);
	    if (push_flag != 0)
		  fprintf(vvp_out, "    %%concat/vec4; draw_string_vec4\n");
      }

      free(fp);
}

static void draw_ternary_vec4(ivl_expr_t expr)
{
      ivl_expr_t cond = ivl_expr_oper1(expr);
      ivl_expr_t true_ex = ivl_expr_oper2(expr);
      ivl_expr_t false_ex = ivl_expr_oper3(expr);

      unsigned lab_true  = local_count++;
      unsigned lab_out   = local_count++;

      int use_flag = draw_eval_condition(cond);

	/* The condition flag is used after possibly other statements,
	   so we need to put it into a non-common place. Allocate a
	   safe flag bit and move the condition to the flag position. */
      if (use_flag < 8) {
	    int tmp_flag = allocate_flag();
	    assert(tmp_flag >= 8);
	    fprintf(vvp_out, "    %%flag_mov %d, %d;\n", tmp_flag, use_flag);
	    use_flag = tmp_flag;
      }

      fprintf(vvp_out, "    %%jmp/0 T_%u.%u, %d;\n", thread_count, lab_true, use_flag);

	/* If the condition is true or xz (not false), we need the true
	   expression. If the condition is true, then we ONLY need the
	   true expression. */
      draw_eval_vec4(true_ex);
      fprintf(vvp_out, "    %%jmp/1 T_%u.%u, %d;\n", thread_count, lab_out, use_flag);
      fprintf(vvp_out, "T_%u.%u ; End of true expr.\n", thread_count, lab_true);

	/* If the condition is false or xz (not true), we need the false
	   expression. If the condition is false, then we ONLY need
	   the false expression. */
      draw_eval_vec4(false_ex);
      fprintf(vvp_out, "    %%jmp/0 T_%u.%u, %d;\n", thread_count, lab_out, use_flag);
      fprintf(vvp_out, " ; End of false expr.\n");

	/* Here, the condition is not true or false, it is xz. Both
	   the true and false expressions have been pushed onto the
	   stack, we just need to blend the bits. */
      fprintf(vvp_out, "    %%blend;\n");
      fprintf(vvp_out, "T_%u.%u;\n", thread_count, lab_out);

      clr_flag(use_flag);
}

static void draw_unary_inc_dec(ivl_expr_t sub, bool incr, bool pre)
{
      ivl_signal_t sig = 0;
      unsigned wid = 0;

      switch (ivl_expr_type(sub)) {
	  case IVL_EX_SELECT: {
		ivl_expr_t e1 = ivl_expr_oper1(sub);
		sig = ivl_expr_signal(e1);
		wid = ivl_expr_width(e1);
		break;
	  }

	  case IVL_EX_SIGNAL:
	    sig = ivl_expr_signal(sub);
	    wid = ivl_expr_width(sub);
	    break;

	  default:
	    assert(0);
	    break;
      }

      draw_eval_vec4(sub);

      const char*cmd = incr? "%add" : "%sub";

      if (pre) {
	      /* prefix means we add the result first, and store the
		 result, as well as leaving a copy on the stack. */
	    fprintf(vvp_out, "    %si 1, 0, %u;\n", cmd, wid);
	    fprintf(vvp_out, "    %%dup/vec4;\n");
	    fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n", sig, wid);

      } else {
	      /* The post-fix decrement returns the non-decremented
		 version, so there is a slight re-arrange. */
	    fprintf(vvp_out, "    %%dup/vec4;\n");
	    fprintf(vvp_out, "    %si 1, 0, %u;\n", cmd, wid);
	    fprintf(vvp_out, "    %%store/vec4 v%p_0, 0, %u;\n", sig, wid);
      }
}

static void draw_unary_vec4(ivl_expr_t expr)
{
      ivl_expr_t sub = ivl_expr_oper1(expr);

      if (debug_draw) {
	    fprintf(vvp_out, " ; %s:%u:draw_unary_vec4: opcode=%c\n",
		    ivl_expr_file(expr), ivl_expr_lineno(expr),
		    ivl_expr_opcode(expr));
      }

      switch (ivl_expr_opcode(expr)) {
	  case '&':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%and/r;\n");
	    break;

	  case '|':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%or/r;\n");
	    break;

	  case '^':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%xor/r;\n");
	    break;

	  case '~':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%inv;\n");
	    break;

	  case '!':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%nor/r;\n");
	    break;

	  case '-':
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%inv;\n");
	    fprintf(vvp_out, "    %%addi 1, 0, %u;\n", ivl_expr_width(sub));
	    break;

	  case 'A': /* nand (~&) */
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%nand/r;\n");
	    break;

	  case 'D': /* pre-decrement (--x) */
	    draw_unary_inc_dec(sub, false, true);
	    break;

	  case 'd': /* post_decrement (x--) */
	    draw_unary_inc_dec(sub, false, false);
	    break;

	  case 'I': /* pre-increment (++x) */
	    draw_unary_inc_dec(sub, true, true);
	    break;

	  case 'i': /* post-increment (x++) */
	    draw_unary_inc_dec(sub, true, false);
	    break;

	  case 'N': /* nor (~|) */
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%nor/r;\n");
	    break;

	  case 'X': /* xnor (~^) */
	    draw_eval_vec4(sub);
	    fprintf(vvp_out, "    %%xnor/r;\n");
	    break;

	  case 'm': /* abs(m) */
	    draw_eval_vec4(sub);
	    if (! ivl_expr_signed(sub))
		  break;

	      /* Test if (m) < 0 */
	    fprintf(vvp_out, "    %%dup/vec4;\n");
	    fprintf(vvp_out, "    %%cmpi/s 0, 0, %u;\n", ivl_expr_width(sub));
	    fprintf(vvp_out, "    %%jmp/0xz T_%u.%u, 5;\n", thread_count, local_count);
	      /* If so, calculate -(m) */
	    fprintf(vvp_out, "    %%inv;\n");
	    fprintf(vvp_out, "    %%addi 1, 0, %u;\n", ivl_expr_width(sub));
	    fprintf(vvp_out, "T_%u.%u ;\n", thread_count, local_count);
	    local_count += 1;
	    break;

	  case 'v': /* Cast expression to vec4 */
	    switch (ivl_expr_value(sub)) {
		case IVL_VT_REAL:
		  draw_eval_real(sub);
		  fprintf(vvp_out, "    %%cvt/vr %u;\n", ivl_expr_width(expr));
		  break;
		case IVL_VT_STRING:
		  draw_eval_string(sub);
		  fprintf(vvp_out, "    %%cast/vec4/str %u;\n", ivl_expr_width(expr));
		  break;
		case IVL_VT_DARRAY:
		  draw_eval_object(sub);
		  fprintf(vvp_out, "    %%cast/vec4/dar %u;\n", ivl_expr_width(expr));
		  break;
		default:
		  assert(0);
		  break;
	    }
	    break;

	  case '2': /* Cast expression to bool */
	    switch (ivl_expr_value(sub)) {
		case IVL_VT_LOGIC:
		  draw_eval_vec4(sub);
		  fprintf(vvp_out, "    %%cast2;\n");
		  resize_vec4_wid(sub, ivl_expr_width(expr));
		  break;
		case IVL_VT_BOOL:
		  draw_eval_vec4(sub);
		  resize_vec4_wid(sub, ivl_expr_width(expr));
		  break;
		case IVL_VT_REAL:
		  draw_eval_real(sub);
		  fprintf(vvp_out, "    %%cvt/vr %u;\n", ivl_expr_width(expr));
		  break;
		case IVL_VT_STRING:
		  draw_eval_string(sub);
		  fprintf(vvp_out, "    %%cast/vec4/str %u;\n", ivl_expr_width(expr));
		  break;
		case IVL_VT_DARRAY:
		  draw_eval_object(sub);
		  fprintf(vvp_out, "    %%cast/vec2/dar %u;\n", ivl_expr_width(expr));
		  break;
		default:
		  assert(0);
		  break;
	    }
	    break;

	  default:
	    fprintf(stderr, "XXXX Unary operator %c not implemented\n", ivl_expr_opcode(expr));
	    break;
      }
}

void draw_eval_vec4(ivl_expr_t expr)
{
      if (debug_draw) {
	    fprintf(vvp_out, " ; %s:%u:draw_eval_vec4: expr_type=%d\n",
		    ivl_expr_file(expr), ivl_expr_lineno(expr),
		    ivl_expr_type(expr));
      }

      if (ivl_expr_value(expr) != IVL_VT_BOOL &&
          ivl_expr_value(expr) != IVL_VT_VECTOR) {
	    fprintf(stderr, "draw_eval_vec4: unexpected value type %d (expr_type=%d) at %s:%u\n",
		    ivl_expr_value(expr), ivl_expr_type(expr),
		    ivl_expr_file(expr), ivl_expr_lineno(expr));
      }
      assert(ivl_expr_value(expr) == IVL_VT_BOOL ||
	     ivl_expr_value(expr) == IVL_VT_VECTOR);

      switch (ivl_expr_type(expr)) {
	  case IVL_EX_BINARY:
	    draw_binary_vec4(expr);
	    return;

	  case IVL_EX_CONCAT:
	    draw_concat_vec4(expr);
	    return;

	  case IVL_EX_NUMBER:
	    draw_number_vec4(expr);
	    return;

	  case IVL_EX_SELECT:
	    if (ivl_expr_oper2(expr)==0)
		  draw_select_pad_vec4(expr);
	    else
		  draw_select_vec4(expr);
	    return;

	  case IVL_EX_SFUNC:
	    draw_sfunc_vec4(expr);
	    return;

	  case IVL_EX_SIGNAL:
	    draw_signal_vec4(expr);
	    return;

	  case IVL_EX_STRING:
	    draw_string_vec4(expr);
	    return;

	  case IVL_EX_TERNARY:
	    draw_ternary_vec4(expr);
	    return;

	  case IVL_EX_UFUNC:
	    draw_ufunc_vec4(expr);
	    return;

	  case IVL_EX_UNARY:
	    draw_unary_vec4(expr);
	    return;

	  case IVL_EX_PROPERTY:
	    draw_property_vec4(expr);
	    return;

	  case IVL_EX_VIFPROP:
	    draw_vifprop_vec4(expr);
	    return;

	  case IVL_EX_ASSOC_METHOD:
	    draw_assoc_method_vec4(expr);
	    return;

	  case IVL_EX_NULL:
	    fprintf(stderr, "%s:%u: Error: 'null' used in an expression\n",
	                    ivl_expr_file(expr), ivl_expr_lineno(expr));
	    fprintf(vvp_out, "; Error 'null' used in an expression\n");
	    vvp_errors += 1;
	    return;

	  default:
	    break;
      }

      fprintf(stderr, "%s:%u: Sorry: cannot evaluate VEC4 expression (%d)\n",
                      ivl_expr_file(expr), ivl_expr_lineno(expr),
                      ivl_expr_type(expr));
      fprintf(vvp_out, "; Sorry: cannot evaluate VEC4 expression (%d)\n",
                       ivl_expr_type(expr));
      vvp_errors += 1;
}
