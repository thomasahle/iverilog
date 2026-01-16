/*
 *  Copyright (C) 2018-2021  Cary R. (cygcary@yahoo.com)
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include "vpi_user.h"
#include "sys_priv.h"

/*
 * Check that $couintbits() is called with the correct arguments.
 */
static PLI_INT32 countbits_compiletf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv, arg;
      int cb_count = 1;

      assert(callh != 0);
      argv = vpi_iterate(vpiArgument, callh);
      (void)name;  /* Parameter is not used. */

	/* $countbits() must have arguments. */
      if (argv == 0) {
	    vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
	               (int)vpi_get(vpiLineNo, callh));
	    vpi_printf("$countbits() requires at least two arguments.\n");
	    vpip_set_return_value(1);
	    vpi_control(vpiFinish, 1);
	    return 0;
      }

	/* The 1st argument must be numeric. */
      arg = vpi_scan(argv);
      if (! is_numeric_obj(arg)) {
	    vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
	               (int)vpi_get(vpiLineNo, callh));
	    vpi_printf("The first argument to $countbits() must be numeric.\n");
	    vpip_set_return_value(1);
	    vpi_control(vpiFinish, 1);
      }

	/* We need one or more numeric control bit arguments. */
      arg = vpi_scan(argv);
      if (! arg) {
	    vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
	               (int)vpi_get(vpiLineNo, callh));
	    vpi_printf("$countbits() requires at least one control bit "
	               "argument.\n");
	    vpip_set_return_value(1);
	    vpi_control(vpiFinish, 1);
      }

      do {
	    if (arg && ! is_numeric_obj(arg)) {
		  vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
		             (int)vpi_get(vpiLineNo, callh));
		  vpi_printf("Control bit argument %d to $countbits() must "
		             "be numeric.\n", cb_count);
		  vpip_set_return_value(1);
		  vpi_control(vpiFinish, 1);
	    }
	    ++cb_count;
	    if (arg) arg = vpi_scan(argv);
      } while (arg);

      return 0;
}

/* Count the number of bits in the expression that match the search bits. */
static PLI_INT32 count_bits_in_expr(vpiHandle expr_arg, char search[4])
{
      s_vpi_value val;
      PLI_INT32 result;
      PLI_INT32 size = vpi_get(vpiSize, expr_arg);
      assert(size > 0);

      val.format = vpiVectorVal;
      vpi_get_value(expr_arg, &val);

      result = 0;
      for (unsigned lp = 0; lp < (unsigned)size; ++lp) {
	    unsigned offset = lp / 32;
	    unsigned bit = lp % 32;
	    unsigned abit, bbit;
	    abit = (val.value.vector[offset].aval >> bit) & 0x1;
	    bbit = (val.value.vector[offset].bval >> bit) & 0x1;
	    if (search[(bbit<<1)|abit]) ++result;
      }

      return result;
}

static PLI_INT32 countbits_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      vpiHandle arg;
      char search[4];
      (void)name;  /* Parameter is not used. */

	/* Scan the control bit arguments and mark which control bits to
	 * include in the count. */
      for (unsigned lp = 0; lp < 4 ; ++lp) search[lp] = 0;
      while ((arg = vpi_scan(argv))) {
	    s_vpi_value val;
	    val.format = vpiScalarVal;
	    vpi_get_value(arg, &val);
	    switch (val.value.scalar) {
	      case vpi0:
		  search[0] = 1;
		  break;
	      case vpi1:
		  search[1] = 1;
		  break;
	      case vpiZ:
		  search[2] = 1;
		  break;
	      case vpiX:
		  search[3] = 1;
		  break;
	      default:
		  vpi_printf("WARNING: %s:%d: ", vpi_get_str(vpiFile, callh),
		             (int)vpi_get(vpiLineNo, callh));
		  vpi_printf("Unknown scalar control bit argument %d passed "
		             "to $countbits() will be ignored.\n",
		             val.value.scalar);
		  break;
	    }
      }

      put_integer_value(callh, count_bits_in_expr(expr_arg, search));

      return 0;
}

/* Count the number of ones in the expression. */
static PLI_INT32 count_ones_in_expr(vpiHandle expr_arg)
{
      s_vpi_value val;
      PLI_INT32 result;
      PLI_INT32 size = vpi_get(vpiSize, expr_arg);
      assert(size > 0);

      val.format = vpiVectorVal;
      vpi_get_value(expr_arg, &val);

      result = 0;
      size = (size + 31) / 32;
      for (unsigned lp = 0; lp < (unsigned)size; ++lp) {
            PLI_UINT32 ones = ~val.value.vector[lp].bval &
                               val.value.vector[lp].aval;
	    while (ones) {
		  if (ones & 0x1) ++result;
		  ones >>= 1;
	    }
      }

      return result;
}

static PLI_INT32 countones_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      put_integer_value(callh, count_ones_in_expr(expr_arg));

      return 0;
}

/* Check to see if the expression is onehot. */
static PLI_INT32 is_onehot(vpiHandle expr_arg, unsigned zero_is_okay)
{
      s_vpi_value val;
      unsigned found_a_one;
      PLI_INT32 size = vpi_get(vpiSize, expr_arg);
      assert(size > 0);

      val.format = vpiVectorVal;
      vpi_get_value(expr_arg, &val);

      found_a_one = 0;
      size = (size + 31) / 32;
      for (unsigned lp = 0; lp < (unsigned)size; ++lp) {
            PLI_UINT32 ones = ~val.value.vector[lp].bval &
                               val.value.vector[lp].aval;
	    while (ones) {
		  if (ones & 0x1) {
			if (found_a_one) return vpi0;
			found_a_one = 1;
		  }
		  ones >>= 1;
	    }
      }

      if (found_a_one) return vpi1;
      else if (zero_is_okay) return vpi1;
      return vpi0;
}

static PLI_INT32 onehot_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      put_scalar_value(callh, is_onehot(expr_arg, 0));

      return 0;
}

static PLI_INT32 onehot0_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      put_scalar_value(callh, is_onehot(expr_arg, 1));

      return 0;
}

/* Check to see if the expression has an undefined value. */
static PLI_INT32 is_unknown(vpiHandle expr_arg)
{
      s_vpi_value val;
      PLI_INT32 size = vpi_get(vpiSize, expr_arg);
      assert(size > 0);

      val.format = vpiVectorVal;
      vpi_get_value(expr_arg, &val);

      size = (size + 31) / 32;
      for (unsigned lp = 0; lp < (unsigned)size; ++lp) {
            if (val.value.vector[lp].bval) return vpi1;
      }

      return vpi0;
}

static PLI_INT32 isunknown_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      put_scalar_value(callh, is_unknown(expr_arg));

      return 0;
}

/*
 * Structure to hold previous value for $stable/$changed
 */
typedef struct stable_state_s {
      int initialized;
      PLI_INT32 prev_value;
      int prev_size;
} stable_state_t;

/*
 * Structure to hold history buffer for $past(expr, N)
 * Supports up to MAX_PAST_DEPTH cycles
 */
#define MAX_PAST_DEPTH 32
typedef struct past_state_s {
      int initialized;
      int depth;  /* Actual depth requested (1 to MAX_PAST_DEPTH) */
      int count;  /* Number of values stored */
      int write_idx;  /* Next write position in circular buffer */
      PLI_INT32 history[MAX_PAST_DEPTH];
} past_state_t;

/*
 * $stable(expr) - returns 1 if expression hasn't changed since last sample
 * This is a sampled value function used in assertions.
 */
static PLI_INT32 stable_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      s_vpi_value val;
      stable_state_t *state;
      PLI_INT32 curr_value;
      int result;
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      /* Get current value as integer */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer;

      /* Get or create state for this call site */
      state = (stable_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            state = (stable_state_t *)malloc(sizeof(stable_state_t));
            state->initialized = 0;
            vpi_put_userdata(callh, state);
      }

      /* First call: initialize with current value, return 1 (stable) */
      if (!state->initialized) {
            state->prev_value = curr_value;
            state->initialized = 1;
            result = 1;  /* Assume stable on first sample */
      } else {
            /* Compare current to previous */
            result = (curr_value == state->prev_value) ? 1 : 0;
            /* Update stored value */
            state->prev_value = curr_value;
      }

      put_scalar_value(callh, result ? vpi1 : vpi0);

      return 0;
}

/*
 * $changed(expr) - returns 1 if expression has changed since last sample
 * This is the opposite of $stable.
 */
static PLI_INT32 changed_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      s_vpi_value val;
      stable_state_t *state;
      PLI_INT32 curr_value;
      int result;
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      /* Get current value as integer */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer;

      /* Get or create state for this call site */
      state = (stable_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            state = (stable_state_t *)malloc(sizeof(stable_state_t));
            state->initialized = 0;
            vpi_put_userdata(callh, state);
      }

      /* First call: initialize with current value, return 0 (not changed yet) */
      if (!state->initialized) {
            state->prev_value = curr_value;
            state->initialized = 1;
            result = 0;  /* No change on first sample */
      } else {
            /* Compare current to previous */
            result = (curr_value != state->prev_value) ? 1 : 0;
            /* Update stored value */
            state->prev_value = curr_value;
      }

      put_scalar_value(callh, result ? vpi1 : vpi0);

      return 0;
}

/*
 * $rose(expr) - returns 1 if expression transitioned from 0 to 1
 */
static PLI_INT32 rose_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      s_vpi_value val;
      stable_state_t *state;
      PLI_INT32 curr_value;
      int result;
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      /* Get current value - just need LSB for rose/fell */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer & 1;

      /* Get or create state for this call site */
      state = (stable_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            state = (stable_state_t *)malloc(sizeof(stable_state_t));
            state->initialized = 0;
            vpi_put_userdata(callh, state);
      }

      /* First call: initialize, return 0 (no transition yet) */
      if (!state->initialized) {
            state->prev_value = curr_value;
            state->initialized = 1;
            result = 0;
      } else {
            /* Rose = was 0, now 1 */
            result = (state->prev_value == 0 && curr_value == 1) ? 1 : 0;
            state->prev_value = curr_value;
      }

      put_scalar_value(callh, result ? vpi1 : vpi0);

      return 0;
}

/*
 * $fell(expr) - returns 1 if expression transitioned from 1 to 0
 */
static PLI_INT32 fell_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      s_vpi_value val;
      stable_state_t *state;
      PLI_INT32 curr_value;
      int result;
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      /* Get current value - just need LSB for rose/fell */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer & 1;

      /* Get or create state for this call site */
      state = (stable_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            state = (stable_state_t *)malloc(sizeof(stable_state_t));
            state->initialized = 0;
            vpi_put_userdata(callh, state);
      }

      /* First call: initialize, return 0 (no transition yet) */
      if (!state->initialized) {
            state->prev_value = curr_value;
            state->initialized = 1;
            result = 0;
      } else {
            /* Fell = was 1, now 0 */
            result = (state->prev_value == 1 && curr_value == 0) ? 1 : 0;
            state->prev_value = curr_value;
      }

      put_scalar_value(callh, result ? vpi1 : vpi0);

      return 0;
}

/*
 * $past(expr) or $past(expr, N) - returns the value of expression from N cycles ago
 * N defaults to 1 if not specified. N must be 1 to MAX_PAST_DEPTH.
 * Note: This simplified version only works for integer-sized values.
 */
static PLI_INT32 past_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      vpiHandle depth_arg = vpi_scan(argv);  /* Optional second argument */
      s_vpi_value val;
      past_state_t *state;
      PLI_INT32 curr_value;
      PLI_INT32 result_value;
      int depth = 1;  /* Default depth */
      int read_idx;
      (void)name;  /* Parameter is not used. */

      /* Get optional depth argument */
      if (depth_arg) {
            val.format = vpiIntVal;
            vpi_get_value(depth_arg, &val);
            depth = val.value.integer;
            if (depth < 1) depth = 1;
            if (depth > MAX_PAST_DEPTH) depth = MAX_PAST_DEPTH;
            vpi_free_object(argv);
      }

      /* Get current value as integer */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer;

      /* Get or create state for this call site */
      state = (past_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            int i;
            state = (past_state_t *)malloc(sizeof(past_state_t));
            state->initialized = 0;
            state->depth = depth;
            state->count = 0;
            state->write_idx = 0;
            for (i = 0; i < MAX_PAST_DEPTH; i++)
                  state->history[i] = 0;
            vpi_put_userdata(callh, state);
      }

      /* First few calls: not enough history yet */
      if (state->count < state->depth) {
            /* Store current value and return it (no real past available) */
            state->history[state->write_idx] = curr_value;
            state->write_idx = (state->write_idx + 1) % MAX_PAST_DEPTH;
            state->count++;
            result_value = curr_value;  /* Return current when not enough history */
      } else {
            /* Read value from 'depth' cycles ago (oldest in the requested range) */
            read_idx = (state->write_idx - state->depth + MAX_PAST_DEPTH) % MAX_PAST_DEPTH;
            result_value = state->history[read_idx];
            /* Store current value for future */
            state->history[state->write_idx] = curr_value;
            state->write_idx = (state->write_idx + 1) % MAX_PAST_DEPTH;
      }

      val.format = vpiIntVal;
      val.value.integer = result_value;
      vpi_put_value(callh, &val, 0, vpiNoDelay);

      return 0;
}

/*
 * Compiletf for $past - allows 1 or 2 numeric arguments
 */
static PLI_INT32 past_compiletf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle arg;

      (void)name;

      /* Must have at least one argument */
      if (argv == 0) {
            vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
                       (int)vpi_get(vpiLineNo, callh));
            vpi_printf("$past requires at least one argument.\n");
            vpip_set_return_value(1);
            vpi_control(vpiFinish, 1);
            return 0;
      }

      /* First argument must be numeric */
      arg = vpi_scan(argv);
      if (!is_numeric_obj(arg)) {
            vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
                       (int)vpi_get(vpiLineNo, callh));
            vpi_printf("$past first argument must be numeric.\n");
            vpip_set_return_value(1);
            vpi_control(vpiFinish, 1);
            vpi_free_object(argv);
            return 0;
      }

      /* Optional second argument must be numeric (depth) */
      arg = vpi_scan(argv);
      if (arg) {
            if (!is_numeric_obj(arg)) {
                  vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
                             (int)vpi_get(vpiLineNo, callh));
                  vpi_printf("$past second argument (depth) must be numeric.\n");
                  vpip_set_return_value(1);
                  vpi_control(vpiFinish, 1);
                  vpi_free_object(argv);
                  return 0;
            }
            /* Check for too many arguments */
            arg = vpi_scan(argv);
            if (arg) {
                  vpi_printf("ERROR: %s:%d: ", vpi_get_str(vpiFile, callh),
                             (int)vpi_get(vpiLineNo, callh));
                  vpi_printf("$past takes at most 2 arguments.\n");
                  vpip_set_return_value(1);
                  vpi_control(vpiFinish, 1);
                  vpi_free_object(argv);
                  return 0;
            }
      }

      return 0;
}

/*
 * $sampled(expr) - returns the value of expression from the previous time step
 * In SVA, $sampled returns the value at the preponed region of the current time step,
 * which is essentially the same as the previous sample.
 */
static PLI_INT32 sampled_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle expr_arg = vpi_scan(argv);
      s_vpi_value val;
      stable_state_t *state;
      PLI_INT32 curr_value;
      PLI_INT32 result_value;
      (void)name;  /* Parameter is not used. */

      vpi_free_object(argv);

      /* Get current value as integer */
      val.format = vpiIntVal;
      vpi_get_value(expr_arg, &val);
      curr_value = val.value.integer;

      /* Get or create state for this call site */
      state = (stable_state_t *)vpi_get_userdata(callh);
      if (state == NULL) {
            state = (stable_state_t *)malloc(sizeof(stable_state_t));
            state->initialized = 0;
            vpi_put_userdata(callh, state);
      }

      /* First call: return current value (no previous exists) */
      if (!state->initialized) {
            state->prev_value = curr_value;
            state->initialized = 1;
            result_value = curr_value;  /* Return current on first sample */
      } else {
            /* Return the sampled (previous) value */
            result_value = state->prev_value;
            /* Update stored value for next time */
            state->prev_value = curr_value;
      }

      val.format = vpiIntVal;
      val.value.integer = result_value;
      vpi_put_value(callh, &val, 0, vpiNoDelay);

      return 0;
}

typedef struct sva_step_s {
      int min_delay;
      int max_delay;
      int atom_count;
      int *atoms;
} sva_step_t;

typedef struct sva_seq_s {
      int step_count;
      sva_step_t *steps;
      int invariant_count;
      int *invariants;
} sva_seq_t;

typedef struct sva_thread_s {
      int step_idx;
      int delay;
      struct sva_thread_s *next;
} sva_thread_t;

typedef struct sva_prop_s {
      int id;
      int immediate;
      int implies_kind;
      int atom_count;
      sva_seq_t antecedent;
      sva_seq_t consequent;
      sva_thread_t *ant_threads;
      sva_thread_t *cons_threads;
      uint64_t last_time;
      int last_result;
} sva_prop_t;

static sva_prop_t **sva_props = 0;
static unsigned sva_prop_count = 0;

static int sva_get_int(vpiHandle arg)
{
      s_vpi_value val;
      val.format = vpiIntVal;
      vpi_get_value(arg, &val);
      return val.value.integer;
}

static sva_prop_t *sva_find_prop(int id)
{
      for (unsigned i = 0; i < sva_prop_count; ++i) {
	    if (sva_props[i] && sva_props[i]->id == id)
		  return sva_props[i];
      }
      return 0;
}

static void sva_add_prop(sva_prop_t *prop)
{
      sva_props = (sva_prop_t **)realloc(sva_props, sizeof(*sva_props) * (sva_prop_count + 1));
      sva_props[sva_prop_count++] = prop;
}

static void sva_free_threads(sva_thread_t *thr)
{
      while (thr) {
	    sva_thread_t *next = thr->next;
	    free(thr);
	    thr = next;
      }
}

static int sva_step_match(const sva_step_t *step, const int *vals)
{
      for (int i = 0; i < step->atom_count; ++i) {
	    if (!vals[step->atoms[i]])
		  return 0;
      }
      return 1;
}

static int sva_invariants_hold(const sva_seq_t *seq, const int *vals)
{
      for (int i = 0; i < seq->invariant_count; ++i) {
	    if (!vals[seq->invariants[i]])
		  return 0;
      }
      return 1;
}

static void sva_spawn_thread(sva_thread_t **list)
{
      sva_thread_t *thr = (sva_thread_t *)calloc(1, sizeof(*thr));
      thr->next = *list;
      *list = thr;
}

static void sva_update_threads(const sva_seq_t *seq, sva_thread_t **list,
                               const int *vals, int *matched, int *failed)
{
      sva_thread_t *cur = *list;
      sva_thread_t *prev = 0;

      while (cur) {
	    int drop = 0;

	    if (seq->invariant_count && !sva_invariants_hold(seq, vals)) {
		  drop = 1;
		  if (failed) (*failed)++;
	    } else if (cur->step_idx >= seq->step_count) {
		  drop = 1;
	    } else {
		  const sva_step_t *step = &seq->steps[cur->step_idx];
		  if (step->max_delay != -1 && cur->delay > step->max_delay) {
			drop = 1;
			if (failed) (*failed)++;
		  } else if (cur->delay >= step->min_delay && sva_step_match(step, vals)) {
			cur->step_idx++;
			cur->delay = 0;
			while (cur->step_idx < seq->step_count) {
			      const sva_step_t *next = &seq->steps[cur->step_idx];
			      if (next->min_delay > 0)
				    break;
			      if (next->max_delay != -1 && 0 > next->max_delay) {
				    drop = 1;
				    if (failed) (*failed)++;
				    break;
			      }
			      if (!sva_step_match(next, vals))
				    break;
			      cur->step_idx++;
			}
			if (!drop && cur->step_idx >= seq->step_count) {
			      if (matched) (*matched)++;
			      drop = 1;
			}
		  } else {
			cur->delay++;
		  }
	    }

	    if (drop) {
		  sva_thread_t *next = cur->next;
		  if (prev)
			prev->next = next;
		  else
			*list = next;
		  free(cur);
		  cur = next;
	    } else {
		  prev = cur;
		  cur = cur->next;
	    }
      }
}

static PLI_INT32 sva_register_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle arg;
      int idx;

      (void)name;
      if (!argv)
	    return 0;

      sva_prop_t *prop = (sva_prop_t *)calloc(1, sizeof(*prop));

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->id = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->immediate = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->implies_kind = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->antecedent.step_count = 0;
      prop->consequent.step_count = 0;
      prop->antecedent.invariant_count = 0;
      prop->consequent.invariant_count = 0;
      prop->atom_count = 0;
      (void)sva_get_int(arg); /* antecedent first_match */

      arg = vpi_scan(argv);
      if (!arg) goto done;
      (void)sva_get_int(arg); /* consequent first_match */

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->atom_count = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->antecedent.step_count = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->antecedent.invariant_count = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->consequent.step_count = sva_get_int(arg);

      arg = vpi_scan(argv);
      if (!arg) goto done;
      prop->consequent.invariant_count = sva_get_int(arg);

      if (prop->antecedent.step_count) {
	    prop->antecedent.steps = (sva_step_t *)calloc(prop->antecedent.step_count,
	                                                   sizeof(sva_step_t));
	    for (idx = 0; idx < prop->antecedent.step_count; ++idx) {
		  sva_step_t *step = &prop->antecedent.steps[idx];
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->min_delay = sva_get_int(arg);
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->max_delay = sva_get_int(arg);
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->atom_count = sva_get_int(arg);
		  if (step->atom_count > 0) {
			step->atoms = (int *)calloc(step->atom_count, sizeof(int));
			for (int j = 0; j < step->atom_count; ++j) {
			      arg = vpi_scan(argv);
			      if (!arg) goto done;
			      step->atoms[j] = sva_get_int(arg);
			}
		  }
	    }
      }

      if (prop->antecedent.invariant_count) {
	    prop->antecedent.invariants = (int *)calloc(prop->antecedent.invariant_count,
	                                                sizeof(int));
	    for (idx = 0; idx < prop->antecedent.invariant_count; ++idx) {
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  prop->antecedent.invariants[idx] = sva_get_int(arg);
	    }
      }

      if (prop->consequent.step_count) {
	    prop->consequent.steps = (sva_step_t *)calloc(prop->consequent.step_count,
	                                                  sizeof(sva_step_t));
	    for (idx = 0; idx < prop->consequent.step_count; ++idx) {
		  sva_step_t *step = &prop->consequent.steps[idx];
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->min_delay = sva_get_int(arg);
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->max_delay = sva_get_int(arg);
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  step->atom_count = sva_get_int(arg);
		  if (step->atom_count > 0) {
			step->atoms = (int *)calloc(step->atom_count, sizeof(int));
			for (int j = 0; j < step->atom_count; ++j) {
			      arg = vpi_scan(argv);
			      if (!arg) goto done;
			      step->atoms[j] = sva_get_int(arg);
			}
		  }
	    }
      }

      if (prop->consequent.invariant_count) {
	    prop->consequent.invariants = (int *)calloc(prop->consequent.invariant_count,
	                                                sizeof(int));
	    for (idx = 0; idx < prop->consequent.invariant_count; ++idx) {
		  arg = vpi_scan(argv);
		  if (!arg) goto done;
		  prop->consequent.invariants[idx] = sva_get_int(arg);
	    }
      }

      prop->last_time = UINT64_MAX;
      prop->last_result = 0;
      sva_add_prop(prop);

done:
      vpi_free_object(argv);
      return 0;
}

static PLI_INT32 sva_check_calltf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      vpiHandle callh = vpi_handle(vpiSysTfCall, 0);
      vpiHandle argv = vpi_iterate(vpiArgument, callh);
      vpiHandle arg;
      s_vpi_time now;
      s_vpi_value rval;
      int result = 0;

      (void)name;
      if (!argv)
	    return 0;

      arg = vpi_scan(argv);
      if (!arg) {
	    vpi_free_object(argv);
	    return 0;
      }
      int id = sva_get_int(arg);
      arg = vpi_scan(argv);
      if (!arg) {
	    vpi_free_object(argv);
	    return 0;
      }
      int disable = sva_get_int(arg);

      sva_prop_t *prop = sva_find_prop(id);
      if (!prop) {
	    vpi_free_object(argv);
	    rval.format = vpiIntVal;
	    rval.value.integer = 0;
	    vpi_put_value(callh, &rval, 0, vpiNoDelay);
	    return 0;
      }

      now.type = vpiSimTime;
      vpi_get_time(0, &now);
      uint64_t sim_time = ((uint64_t)now.high << 32) | now.low;
      if (sim_time == prop->last_time) {
	    rval.format = vpiIntVal;
	    rval.value.integer = prop->last_result;
	    vpi_put_value(callh, &rval, 0, vpiNoDelay);
	    vpi_free_object(argv);
	    return 0;
      }

      int *vals = 0;
      if (prop->atom_count > 0) {
	    vals = (int *)calloc(prop->atom_count, sizeof(int));
	    for (int i = 0; i < prop->atom_count; ++i) {
		  arg = vpi_scan(argv);
		  if (!arg) break;
		  vals[i] = sva_get_int(arg) ? 1 : 0;
	    }
      }

      if (disable) {
	    sva_free_threads(prop->ant_threads);
	    sva_free_threads(prop->cons_threads);
	    prop->ant_threads = 0;
	    prop->cons_threads = 0;
	    result = 0;
      } else if (prop->immediate) {
	    int val = (prop->atom_count > 0) ? vals[0] : 1;
	    result = val ? 1 : 2;
      } else if (prop->implies_kind == 0) {
	    if (prop->consequent.step_count)
		  sva_spawn_thread(&prop->cons_threads);
	    int matched = 0;
	    int failed = 0;
	    sva_update_threads(&prop->consequent, &prop->cons_threads, vals,
	                       &matched, &failed);
	    if (failed)
		  result = 2;
	    else if (matched)
		  result = 1;
      } else {
	    if (prop->antecedent.step_count)
		  sva_spawn_thread(&prop->ant_threads);
	    int ant_matched = 0;
	    sva_update_threads(&prop->antecedent, &prop->ant_threads, vals,
	                       &ant_matched, 0);
	    for (int i = 0; i < ant_matched; ++i)
		  sva_spawn_thread(&prop->cons_threads);
	    int matched = 0;
	    int failed = 0;
	    sva_update_threads(&prop->consequent, &prop->cons_threads, vals,
	                       &matched, &failed);
	    if (failed)
		  result = 2;
	    else if (matched)
		  result = 1;
      }

      prop->last_time = sim_time;
      prop->last_result = result;
      rval.format = vpiIntVal;
      rval.value.integer = result;
      vpi_put_value(callh, &rval, 0, vpiNoDelay);

      free(vals);
      vpi_free_object(argv);
      return 0;
}

static PLI_INT32 bit_vec_sizetf(ICARUS_VPI_CONST PLI_BYTE8 *name)
{
      (void)name;  /* Parameter is not used. */

      return 1;
}

/*
 * Register the functions with Verilog.
 */
void v2009_bitvec_register(void)
{
      s_vpi_systf_data tf_data;
      vpiHandle res;

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiIntFunc;
      tf_data.calltf      = countbits_calltf;
      tf_data.compiletf   = countbits_compiletf;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$countbits";
      tf_data.user_data   = 0;
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiIntFunc;
      tf_data.calltf      = countones_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$countones";
      tf_data.user_data   = "$countones";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = onehot_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$onehot";
      tf_data.user_data   = "$onehot";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = onehot0_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$onehot0";
      tf_data.user_data   = "$onehot0";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = isunknown_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$isunknown";
      tf_data.user_data   = "$isunknown";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      /* Sampled value functions for assertions */
      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = stable_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$stable";
      tf_data.user_data   = "$stable";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = changed_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$changed";
      tf_data.user_data   = "$changed";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = rose_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$rose";
      tf_data.user_data   = "$rose";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiSizedFunc;
      tf_data.calltf      = fell_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = bit_vec_sizetf;
      tf_data.tfname      = "$fell";
      tf_data.user_data   = "$fell";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiIntFunc;
      tf_data.calltf      = past_calltf;
      tf_data.compiletf   = past_compiletf;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$past";
      tf_data.user_data   = "$past";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiIntFunc;
      tf_data.calltf      = sampled_calltf;
      tf_data.compiletf   = sys_one_numeric_arg_compiletf;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$sampled";
      tf_data.user_data   = "$sampled";
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysTask;
      tf_data.sysfunctype = 0;
      tf_data.calltf      = sva_register_calltf;
      tf_data.compiletf   = 0;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$ivl_sva_register";
      tf_data.user_data   = 0;
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);

      tf_data.type        = vpiSysFunc;
      tf_data.sysfunctype = vpiIntFunc;
      tf_data.calltf      = sva_check_calltf;
      tf_data.compiletf   = 0;
      tf_data.sizetf      = 0;
      tf_data.tfname      = "$ivl_sva_check";
      tf_data.user_data   = 0;
      res = vpi_register_systf(&tf_data);
      vpip_make_systf_system_defined(res);
}
