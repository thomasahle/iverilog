/*
 * Copyright (c) 2001-2025 Stephen Williams (steve@icarus.com)
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

# include  "config.h"
# include  "vthread.h"
# include  "codes.h"
# include  "schedule.h"
# include  "ufunc.h"
# include  "event.h"
# include  "vpi_priv.h"
# include  "vvp_net_sig.h"
# include  "vvp_cobject.h"
# include  "vvp_darray.h"
# include  "class_type.h"
# include  "factory_registry.h"
# include  "config_db.h"
#ifdef CHECK_WITH_VALGRIND
# include  "vvp_cleanup.h"
#endif
# include  <set>
# include  <map>
# include  <typeinfo>
# include  <vector>
# include  <cstdlib>
# include  <climits>
# include  <cstring>
# include  <cmath>
# include  <cassert>

# include  <iostream>
# include  <sstream>
# include  <cstdio>

using namespace std;

/* This is the size of an unsigned long in bits. This is just a
   convenience macro. */
# define CPU_WORD_BITS (8*sizeof(unsigned long))
# define TOP_BIT (1UL << (CPU_WORD_BITS-1))

/*
 * This vthread_s structure describes all there is to know about a
 * thread, including its program counter, all the private bits it
 * holds, and its place in other lists.
 *
 *
 * ** Notes On The Interactions of %fork/%join/%end:
 *
 * The %fork instruction creates a new thread and pushes that into a
 * set of children for the thread. This new thread, then, becomes a
 * child of the current thread, and the current thread a parent of the
 * new thread. Any child can be reaped by a %join.
 *
 * Children that are detached with %join/detach need to have a different
 * parent/child relationship since the parent can still effect them if
 * it uses the %disable/fork or %wait/fork opcodes. The i_am_detached
 * flag and detached_children set are used for this relationship.
 *
 * It is a programming error for a thread that created threads to not
 * %join (or %join/detach) as many as it created before it %ends. The
 * children set will get messed up otherwise.
 *
 * the i_am_joining flag is a clue to children that the parent is
 * blocked in a %join and may need to be scheduled. The %end
 * instruction will check this flag in the parent to see if it should
 * notify the parent that something is interesting.
 *
 * The i_have_ended flag, on the other hand, is used by threads to
 * tell their parents that they are already dead. A thread that
 * executes %end will set its own i_have_ended flag and let its parent
 * reap it when the parent does the %join. If a thread has its
 * schedule_parent_on_end flag set already when it %ends, then it
 * reaps itself and simply schedules its parent. If a child has its
 * i_have_ended flag set when a thread executes %join, then it is free
 * to reap the child immediately.
 */

struct vthread_s {
      vthread_s();

      void debug_dump(ostream&fd, const char*label_text);

	/* This is the program counter. */
      vvp_code_t pc;
	/* These hold the private thread bits. */
      enum { FLAGS_COUNT = 512, WORDS_COUNT = 16 };
      vvp_bit4_t flags[FLAGS_COUNT];

	/* These are the word registers. */
      union {
	    int64_t  w_int;
	    uint64_t w_uint;
      } words[WORDS_COUNT];

	// These vectors are depths within the parent thread's
	// corresponding stack.  This is how the %ret/* instructions
	// get at parent thread arguments.
      vector<unsigned> args_real;
      vector<unsigned> args_str;
      vector<unsigned> args_vec4;

    private:
      vector<vvp_vector4_t>stack_vec4_;
    public:
      inline vvp_vector4_t pop_vec4(void)
      {
	    assert(! stack_vec4_.empty());
	    vvp_vector4_t val = stack_vec4_.back();
	    stack_vec4_.pop_back();
	    return val;
      }
      inline void push_vec4(const vvp_vector4_t&val)
      {
	    stack_vec4_.push_back(val);
      }
      inline const vvp_vector4_t& peek_vec4(unsigned depth)
      {
	    unsigned size = stack_vec4_.size();
	    assert(depth < size);
	    unsigned use_index = size-1-depth;
	    return stack_vec4_[use_index];
      }
      inline vvp_vector4_t& peek_vec4(void)
      {
	    unsigned use_index = stack_vec4_.size();
	    assert(use_index >= 1);
	    return stack_vec4_[use_index-1];
      }
      inline void poke_vec4(unsigned depth, const vvp_vector4_t&val)
      {
	    assert(depth < stack_vec4_.size());
	    unsigned use_index = stack_vec4_.size()-1-depth;
	    stack_vec4_[use_index] = val;
      }
      inline void pop_vec4(unsigned cnt)
      {
	    while (cnt > 0) {
		  stack_vec4_.pop_back();
		  cnt -= 1;
	    }
      }
      inline unsigned vec4_stack_size(void) const
      {
	    return stack_vec4_.size();
      }


    private:
      vector<double> stack_real_;
    public:
      inline double pop_real(void)
      {
	    assert(! stack_real_.empty());
	    double val = stack_real_.back();
	    stack_real_.pop_back();
	    return val;
      }
      inline void push_real(double val)
      {
	    stack_real_.push_back(val);
      }
      inline double peek_real(unsigned depth)
      {
	    assert(depth < stack_real_.size());
	    unsigned use_index = stack_real_.size()-1-depth;
	    return stack_real_[use_index];
      }
      inline void poke_real(unsigned depth, double val)
      {
	    assert(depth < stack_real_.size());
	    unsigned use_index = stack_real_.size()-1-depth;
	    stack_real_[use_index] = val;
      }
      inline void pop_real(unsigned cnt)
      {
	    while (cnt > 0) {
		  stack_real_.pop_back();
		  cnt -= 1;
	    }
      }

	/* Strings are operated on using a forth-like operator
	   set. Items at the top of the stack (back()) are the objects
	   operated on except for special cases. New objects are
	   pushed onto the top (back()) and pulled from the top
	   (back()) only. */
    private:
      vector<string> stack_str_;
    public:
      inline string pop_str(void)
      {
	    assert(! stack_str_.empty());
	    string val = stack_str_.back();
	    stack_str_.pop_back();
	    return val;
      }
      inline void push_str(const string&val)
      {
	    stack_str_.push_back(val);
      }
      inline string&peek_str(unsigned depth)
      {
	    assert(depth<stack_str_.size());
	    unsigned use_index = stack_str_.size()-1-depth;
	    return stack_str_[use_index];
      }
      inline void poke_str(unsigned depth, const string&val)
      {
	    assert(depth < stack_str_.size());
	    unsigned use_index = stack_str_.size()-1-depth;
	    stack_str_[use_index] = val;
      }
      inline void pop_str(unsigned cnt)
      {
	    while (cnt > 0) {
		  stack_str_.pop_back();
		  cnt -= 1;
	    }
      }

	/* Objects are also operated on in a stack. */
    private:
      enum { STACK_OBJ_MAX_SIZE = 32 };
      vvp_object_t stack_obj_[STACK_OBJ_MAX_SIZE];
      unsigned stack_obj_size_;
    public:
      inline vvp_object_t& peek_object(void)
      {
	    assert(stack_obj_size_ > 0);
	    return stack_obj_[stack_obj_size_-1];
      }
      inline vvp_object_t& peek_object(unsigned depth)
      {
	    assert(stack_obj_size_ > depth);
	    return stack_obj_[stack_obj_size_-1-depth];
      }
      inline void pop_object(vvp_object_t&obj)
      {
	    assert(stack_obj_size_ > 0);
	    stack_obj_size_ -= 1;
	    obj = stack_obj_[stack_obj_size_];
	    stack_obj_[stack_obj_size_].reset(0);
      }
      inline void pop_object(unsigned cnt, unsigned skip =0)
      {
	    assert((cnt+skip) <= stack_obj_size_);
	    for (size_t idx = stack_obj_size_-skip-cnt ; idx < stack_obj_size_-skip ; idx += 1)
		  stack_obj_[idx].reset(0);
	    stack_obj_size_ -= cnt;
	    for (size_t idx = stack_obj_size_-skip ; idx < stack_obj_size_ ; idx += 1)
		  stack_obj_[idx] = stack_obj_[idx+skip];
	    for (size_t idx = stack_obj_size_ ; idx < stack_obj_size_+skip ; idx += 1)
		  stack_obj_[idx].reset(0);
      }
      inline void push_object(const vvp_object_t&obj)
      {
	    assert(stack_obj_size_ < STACK_OBJ_MAX_SIZE);
	    stack_obj_[stack_obj_size_] = obj;
	    stack_obj_size_ += 1;
      }
      inline bool has_objects() const { return stack_obj_size_ > 0; }

	/* My parent sets this when it wants me to wake it up. */
      unsigned i_am_joining      :1;
      unsigned i_am_detached     :1;
      unsigned i_am_waiting      :1;
      unsigned i_am_in_function  :1; // True if running function code
      unsigned i_am_forked_task  :1; // True if created by fork (not call)
      unsigned i_have_ended      :1;
      unsigned i_was_disabled    :1;
      unsigned waiting_for_event :1;
      unsigned is_scheduled      :1;
      unsigned delay_delete      :1;
	/* This points to the children of the thread. */
      set<struct vthread_s*>children;
	/* This points to the detached children of the thread. */
      set<struct vthread_s*>detached_children;
	/* This points to my parent, if I have one. */
      struct vthread_s*parent;
	/* This points to the containing scope. */
      __vpiScope*parent_scope;
	/* This is used for keeping wait queues. */
      struct vthread_s*wait_next;
	/* These are used to access automatically allocated items. */
      vvp_context_t wt_context, rd_context;
	/* These are used to store '@' (implicit this) for forked tasks.
	 * When a forked task calls functions, context swaps change rd_context
	 * away from the fork context where '@' was stored. These members
	 * allow us to retrieve '@' regardless of context state. */
      vvp_object_t fork_this_obj_;
      vvp_net_t* fork_this_net_;
	/* These are used to pass non-blocking event control information. */
      vvp_net_t*event;
      uint64_t ecount;

	/* Inline constraint bounds for randomize() with { ... }
	 * These are pushed before %randomize and cleared after */
      std::vector<class_type::simple_bound_t> inline_constraints_;

      /* Array copy sources for foreach element equality constraints */
      std::map<unsigned, vvp_object_t> array_copy_sources_;

      void push_inline_constraint(const class_type::simple_bound_t& bound) {
	    inline_constraints_.push_back(bound);
      }
      void push_array_copy_source(unsigned prop_idx, const vvp_object_t& src) {
	    array_copy_sources_[prop_idx] = src;
      }
      void clear_inline_constraints() {
	    inline_constraints_.clear();
	    array_copy_sources_.clear();
      }
      const std::vector<class_type::simple_bound_t>& get_inline_constraints() const {
	    return inline_constraints_;
      }
      const std::map<unsigned, vvp_object_t>& get_array_copy_sources() const {
	    return array_copy_sources_;
      }

	/* Save the file/line information when available. */
    private:
      char *filenm_;
      unsigned lineno_;
    public:
      void set_fileline(char *filenm, unsigned lineno);
      string get_fileline();

      inline void cleanup()
      {
	    if (i_was_disabled) {
		  stack_vec4_.clear();
		  stack_real_.clear();
		  stack_str_.clear();
		  pop_object(stack_obj_size_);
	    }
	    free(filenm_);
	    filenm_ = 0;
	    assert(stack_vec4_.empty());
	    assert(stack_real_.empty());
	    assert(stack_str_.empty());
	    assert(stack_obj_size_ == 0);
      }
};

inline vthread_s::vthread_s()
{
      stack_obj_size_ = 0;
      filenm_ = 0;
      lineno_ = 0;
}

void vthread_s::set_fileline(char *filenm, unsigned lineno)
{
      assert(filenm);
      if (!filenm_ || (strcmp(filenm_, filenm) != 0)) {
	    free(filenm_);
	    filenm_ = strdup(filenm);
      }
      lineno_ = lineno;
}

inline string vthread_s::get_fileline()
{
      ostringstream buf;
      if (filenm_) {
	    buf << filenm_ << ":" << lineno_ << ": ";
      }
      string res = buf.str();
      return res;
}

void vthread_s::debug_dump(ostream&fd, const char*label)
{
      fd << "**** " << label << endl;
      fd << "**** ThreadId: " << this << ", parent id: " << parent << endl;

      fd << "**** Flags: ";
      for (int idx = 0 ; idx < FLAGS_COUNT ; idx += 1)
	    fd << flags[idx];
      fd << endl;
      fd << "**** vec4 stack..." << endl;
      for (size_t idx = stack_vec4_.size() ; idx > 0 ; idx -= 1)
	    fd << "    " << (stack_vec4_.size()-idx) << ": " << stack_vec4_[idx-1] << endl;
      fd << "**** str stack (" << stack_str_.size() << ")..." << endl;
      fd << "**** obj stack (" << stack_obj_size_ << ")..." << endl;
      fd << "**** args_vec4 array (" << args_vec4.size() << ")..." << endl;
      for (size_t idx = 0 ; idx < args_vec4.size() ; idx += 1)
	    fd << "    " << idx << ": " << args_vec4[idx] << endl;
      fd << "**** file/line (";
      if (filenm_) fd << filenm_;
      else fd << "<no file name>";
      fd << ":" << lineno_ << ")" << endl;
      fd << "**** Done ****" << endl;
}

/*
 * This function converts the text format of the string by interpreting
 * any octal characters (\nnn) to their single byte value. We do this here
 * because the text value in the vvp_code_t is stored as a C string. This
 * converts it to a C++ string that can hold binary values. We only have
 * to handle the octal escapes because the main compiler takes care of all
 * the other string special characters and normalizes the strings to use
 * only this format.
 */
static string filter_string(const char*text)
{
      vector<char> tmp (strlen(text)+1);
      size_t dst = 0;
      for (const char*ptr = text ; *ptr ; ptr += 1) {
	    // Not an escape? Move on.
	    if (*ptr != '\\') {
		  tmp[dst++] = *ptr;
		  continue;
	    }

	    // Now we know that *ptr is pointing to a \ character and we
	    // have an octal sequence coming up. Advance the ptr and start
	    // processing octal digits.
	    ptr += 1;
	    if (*ptr == 0)
		  break;

	    char byte = 0;
	    int cnt = 3;
	    while (*ptr && cnt > 0 && *ptr >= '0' && *ptr <= '7') {
		  byte *= 8;
		  byte += *ptr - '0';
		  cnt -= 1;
		  ptr += 1;
	    }

	    // null-bytes are supposed to be removed when assigning a string
	    // literal to a string.
	    if (byte != '\0')
		  tmp[dst++] = byte;

	    // After the while loop above, the ptr points to the next character,
	    // but the for-loop condition is assuming that ptr points to the last
	    // character, since it has the ptr+=1.
	    ptr -= 1;
      }

      // Put a nul byte at the end of the built up string, but really we are
      // using the known length in the string constructor.
      tmp[dst] = 0;
      string res (&tmp[0], dst);
      return res;
}

static void do_join(vthread_t thr, vthread_t child);

__vpiScope* vthread_scope(struct vthread_s*thr)
{
      return thr->parent_scope;
}

struct vthread_s*running_thread = 0;

string get_fileline()
{
      return running_thread->get_fileline();
}

void vthread_push(struct vthread_s*thr, double val)
{
      thr->push_real(val);
}

void vthread_push(struct vthread_s*thr, const string&val)
{
      thr->push_str(val);
}

void vthread_push(struct vthread_s*thr, const vvp_vector4_t&val)
{
      thr->push_vec4(val);
}

void vthread_pop_real(struct vthread_s*thr, unsigned depth)
{
      thr->pop_real(depth);
}

void vthread_pop_str(struct vthread_s*thr, unsigned depth)
{
      thr->pop_str(depth);
}

void vthread_pop_vec4(struct vthread_s*thr, unsigned depth)
{
      thr->pop_vec4(depth);
}

double vthread_get_real_stack(struct vthread_s*thr, unsigned depth)
{
      return thr->peek_real(depth);
}

const string&vthread_get_str_stack(struct vthread_s*thr, unsigned depth)
{
      return thr->peek_str(depth);
}

const vvp_vector4_t& vthread_get_vec4_stack(struct vthread_s*thr, unsigned depth)
{
      return thr->peek_vec4(depth);
}

unsigned vthread_get_vec4_stack_size(struct vthread_s*thr)
{
      return thr->vec4_stack_size();
}

/*
 * Some thread management functions
 */
/*
 * This is a function to get a vvp_queue handle from the variable
 * referenced by "net". If the queue is nil, then allocated it and
 * assign the value to the net. Note that this function is
 * parameterized by the queue type so that we can create the right
 * derived type of queue object.
 */
template <class VVP_QUEUE> static vvp_queue*get_queue_object(vthread_t thr, vvp_net_t*net)
{
      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    assert(obj->get_object().test_nil());
	    queue = new VVP_QUEUE;
	    vvp_object_t val (queue);
	    vvp_net_ptr_t ptr (net, 0);
	    vvp_send_object(ptr, val, thr->wt_context);
      }

      return queue;
}

/*
 * The following are used to allow a common template to be written for
 * queue real/string/vec4 operations
 */
inline static void pop_value(vthread_t thr, double&value, unsigned)
{
      value = thr->pop_real();
}

inline static void pop_value(vthread_t thr, string&value, unsigned)
{
      value = thr->pop_str();
}

inline static void pop_value(vthread_t thr, vvp_vector4_t&value, unsigned wid)
{
      value = thr->pop_vec4();
      assert(value.size() == wid);
}

inline static void pop_value(vthread_t thr, vvp_object_t&value, unsigned)
{
      thr->pop_object(value);
}

/*
 * The following are used to allow the queue templates to print correctly.
 */
inline static string get_queue_type(double&)
{
      return "queue<real>";
}

inline static string get_queue_type(string&)
{
      return "queue<string>";
}

inline static string get_queue_type(const vvp_vector4_t&value)
{
      ostringstream buf;
      buf << "queue<vector[" << value.size() << "]>";
      string res = buf.str();
      return res;
}

inline static void print_queue_value(double value)
{
      cerr << value;
}

inline static void print_queue_value(const string&value)
{
      cerr << "\"" << value << "\"";
}

inline static void print_queue_value(const vvp_vector4_t&value)
{
      cerr << value;
}

inline static string get_queue_type(const vvp_object_t&)
{
      return "queue<object>";
}

inline static void print_queue_value(const vvp_object_t&)
{
      cerr << "<object>";
}

/*
 * The following are used to get a darray/queue default value.
 */
inline static void dq_default(double&value, unsigned)
{
      value = 0.0;
}

inline static void dq_default(string&value, unsigned)
{
      value = "";
}

inline static void dq_default(vvp_vector4_t&value, unsigned wid)
{
      value = vvp_vector4_t(wid);
}

inline static void dq_default(vvp_object_t&value, unsigned)
{
      value = vvp_object_t();  // null object
}


template <class T> T coerce_to_width(const T&that, unsigned width)
{
      if (that.size() == width)
	    return that;

      assert(that.size() > width);
      T res (width);
      for (unsigned idx = 0 ;  idx < width ;  idx += 1)
	    res.set_bit(idx, that.value(idx));

      return res;
}

/* Explicitly define the vvp_vector4_t version of coerce_to_width(). */
template vvp_vector4_t coerce_to_width(const vvp_vector4_t&that,
                                       unsigned width);


static void multiply_array_imm(unsigned long*res, const unsigned long*val,
			       unsigned words, unsigned long imm)
{
      for (unsigned idx = 0 ; idx < words ; idx += 1)
	    res[idx] = 0;

      for (unsigned mul_idx = 0 ; mul_idx < words ; mul_idx += 1) {
	    unsigned long sum;
	    unsigned long tmp = multiply_with_carry(val[mul_idx], imm, sum);

	    unsigned long carry = 0;
	    res[mul_idx] = add_with_carry(res[mul_idx], tmp, carry);
	    for (unsigned add_idx = mul_idx+1 ; add_idx < words ; add_idx += 1) {
		  res[add_idx] = add_with_carry(res[add_idx], sum, carry);
		  sum = 0;
	    }
      }
}

/*
 * Allocate a context for use by a child thread. By preference, use
 * the last freed context. If none available, create a new one. Add
 * it to the list of live contexts in that scope.
 */
static vvp_context_t vthread_alloc_context(__vpiScope*scope)
{
      assert(scope->is_automatic());

      vvp_context_t context = scope->free_contexts;
      if (context) {
            scope->free_contexts = vvp_get_next_context(context);
            for (unsigned idx = 0 ; idx < scope->nitem ; idx += 1) {
                  scope->item[idx]->reset_instance(context);
            }
      } else {
            context = vvp_allocate_context(scope->nitem);
            for (unsigned idx = 0 ; idx < scope->nitem ; idx += 1) {
                  scope->item[idx]->alloc_instance(context);
            }
      }

      vvp_set_next_context(context, scope->live_contexts);
      scope->live_contexts = context;

      return context;
}

/*
 * Allocate a new context and copy values from an existing context.
 * This is used for fork/join_none where the forked thread needs its
 * own copy of the automatic variables.
 */
static vvp_context_t vthread_copy_context(__vpiScope*scope, vvp_context_t src)
{
      assert(scope->is_automatic());
      assert(src);

      // Allocate new context
      vvp_context_t dst = vvp_allocate_context(scope->nitem);

      // First allocate instances for all items in the new context
      for (unsigned idx = 0 ; idx < scope->nitem ; idx += 1) {
            scope->item[idx]->alloc_instance(dst);
      }

      // Then copy values from source to destination
      for (unsigned idx = 0 ; idx < scope->nitem ; idx += 1) {
            scope->item[idx]->copy_instance(dst, src);
      }

      // Add to live contexts list
      vvp_set_next_context(dst, scope->live_contexts);
      scope->live_contexts = dst;

      return dst;
}

/*
 * Free a context previously allocated to a child thread by pushing it
 * onto the freed context stack. Remove it from the list of live contexts
 * in that scope.
 */
static void vthread_free_context(vvp_context_t context, __vpiScope*scope)
{
      assert(scope->is_automatic());
      assert(context);

      if (context == scope->live_contexts) {
            scope->live_contexts = vvp_get_next_context(context);
      } else {
            vvp_context_t tmp = scope->live_contexts;
            while (context != vvp_get_next_context(tmp)) {
                  assert(tmp);
                  tmp = vvp_get_next_context(tmp);
            }
            vvp_set_next_context(tmp, vvp_get_next_context(context));
      }

      vvp_set_next_context(context, scope->free_contexts);
      scope->free_contexts = context;
}

#ifdef CHECK_WITH_VALGRIND
void contexts_delete(class __vpiScope*scope)
{
      vvp_context_t context = scope->free_contexts;

      while (context) {
	    scope->free_contexts = vvp_get_next_context(context);
	    for (unsigned idx = 0; idx < scope->nitem; idx += 1) {
		  scope->item[idx]->free_instance(context);
	    }
	    free(context);
	    context = scope->free_contexts;
      }
      free(scope->item);
}
#endif

/*
 * Create a new thread with the given start address.
 */
vthread_t vthread_new(vvp_code_t pc, __vpiScope*scope)
{
      vthread_t thr = new struct vthread_s;
      thr->pc     = pc;
	//thr->bits4  = vvp_vector4_t(32);
      thr->parent = 0;
      thr->parent_scope = scope;
      thr->wait_next = 0;
      thr->wt_context = 0;
      thr->rd_context = 0;
      thr->fork_this_net_ = 0;  // fork_this_obj_ is default-constructed as nil

      thr->i_am_joining  = 0;
      thr->i_am_detached = 0;
      thr->i_am_waiting  = 0;
      thr->i_am_in_function = 0;
      thr->i_am_forked_task = 0;
      thr->is_scheduled  = 0;
      thr->i_have_ended  = 0;
      thr->i_was_disabled = 0;
      thr->delay_delete  = 0;
      thr->waiting_for_event = 0;
      thr->event  = 0;
      thr->ecount = 0;

      thr->flags[0] = BIT4_0;
      thr->flags[1] = BIT4_1;
      thr->flags[2] = BIT4_X;
      thr->flags[3] = BIT4_Z;
      for (int idx = 4 ; idx < 8 ; idx += 1)
	    thr->flags[idx] = BIT4_X;

      scope->threads .insert(thr);
      return thr;
}

#ifdef CHECK_WITH_VALGRIND
#if 0
/*
 * These are not currently correct. If you use them you will get
 * double delete messages. There is still a leak related to a
 * waiting event that needs to be investigated.
 */

static void wait_next_delete(vthread_t base)
{
      while (base) {
	    vthread_t tmp = base->wait_next;
	    delete base;
	    base = tmp;
	    if (base->waiting_for_event == 0) break;
      }
}

static void child_delete(vthread_t base)
{
      while (base) {
	    vthread_t tmp = base->child;
	    delete base;
	    base = tmp;
      }
}
#endif

void vthreads_delete(class __vpiScope*scope)
{
      for (std::set<vthread_t>::iterator cur = scope->threads.begin()
		 ; cur != scope->threads.end() ; ++ cur ) {
	    delete *cur;
      }
      scope->threads.clear();
}
#endif

/*
 * Reaping pulls the thread out of the stack of threads. If I have a
 * child, then hand it over to my parent or fully detach it.
 */
static void vthread_reap(vthread_t thr)
{
      if (! thr->children.empty()) {
	    for (set<vthread_t>::iterator cur = thr->children.begin()
		       ; cur != thr->children.end() ; ++cur) {
		  vthread_t child = *cur;
		  assert(child);
		  assert(child->parent == thr);
		  child->parent = thr->parent;
	    }
      }
      if (! thr->detached_children.empty()) {
	    for (set<vthread_t>::iterator cur = thr->detached_children.begin()
		       ; cur != thr->detached_children.end() ; ++cur) {
		  vthread_t child = *cur;
		  assert(child);
		  assert(child->parent == thr);
		  assert(child->i_am_detached);
		  child->parent = 0;
		  child->i_am_detached = 0;
	    }
      }
      if (thr->parent) {
	      /* assert that the given element was removed. */
	    if (thr->i_am_detached) {
		  size_t res = thr->parent->detached_children.erase(thr);
		  assert(res == 1);
	    } else {
		  size_t res = thr->parent->children.erase(thr);
		  assert(res == 1);
	    }
      }

      thr->parent = 0;

	// Remove myself from the containing scope if needed.
      thr->parent_scope->threads.erase(thr);

      thr->pc = codespace_null();

	/* If this thread is not scheduled, then is it safe to delete
	   it now. Otherwise, let the schedule event (which will
	   execute the thread at of_ZOMBIE) delete the object. */
      if ((thr->is_scheduled == 0) && (thr->waiting_for_event == 0)) {
	    assert(thr->children.empty());
	    assert(thr->wait_next == 0);
	    if (thr->delay_delete)
		  schedule_del_thr(thr);
	    else
		  vthread_delete(thr);
      }
}

void vthread_delete(vthread_t thr)
{
      thr->cleanup();
      delete thr;
}

void vthread_mark_scheduled(vthread_t thr)
{
      while (thr != 0) {
	    assert(thr->is_scheduled == 0);
	    thr->is_scheduled = 1;
	    thr = thr->wait_next;
      }
}

void vthread_mark_final(vthread_t thr)
{
      /*
       * The behavior in a final thread is the same as in a function. Any
       * child thread will be executed immediately rather than being
       * scheduled.
       */
      while (thr != 0) {
	    thr->i_am_in_function = 1;
	    thr = thr->wait_next;
      }
}

void vthread_delay_delete()
{
      if (running_thread)
	    running_thread->delay_delete = 1;
}

/*
 * This function runs each thread by fetching an instruction,
 * incrementing the PC, and executing the instruction. The thread may
 * be the head of a list, so each thread is run so far as possible.
 */
void vthread_run(vthread_t thr)
{
      while (thr != 0) {
	    vthread_t tmp = thr->wait_next;
	    thr->wait_next = 0;

	    assert(thr->is_scheduled);
	    thr->is_scheduled = 0;

            running_thread = thr;

	    for (;;) {
		  vvp_code_t cp = thr->pc;
		  thr->pc += 1;

		    /* Run the opcode implementation. If the execution of
		       the opcode returns false, then the thread is meant to
		       be paused, so break out of the loop. */
		  bool rc = (cp->opcode)(thr, cp);
		  if (rc == false)
			break;
	    }

	    thr = tmp;
      }
      running_thread = 0;
}

/*
 * The CHUNK_LINK instruction is a special next pointer for linking
 * chunks of code space. It's like a simplified %jmp.
 */
bool of_CHUNK_LINK(vthread_t thr, vvp_code_t code)
{
      assert(code->cptr);
      thr->pc = code->cptr;
      return true;
}

/*
 * This is called by an event functor to wake up all the threads on
 * its list. I in fact created that list in the %wait instruction, and
 * I also am certain that the waiting_for_event flag is set.
 */
void vthread_schedule_list(vthread_t thr)
{
      for (vthread_t cur = thr ;  cur ;  cur = cur->wait_next) {
	    assert(cur->waiting_for_event);
	    cur->waiting_for_event = 0;
      }

      schedule_vthread(thr, 0);
}

vvp_context_t vthread_get_wt_context()
{
      if (running_thread)
            return running_thread->wt_context;
      else
            return 0;
}

vvp_context_t vthread_get_rd_context()
{
      if (running_thread)
            return running_thread->rd_context;
      else
            return 0;
}

vvp_context_item_t vthread_get_wt_context_item(unsigned context_idx)
{
      assert(running_thread && running_thread->wt_context);
      return vvp_get_context_item(running_thread->wt_context, context_idx);
}

vvp_context_item_t vthread_get_rd_context_item(unsigned context_idx)
{
      assert(running_thread && running_thread->rd_context);
      return vvp_get_context_item(running_thread->rd_context, context_idx);
}

/*
 * %abs/wr
 */
bool of_ABS_WR(vthread_t thr, vvp_code_t)
{
      thr->push_real( fabs(thr->pop_real()) );
      return true;
}

bool of_ALLOC(vthread_t thr, vvp_code_t cp)
{
        /* Allocate a context. */
      vvp_context_t child_context = vthread_alloc_context(cp->scope);

        /* Push the allocated context onto the write context stack. */
      vvp_set_stacked_context(child_context, thr->wt_context);

      thr->wt_context = child_context;

      return true;
}

bool of_AND(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t&vala = thr->peek_vec4();
      assert(vala.size() == valb.size());
      vala &= valb;
      return true;
}

/*
 * This function must ALWAYS be called with the val set to the right
 * size, and initialized with BIT4_0 bits. Certain optimizations rely
 * on that.
 */
static void get_immediate_rval(vvp_code_t cp, vvp_vector4_t&val)
{
      uint32_t vala = cp->bit_idx[0];
      uint32_t valb = cp->bit_idx[1];
      unsigned wid  = cp->number;

      if (valb == 0) {
	      // Special case: if the value is zero, we are done
	      // before we start.
	    if (vala == 0) return;

	      // Special case: The value has no X/Z bits, so we can
	      // use the setarray method to write the value all at once.
	    unsigned use_wid = 8*sizeof(unsigned long);
	    if (wid < use_wid)
		  use_wid = wid;
	    unsigned long tmp[1];
	    tmp[0] = vala;
	    val.setarray(0, use_wid, tmp);
	    return;
      }

	// The immediate value can be values bigger then 32 bits, but
	// only if the high bits are zero. So at most we need to run
	// through the loop below 32 times. Maybe less, if the target
	// width is less. We don't have to do anything special on that
	// because vala/valb bits will shift away so (vala|valb) will
	// turn to zero at or before 32 shifts.

      for (unsigned idx = 0 ; idx < wid && (vala|valb) ; idx += 1) {
	    uint32_t ba = 0;
	      // Convert the vala/valb bits to a ba number that
	      // matches the encoding of the vvp_bit4_t enumeration.
	    ba = (valb & 1) << 1;
	    ba |= vala & 1;

	      // Note that the val is already pre-filled with BIT4_0
	      // bits, os we only need to set non-zero bit values.
	    if (ba) val.set_bit(idx, (vvp_bit4_t)ba);

	    vala >>= 1;
	    valb >>= 1;
      }
}

/*
 * %add
 *
 * Pop r,
 * Pop l,
 * Push l+r
 *
 * Pop 2 and push 1 is the same as pop 1 and replace the remaining top
 * of the stack with a new value. That is what we will do.
 */
bool of_ADD(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t r = thr->pop_vec4();
	// Rather then pop l, use it directly from the stack. When we
	// assign to 'l', that will edit the top of the stack, which
	// replaces a pop and a pull.
      vvp_vector4_t&l = thr->peek_vec4();

      l.add(r);

      return true;
}

/*
 * %addi <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments, and push
 * the result.
 */
bool of_ADDI(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      vvp_vector4_t&l = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t r (wid, BIT4_0);
      get_immediate_rval (cp, r);

      l.add(r);

      return true;
}

/*
 * %add/wr
 */
bool of_ADD_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(l + r);
      return true;
}

/* %assign/ar <array>, <delay>
 * Generate an assignment event to a real array. Index register 3
 * contains the canonical address of the word in the memory. <delay>
 * is the delay in simulation time. <bit> is the index register
 * containing the real value.
 */
bool of_ASSIGN_AR(vthread_t thr, vvp_code_t cp)
{
      long adr = thr->words[3].w_int;
      unsigned delay = cp->bit_idx[0];
      double value = thr->pop_real();

      if (adr >= 0) {
	    schedule_assign_array_word(cp->array, adr, value, delay);
      }

      return true;
}

/* %assign/ar/d <array>, <delay_idx>
 * Generate an assignment event to a real array. Index register 3
 * contains the canonical address of the word in the memory.
 * <delay_idx> is the integer register that contains the delay value.
 */
bool of_ASSIGN_ARD(vthread_t thr, vvp_code_t cp)
{
      long adr = thr->words[3].w_int;
      double value = thr->pop_real();

      if (adr >= 0) {
	    vvp_time64_t delay = thr->words[cp->bit_idx[0]].w_uint;
	    schedule_assign_array_word(cp->array, adr, value, delay);
      }

      return true;
}

/* %assign/ar/e <array>
 * Generate an assignment event to a real array. Index register 3
 * contains the canonical address of the word in the memory. <bit>
 * is the index register containing the real value. The event
 * information is contained in the thread event control registers
 * and is set with %evctl.
 */
bool of_ASSIGN_ARE(vthread_t thr, vvp_code_t cp)
{
      long adr = thr->words[3].w_int;
      double value = thr->pop_real();

      if (adr >= 0) {
	    if (thr->ecount == 0) {
		  schedule_assign_array_word(cp->array, adr, value, 0);
	    } else {
		  schedule_evctl(cp->array, adr, value, thr->event,
		                 thr->ecount);
	    }
      }

      return true;
}

/*
 * %assign/vec4 <var>, <delay>
 */
bool of_ASSIGN_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      unsigned delay = cp->bit_idx[0];
      const vvp_vector4_t&val = thr->peek_vec4();

      schedule_assign_vector(ptr, 0, 0, val, delay);
      thr->pop_vec4(1);
      return true;
}

/*
 * Resizes a vector value for a partial assignment so that the value is fully
 * in-bounds of the target signal. Both `val` and `off` will be updated if
 * necessary.
 *
 * Returns false if the value is fully out-of-bounds and the assignment should
 * be skipped. Otherwise returns true.
 */
static bool resize_rval_vec(vvp_vector4_t &val, int64_t &off,
			    unsigned int sig_wid)
{
      unsigned int wid = val.size();

        // Fully in bounds, most likely case
      if (off >= 0 && (uint64_t)off + wid <= sig_wid)
	    return true;

      unsigned int base = 0;
      if (off >= 0) {
	      // Fully out-of-bounds
	    if ((uint64_t)off >= sig_wid)
		  return false;
      } else {
	      // Fully out-of-bounds */
	    if ((uint64_t)(-off) >= wid)
		  return false;

	      // If the index is below the vector, then only assign the high
	      // bits that overlap with the target
	    base = -off;
	    wid += off;
		off = 0;
      }

	// If the value is partly above the target, then only assign
	// the bits that overlap
      if ((uint64_t)off + wid > sig_wid)
	    wid = sig_wid - (uint64_t)off;

      val = val.subvalue(base, wid);

      return true;
}

/*
 * %assign/vec4/a/d <arr>, <offx>, <delx>
 */
bool of_ASSIGN_VEC4_A_D(vthread_t thr, vvp_code_t cp)
{
      int off_idx = cp->bit_idx[0];
      int del_idx = cp->bit_idx[1];
      int adr_idx = 3;

      int64_t  off = off_idx ? thr->words[off_idx].w_int : 0;
      vvp_time64_t del = del_idx? thr->words[del_idx].w_uint : 0;
      long     adr = thr->words[adr_idx].w_int;

      vvp_vector4_t val = thr->pop_vec4();

	// Abort if flags[4] is set. This can happen if the calculation
	// into an index register failed.
      if (thr->flags[4] == BIT4_1)
	    return true;

      if (!resize_rval_vec(val, off, cp->array->get_word_size()))
	    return true;

      schedule_assign_array_word(cp->array, adr, off, val, del);

      return true;
}

/*
 * %assign/vec4/a/e <arr>, <offx>
 */
bool of_ASSIGN_VEC4_A_E(vthread_t thr, vvp_code_t cp)
{
      int off_idx = cp->bit_idx[0];
      int adr_idx = 3;

      int64_t  off = off_idx ? thr->words[off_idx].w_int : 0;
      long     adr = thr->words[adr_idx].w_int;

      vvp_vector4_t val = thr->pop_vec4();

	// Abort if flags[4] is set. This can happen if the calculation
	// into an index register failed.
      if (thr->flags[4] == BIT4_1)
	    return true;

      if (!resize_rval_vec(val, off, cp->array->get_word_size()))
	    return true;

      if (thr->ecount == 0) {
	    schedule_assign_array_word(cp->array, adr, off, val, 0);
      } else {
	    schedule_evctl(cp->array, adr, val, off, thr->event, thr->ecount);
      }

      return true;
}

/*
 * %assign/vec4/off/d <var>, <off>, <del>
 */
bool of_ASSIGN_VEC4_OFF_D(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      unsigned off_index = cp->bit_idx[0];
      unsigned del_index = cp->bit_idx[1];
      vvp_vector4_t val = thr->pop_vec4();

      int64_t off = thr->words[off_index].w_int;
      vvp_time64_t del = thr->words[del_index].w_uint;

	// Abort if flags[4] is set. This can happen if the calculation
	// into an index register failed.
      if (thr->flags[4] == BIT4_1)
	    return true;

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (cp->net->fil);
      assert(sig);

      if (!resize_rval_vec(val, off, sig->value_size()))
	    return true;

      schedule_assign_vector(ptr, off, sig->value_size(), val, del);
      return true;
}

/*
 * %assign/vec4/off/e <var>, <off>
 */
bool of_ASSIGN_VEC4_OFF_E(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      unsigned off_index = cp->bit_idx[0];
      vvp_vector4_t val = thr->pop_vec4();

      int64_t off = thr->words[off_index].w_int;

	// Abort if flags[4] is set. This can happen if the calculation
	// into an index register failed.
      if (thr->flags[4] == BIT4_1)
	    return true;

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (cp->net->fil);
      assert(sig);

      if (!resize_rval_vec(val, off, sig->value_size()))
	    return true;

      if (thr->ecount == 0) {
	    schedule_assign_vector(ptr, off, sig->value_size(), val, 0);
      } else {
	    schedule_evctl(ptr, val, off, sig->value_size(), thr->event, thr->ecount);
      }

      return true;
}

/*
 * %assign/vec4/d <var-label> <delay>
 */
bool of_ASSIGN_VEC4D(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      unsigned del_index = cp->bit_idx[0];
      vvp_time64_t del = thr->words[del_index].w_int;

      vvp_vector4_t value = thr->pop_vec4();

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (cp->net->fil);
      assert(sig);

      schedule_assign_vector(ptr, 0, sig->value_size(), value, del);

      return true;
}

/*
 * %assign/vec4/e <var-label>
 */
bool of_ASSIGN_VEC4E(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      vvp_vector4_t value = thr->pop_vec4();

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (cp->net->fil);
      assert(sig);

      if (thr->ecount == 0) {
	    schedule_assign_vector(ptr, 0, sig->value_size(), value, 0);
      } else {
	    schedule_evctl(ptr, value, 0, sig->value_size(), thr->event, thr->ecount);
      }

      return true;
}

/*
 * This is %assign/wr <vpi-label>, <delay>
 *
 * This assigns (after a delay) a value to a real variable. Use the
 * vpi_put_value function to do the assign, with the delay written
 * into the vpiInertialDelay carrying the desired delay.
 */
bool of_ASSIGN_WR(vthread_t thr, vvp_code_t cp)
{
      unsigned delay = cp->bit_idx[0];
      double value = thr->pop_real();
      s_vpi_time del;

      del.type = vpiSimTime;
      vpip_time_to_timestruct(&del, delay);

      __vpiHandle*tmp = cp->handle;

      t_vpi_value val;
      val.format = vpiRealVal;
      val.value.real = value;
      vpi_put_value(tmp, &val, &del, vpiTransportDelay);

      return true;
}

bool of_ASSIGN_WRD(vthread_t thr, vvp_code_t cp)
{
      vvp_time64_t delay = thr->words[cp->bit_idx[0]].w_uint;
      double value = thr->pop_real();
      s_vpi_time del;

      del.type = vpiSimTime;
      vpip_time_to_timestruct(&del, delay);

      __vpiHandle*tmp = cp->handle;

      t_vpi_value val;
      val.format = vpiRealVal;
      val.value.real = value;
      vpi_put_value(tmp, &val, &del, vpiTransportDelay);

      return true;
}

bool of_ASSIGN_WRE(vthread_t thr, vvp_code_t cp)
{
      assert(thr->event != 0);
      double value = thr->pop_real();
      __vpiHandle*tmp = cp->handle;

	// If the count is zero then just put the value.
      if (thr->ecount == 0) {
	    t_vpi_value val;

	    val.format = vpiRealVal;
	    val.value.real = value;
	    vpi_put_value(tmp, &val, 0, vpiNoDelay);
      } else {
	    schedule_evctl(tmp, value, thr->event, thr->ecount);
      }

      thr->event = 0;
      thr->ecount = 0;

      return true;
}

bool of_BLEND(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t vala = thr->pop_vec4();
      vvp_vector4_t valb = thr->pop_vec4();
      assert(vala.size() == valb.size());

      for (unsigned idx = 0 ; idx < vala.size() ; idx += 1) {
	    if (vala.value(idx) == valb.value(idx))
		  continue;

	    vala.set_bit(idx, BIT4_X);
      }

      thr->push_vec4(vala);
      return true;
}

bool of_BLEND_WR(vthread_t thr, vvp_code_t)
{
      double f = thr->pop_real();
      double t = thr->pop_real();
      thr->push_real((t == f) ? t : 0.0);
      return true;
}

bool of_BREAKPOINT(vthread_t, vvp_code_t)
{
      return true;
}

/*
 * %callf/void <code-label>, <scope-label>
 * Combine the %fork and %join steps for invoking a function.
 */
static bool do_callf_void(vthread_t thr, vthread_t child)
{

      if (child->parent_scope->is_automatic()) {
	      /* The context allocated for this child is the top entry
		 on the write context stack */
	    child->wt_context = thr->wt_context;
	    child->rd_context = thr->wt_context;
      }

      // Propagate fork_this from parent if parent has it set.
      // This allows functions called by forked tasks to access '@'.
      // Note: We don't set i_am_forked_task - that's only for actual forks.
      if (thr->fork_this_net_ != 0) {
	    child->fork_this_net_ = thr->fork_this_net_;
	    // If parent's fork_this_obj_ is valid, use it.
	    // Otherwise, try to read '@' from the current write context.
	    if (!thr->fork_this_obj_.test_nil()) {
		  child->fork_this_obj_ = thr->fork_this_obj_;
	    } else if (thr->wt_context) {
		  // Try to read '@' from context
		  vvp_fun_signal_object_aa*fun_aa =
			dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
		  if (fun_aa) {
			child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
		  }
	    }
      }

        // Mark the function thread as a direct child of the current thread.
      child->parent = thr;
      thr->children.insert(child);
        // This should be the only child
      assert(thr->children.size()==1);

        // Execute the function. This SHOULD run the function to completion,
        // but there are some exceptional situations where it won't.
      assert(child->parent_scope->get_type_code() == vpiFunction);
      child->is_scheduled = 1;
      child->i_am_in_function = 1;
      vthread_run(child);
      running_thread = thr;

      if (child->i_have_ended) {
	    do_join(thr, child);
	    return true;
      } else {
	    thr->i_am_joining = 1;
	    return false;
      }
}

bool of_CALLF_OBJ(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);
      return do_callf_void(thr, child);

      // XXXX NOT IMPLEMENTED
}

bool of_CALLF_REAL(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);

	// This is the return value. Push a place-holder value. The function
	// will replace this with the actual value using a %ret/real instruction.
      thr->push_real(0.0);
      child->args_real.push_back(0);

      return do_callf_void(thr, child);
}

bool of_CALLF_STR(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);

      thr->push_str("");
      child->args_str.push_back(0);

      return do_callf_void(thr, child);
}

bool of_CALLF_VEC4(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);

      vpiScopeFunction*scope_func = dynamic_cast<vpiScopeFunction*>(cp->scope);
      assert(scope_func);

	// This is the return value. Push a place-holder value. The function
	// will replace this with the actual value using a %ret/real instruction.
      thr->push_vec4(vvp_vector4_t(scope_func->get_func_width(), scope_func->get_func_init_val()));
      child->args_vec4.push_back(0);

      return do_callf_void(thr, child);
}

bool of_CALLF_VOID(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);
      return do_callf_void(thr, child);
}

/*
 * %callf/virt/void <method_name>, <base_code>, <base_scope>
 * Virtual method call: look up the method in the object's actual class type
 * and call that method. The object is retrieved from the '@' (this) variable
 * in the base_scope that was allocated for the call.
 */
bool of_CALLF_VIRT_VOID(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      // Get the method name from the scope's basename
      const char*method_name = base_scope->scope_name();

      // Find the '@' (this) variable in the base scope and get the object from it
      vvp_object_t obj;
      bool found_this = false;

      // Get the write context - this is where the '@' parameter was stored
      vvp_context_t wt_ctx = vthread_get_wt_context();

      for (unsigned idx = 0; idx < base_scope->intern.size(); ++idx) {
	    vpiHandle item = base_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  // Check if this is the '@' variable (implicit 'this' parameter)
		  const char* name = item->vpi_get_str(vpiName);
		  if (name && strcmp(name, "@") == 0) {
			// Found the 'this' variable - get its value from write context
			__vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t*net = var->get_net();
			      if (net && net->fun) {
				    // Try to get from automatic variable (uses write context)
				    vvp_fun_signal_object_aa*fun_aa =
					  dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
				    if (fun_aa && wt_ctx) {
					  obj = fun_aa->get_object_from_context(wt_ctx);
					  found_this = true;
				    } else {
					  // Fall back to static variable (uses internal storage)
					  vvp_fun_signal_object*fun =
						dynamic_cast<vvp_fun_signal_object*>(net->fun);
					  if (fun) {
						obj = fun->get_object();
						found_this = true;
					  }
				    }
			      }
			}
			break;
		  }
	    }
      }

      // If we couldn't find 'this', fall back to base class call
      if (!found_this || obj.test_nil()) {
	    vthread_t child = vthread_new(cp->cptr2, base_scope);
	    return do_callf_void(thr, child);
      }

      // Get the cobject to access the class type
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (cobj == 0) {
	    // Not a class object - use base class method
	    vthread_t child = vthread_new(cp->cptr2, base_scope);
	    return do_callf_void(thr, child);
      }

      // Get the actual class type from the object
      const class_type*actual_class = cobj->get_class_type();
      if (actual_class == 0) {
	    // No class type - use base class method
	    vthread_t child = vthread_new(cp->cptr2, base_scope);
	    return do_callf_void(thr, child);
      }

      // Look up the method in the actual class type's method table
      const class_type::method_info*method = actual_class->get_method(method_name);
      if (method == 0 || method->entry == 0) {
	    // Method not found in derived class - use base class
	    vthread_t child = vthread_new(cp->cptr2, base_scope);
	    return do_callf_void(thr, child);
      }

      // Call the method found in the actual class
      vthread_t child = vthread_new(method->entry, method->scope);

      // If virtual dispatch changed the scope, handle context specially
      if (method->scope != base_scope && method->scope->is_automatic()) {
	    // Allocate new context for the virtual dispatch target scope
	    vvp_context_t new_context = vthread_alloc_context(method->scope);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    // Copy all matching class object parameters from base scope to target scope
	    __vpiScope*target_scope = method->scope;
	    bool found_at = false;
	    for (unsigned base_idx = 0; base_idx < base_scope->intern.size(); ++base_idx) {
		  vpiHandle base_item = base_scope->intern[base_idx];
		  if (!base_item) continue;
		  if (base_item->get_type_code() != vpiClassVar) continue;
		  const char* base_name_tmp = base_item->vpi_get_str(vpiName);
		  if (!base_name_tmp) continue;
		  // Copy base_name to avoid buffer reuse by subsequent vpi_get_str calls
		  std::string base_name_str(base_name_tmp);
		  const char* base_name = base_name_str.c_str();

		  __vpiBaseVar*base_var = dynamic_cast<__vpiBaseVar*>(base_item);
		  if (!base_var) continue;
		  vvp_net_t*base_net = base_var->get_net();
		  if (!base_net || !base_net->fun) continue;
		  vvp_fun_signal_object_aa*base_fun =
			dynamic_cast<vvp_fun_signal_object_aa*>(base_net->fun);
		  if (!base_fun) continue;

		  // Get value from base context (current wt_context)
		  vvp_object_t val = base_fun->get_object_from_context(wt_ctx);

		  // Track if we found @
		  if (strcmp(base_name, "@") == 0) {
			found_at = true;
		  }

		  if (val.test_nil()) continue;

		  // Find matching variable in target scope
		  for (unsigned tgt_idx = 0; tgt_idx < target_scope->intern.size(); ++tgt_idx) {
			vpiHandle tgt_item = target_scope->intern[tgt_idx];
			if (!tgt_item) continue;
			if (tgt_item->get_type_code() != vpiClassVar) continue;
			const char* tgt_name = tgt_item->vpi_get_str(vpiName);
			if (!tgt_name || strcmp(base_name, tgt_name) != 0) continue;

			__vpiBaseVar*tgt_var = dynamic_cast<__vpiBaseVar*>(tgt_item);
			if (!tgt_var) continue;
			vvp_net_t*tgt_net = tgt_var->get_net();
			if (!tgt_net || !tgt_net->fun) continue;
			vvp_fun_signal_object_aa*tgt_fun =
			      dynamic_cast<vvp_fun_signal_object_aa*>(tgt_net->fun);
			if (!tgt_fun) continue;

			// Copy value to target context
			tgt_fun->set_object_in_context(new_context, val);
			break;
		  }
	    }

	    // Warning suppressed - @ not found is expected for some methods

	    // Propagate fork_this from parent if parent has it set
	    if (thr->fork_this_net_ != 0) {
		  child->fork_this_net_ = thr->fork_this_net_;
		  if (!thr->fork_this_obj_.test_nil()) {
			child->fork_this_obj_ = thr->fork_this_obj_;
		  } else if (thr->wt_context) {
			vvp_fun_signal_object_aa*fun_aa =
			      dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
			if (fun_aa) {
			      child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
			}
		  }
	    }

	    // Inline the rest of do_callf_void (with context already set)
	    child->parent = thr;
	    thr->children.insert(child);
	    assert(thr->children.size()==1);
	    // Virtual dispatch can call either functions or tasks
	    assert(child->parent_scope->get_type_code() == vpiFunction ||
	           child->parent_scope->get_type_code() == vpiTask);
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;

	    if (child->i_have_ended) {
		  do_join(thr, child);
		  return true;
	    } else {
		  thr->i_am_joining = 1;
		  return false;
	    }
      }

      return do_callf_void(thr, child);
}

/*
 * Helper function to copy scope parameters from base scope to derived scope.
 * This is needed when virtual dispatch redirects to a derived class's method,
 * because the code generator stores parameters to the base class's scope variables
 * before the virtual call instruction. The derived class's scope has its own
 * variables that need to be initialized.
 *
 * base_context is the context where parameters were stored (for base scope)
 * derived_context is the newly allocated context for the derived scope
 */
static void copy_scope_parameters(__vpiScope*base_scope, __vpiScope*derived_scope,
				  vvp_context_t base_context, vvp_context_t derived_context)
{
      // Don't do anything if scopes are the same
      if (base_scope == derived_scope)
	    return;

      // Build a map of base scope variable names to their nets
      std::map<std::string, vvp_net_t*> base_vars;
      for (unsigned idx = 0; idx < base_scope->intern.size(); ++idx) {
	    vpiHandle item = base_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name_tmp = item->vpi_get_str(vpiName);
		  if (name_tmp) {
			// Copy name to avoid buffer reuse by subsequent vpi_get_str calls
			std::string name(name_tmp);
			__vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t*net = var->get_net();
			      if (net)
				    base_vars[name] = net;
			}
		  }
	    }
      }

      // Copy values to matching variables in derived scope
      for (unsigned idx = 0; idx < derived_scope->intern.size(); ++idx) {
	    vpiHandle item = derived_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name_tmp = item->vpi_get_str(vpiName);
		  if (name_tmp) {
			std::string name(name_tmp);
			auto it = base_vars.find(name);
			if (it != base_vars.end()) {
			      // Found matching variable - copy the object value
			      __vpiBaseVar*derived_var = dynamic_cast<__vpiBaseVar*>(item);
			      if (derived_var) {
				    vvp_net_t*base_net = it->second;
				    vvp_net_t*derived_net = derived_var->get_net();
				    if (base_net && base_net->fun && derived_net && derived_net->fun) {
					  // Handle context-aware (automatic) variables
					  vvp_fun_signal_object_aa*base_fun_aa =
						dynamic_cast<vvp_fun_signal_object_aa*>(base_net->fun);
					  vvp_fun_signal_object_aa*derived_fun_aa =
						dynamic_cast<vvp_fun_signal_object_aa*>(derived_net->fun);
					  if (base_fun_aa && derived_fun_aa && base_context && derived_context) {
						vvp_object_t obj = base_fun_aa->get_object_from_context(base_context);
						if (!obj.test_nil()) {
						      derived_fun_aa->set_object_in_context(derived_context, obj);
						}
					  } else {
						// Handle non-automatic variables
						vvp_fun_signal_object*base_fun =
						      dynamic_cast<vvp_fun_signal_object*>(base_net->fun);
						vvp_fun_signal_object*derived_fun =
						      dynamic_cast<vvp_fun_signal_object*>(derived_net->fun);
						if (base_fun && derived_fun) {
						      vvp_object_t obj = base_fun->get_object();
						      if (!obj.test_nil()) {
							    vvp_net_ptr_t ptr(derived_net, 0);
							    vvp_send_object(ptr, obj, derived_context);
						      }
						}
					  }
				    }
			      }
			}
		  }
	    }
      }
}

/*
 * Helper function for virtual method dispatch. Finds the '@' (this) variable,
 * gets the actual class type, and looks up the method. Returns the method info
 * or nullptr if virtual dispatch should fall back to base class call.
 */
static const class_type::method_info* resolve_virtual_method(vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      const char*method_name = base_scope->scope_name();

      vvp_object_t obj;
      bool found_this = false;
      vvp_context_t wt_ctx = vthread_get_wt_context();

      for (unsigned idx = 0; idx < base_scope->intern.size(); ++idx) {
	    vpiHandle item = base_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name = item->vpi_get_str(vpiName);
		  if (name && strcmp(name, "@") == 0) {
			__vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t*net = var->get_net();
			      if (net && net->fun) {
				    vvp_fun_signal_object_aa*fun_aa =
					  dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
				    if (fun_aa && wt_ctx) {
					  obj = fun_aa->get_object_from_context(wt_ctx);
					  found_this = true;
				    } else {
					  vvp_fun_signal_object*fun =
						dynamic_cast<vvp_fun_signal_object*>(net->fun);
					  if (fun) {
						obj = fun->get_object();
						found_this = true;
					  }
				    }
			      }
			}
			break;
		  }
	    }
      }

      if (!found_this || obj.test_nil())
	    return nullptr;

      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (cobj == 0)
	    return nullptr;

      const class_type*actual_class = cobj->get_class_type();
      if (actual_class == 0)
	    return nullptr;

      const class_type::method_info*method = actual_class->get_method(method_name);
      if (method == 0 || method->entry == 0)
	    return nullptr;

      return method;
}

bool of_CALLF_VIRT_VEC4(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      const class_type::method_info*method = resolve_virtual_method(cp);
      vvp_code_t entry;
      __vpiScope*scope;
      if (method) {
	    entry = method->entry;
	    scope = method->scope;
      } else {
	    entry = cp->cptr2;
	    scope = base_scope;
      }

      vthread_t child = vthread_new(entry, scope);

      vpiScopeFunction*scope_func = dynamic_cast<vpiScopeFunction*>(scope);
      assert(scope_func);

      thr->push_vec4(vvp_vector4_t(scope_func->get_func_width(), scope_func->get_func_init_val()));
      child->args_vec4.push_back(0);

      // When virtual dispatch changes the scope, we need to allocate a new context
      // for the derived scope and copy parameters from base context to it
      if (method && scope != base_scope && scope->is_automatic()) {
	    vvp_context_t new_context = vthread_alloc_context(scope);
	    copy_scope_parameters(base_scope, scope, thr->wt_context, new_context);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    // Propagate fork_this from parent if parent has it set
	    if (thr->fork_this_net_ != 0) {
		  child->fork_this_net_ = thr->fork_this_net_;
		  if (!thr->fork_this_obj_.test_nil()) {
			child->fork_this_obj_ = thr->fork_this_obj_;
		  } else if (thr->wt_context) {
			vvp_fun_signal_object_aa*fun_aa =
			      dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
			if (fun_aa) {
			      child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
			}
		  }
	    }

	    // Inline call execution (context already set)
	    child->parent = thr;
	    thr->children.insert(child);
	    assert(thr->children.size()==1);
	    assert(child->parent_scope->get_type_code() == vpiFunction);
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;

	    if (child->i_have_ended) {
		  do_join(thr, child);
		  return true;
	    } else {
		  thr->i_am_joining = 1;
		  return false;
	    }
      }

      return do_callf_void(thr, child);
}

bool of_CALLF_VIRT_REAL(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      const class_type::method_info*method = resolve_virtual_method(cp);
      vvp_code_t entry;
      __vpiScope*scope;
      if (method) {
	    entry = method->entry;
	    scope = method->scope;
      } else {
	    entry = cp->cptr2;
	    scope = base_scope;
      }

      vthread_t child = vthread_new(entry, scope);

      thr->push_real(0.0);
      child->args_real.push_back(0);

      // When virtual dispatch changes the scope, allocate new context and copy params
      if (method && scope != base_scope && scope->is_automatic()) {
	    vvp_context_t new_context = vthread_alloc_context(scope);
	    copy_scope_parameters(base_scope, scope, thr->wt_context, new_context);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    if (thr->fork_this_net_ != 0) {
		  child->fork_this_net_ = thr->fork_this_net_;
		  if (!thr->fork_this_obj_.test_nil()) {
			child->fork_this_obj_ = thr->fork_this_obj_;
		  } else if (thr->wt_context) {
			vvp_fun_signal_object_aa*fun_aa =
			      dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
			if (fun_aa) {
			      child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
			}
		  }
	    }

	    child->parent = thr;
	    thr->children.insert(child);
	    assert(thr->children.size()==1);
	    assert(child->parent_scope->get_type_code() == vpiFunction);
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;

	    if (child->i_have_ended) {
		  do_join(thr, child);
		  return true;
	    } else {
		  thr->i_am_joining = 1;
		  return false;
	    }
      }

      return do_callf_void(thr, child);
}

bool of_CALLF_VIRT_STR(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      const class_type::method_info*method = resolve_virtual_method(cp);
      vvp_code_t entry;
      __vpiScope*scope;
      if (method) {
	    entry = method->entry;
	    scope = method->scope;
      } else {
	    entry = cp->cptr2;
	    scope = base_scope;
      }

      vthread_t child = vthread_new(entry, scope);

      thr->push_str("");
      child->args_str.push_back(0);

      // When virtual dispatch changes the scope, allocate new context and copy params
      if (method && scope != base_scope && scope->is_automatic()) {
	    vvp_context_t new_context = vthread_alloc_context(scope);
	    copy_scope_parameters(base_scope, scope, thr->wt_context, new_context);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    if (thr->fork_this_net_ != 0) {
		  child->fork_this_net_ = thr->fork_this_net_;
		  if (!thr->fork_this_obj_.test_nil()) {
			child->fork_this_obj_ = thr->fork_this_obj_;
		  } else if (thr->wt_context) {
			vvp_fun_signal_object_aa*fun_aa =
			      dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
			if (fun_aa) {
			      child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
			}
		  }
	    }

	    child->parent = thr;
	    thr->children.insert(child);
	    assert(thr->children.size()==1);
	    assert(child->parent_scope->get_type_code() == vpiFunction);
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;

	    if (child->i_have_ended) {
		  do_join(thr, child);
		  return true;
	    } else {
		  thr->i_am_joining = 1;
		  return false;
	    }
      }

      return do_callf_void(thr, child);
}

bool of_CALLF_VIRT_OBJ(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      const class_type::method_info*method = resolve_virtual_method(cp);
      vvp_code_t entry;
      __vpiScope*scope;
      if (method) {
	    entry = method->entry;
	    scope = method->scope;
      } else {
	    entry = cp->cptr2;
	    scope = base_scope;
      }

      vthread_t child = vthread_new(entry, scope);

      // When virtual dispatch changes the scope, allocate new context and copy params
      if (method && scope != base_scope && scope->is_automatic()) {
	    vvp_context_t new_context = vthread_alloc_context(scope);
	    copy_scope_parameters(base_scope, scope, thr->wt_context, new_context);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    if (thr->fork_this_net_ != 0) {
		  child->fork_this_net_ = thr->fork_this_net_;
		  if (!thr->fork_this_obj_.test_nil()) {
			child->fork_this_obj_ = thr->fork_this_obj_;
		  } else if (thr->wt_context) {
			vvp_fun_signal_object_aa*fun_aa =
			      dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
			if (fun_aa) {
			      child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
			}
		  }
	    }

	    child->parent = thr;
	    thr->children.insert(child);
	    assert(thr->children.size()==1);
	    assert(child->parent_scope->get_type_code() == vpiFunction);
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;

	    if (child->i_have_ended) {
		  do_join(thr, child);
		  return true;
	    } else {
		  thr->i_am_joining = 1;
		  return false;
	    }
      }

      return do_callf_void(thr, child);
}

/*
 * The %cassign/link instruction connects a source node to a
 * destination node. The destination node must be a signal, as it is
 * marked with the source of the cassign so that it may later be
 * unlinked without specifically knowing the source that this
 * instruction used.
 */
bool of_CASSIGN_LINK(vthread_t, vvp_code_t cp)
{
      vvp_net_t*dst = cp->net;
      vvp_net_t*src = cp->net2;

      vvp_fun_signal_base*sig
	    = dynamic_cast<vvp_fun_signal_base*>(dst->fun);
      assert(sig);

	/* Any previous continuous assign should have been removed already. */
      assert(sig->cassign_link == 0);

      sig->cassign_link = src;

	/* Link the output of the src to the port[1] (the cassign
	   port) of the destination. */
      vvp_net_ptr_t dst_ptr (dst, 1);
      src->link(dst_ptr);

      return true;
}

/*
 * If there is an existing continuous assign linked to the destination
 * node, unlink it. This must be done before applying a new continuous
 * assign, otherwise the initial assigned value will be propagated to
 * any other nodes driven by the old continuous assign source.
 */
static void cassign_unlink(vvp_net_t*dst)
{
      vvp_fun_signal_base*sig
	    = dynamic_cast<vvp_fun_signal_base*>(dst->fun);
      assert(sig);

      if (sig->cassign_link == 0)
	    return;

      vvp_net_ptr_t tmp (dst, 1);
      sig->cassign_link->unlink(tmp);
      sig->cassign_link = 0;
}

/*
 * The %cassign/v instruction invokes a continuous assign of a
 * constant value to a signal. The instruction arguments are:
 *
 *     %cassign/vec4 <net>;
 *
 * Where the <net> is the net label assembled into a vvp_net pointer,
 * and the <base> and <wid> are stashed in the bit_idx array.
 *
 * This instruction writes vvp_vector4_t values to port-1 of the
 * target signal.
 */
bool of_CASSIGN_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      vvp_vector4_t value = thr->pop_vec4();

	/* Remove any previous continuous assign to this net. */
      cassign_unlink(net);

	/* Set the value into port 1 of the destination. */
      vvp_net_ptr_t ptr (net, 1);
      vvp_send_vec4(ptr, value, 0);

      return true;
}

/*
 * %cassign/vec4/off <var>, <off>
 */
bool of_CASSIGN_VEC4_OFF(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned base_idx = cp->bit_idx[0];
      long base = thr->words[base_idx].w_int;
      vvp_vector4_t value = thr->pop_vec4();
      unsigned wid = value.size();

      if (thr->flags[4] == BIT4_1)
	    return true;

	/* Remove any previous continuous assign to this net. */
      cassign_unlink(net);

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (net->fil);
      assert(sig);

      if (base < 0 && (wid <= (unsigned)-base))
	    return true;

      if (base >= (long)sig->value_size())
	    return true;

      if (base < 0) {
	    wid -= (unsigned) -base;
	    base = 0;
	    value.resize(wid);
      }

      if (base+wid > sig->value_size()) {
	    wid = sig->value_size() - base;
	    value.resize(wid);
      }

      vvp_net_ptr_t ptr (net, 1);
      vvp_send_vec4_pv(ptr, value, base, sig->value_size(), 0);
      return true;
}

bool of_CASSIGN_WR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net  = cp->net;
      double value = thr->pop_real();

	/* Remove any previous continuous assign to this net. */
      cassign_unlink(net);

	/* Set the value into port 1 of the destination. */
      vvp_net_ptr_t ptr (net, 1);
      vvp_send_real(ptr, value, 0);

      return true;
}

/*
 * %cast <dst_signal>, <target_class_type>
 *
 * Pop the source object from the object stack.
 * Check if its actual class is compatible with target_class_type.
 * If compatible: store to dst_signal and push 1 to vec4 stack.
 * If not compatible: push 0 to vec4 stack.
 */
bool of_CAST(vthread_t thr, vvp_code_t cp)
{
      // Get target class type from handle (in first union)
      class_type*target_class = dynamic_cast<class_type*>(cp->handle);
      if (!target_class) {
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      // Pop source object from object stack
      vvp_object_t src;
      thr->pop_object(src);

      // Check if source is null
      vvp_cobject*cobj = src.peek<vvp_cobject>();
      if (cobj == 0) {
	    // Null object - cast fails
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      // Get the actual class type of the source object
      const class_type*actual_class = cobj->get_class_type();

      // Check if actual_class is same as or derived from target_class
      if (actual_class->is_derived_from(target_class)) {
	    // Cast succeeds - store to destination (net2 is in second union) and return 1
	    vvp_net_ptr_t ptr (cp->net2, 0);
	    vvp_send_object(ptr, src, thr->wt_context);
	    vvp_vector4_t res(32, BIT4_0);
	    res.set_bit(0, BIT4_1);
	    thr->push_vec4(res);
      } else {
	    // Cast fails - return 0
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %cast/prop <prop_idx>, <target_class>
 * Cast and store to a property of an object.
 * Object stack: [dest_obj, src_obj]
 * Pop src_obj, check if compatible with target_class.
 * If compatible: store to dest_obj.prop[prop_idx], push 1 to vec4 stack.
 * If not compatible: push 0 to vec4 stack.
 * Pop both objects from stack.
 */
bool of_CAST_PROP(vthread_t thr, vvp_code_t cp)
{
      // Get property index and target class type
      // Note: OA_BIT1 is stored in cp->bit_idx[0], OA_VPI_PTR in cp->handle
      unsigned prop_idx = cp->bit_idx[0];
      class_type*target_class = dynamic_cast<class_type*>(cp->handle);

      if (!target_class) {
	    thr->pop_object(2);  // pop src and dest
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      // Pop source object
      vvp_object_t src;
      thr->pop_object(src);

      // Pop destination object (the object containing the property)
      vvp_object_t dest;
      thr->pop_object(dest);

      vvp_cobject*dest_cobj = dest.peek<vvp_cobject>();

      // Check if source is null
      vvp_cobject*src_cobj = src.peek<vvp_cobject>();
      if (src_cobj == 0) {
	    // Null source - cast fails
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      // Get the actual class type of the source object
      const class_type*actual_class = src_cobj->get_class_type();

      // Check if actual_class is same as or derived from target_class
      if (actual_class->is_derived_from(target_class)) {
	    // Cast succeeds - store src to dest's property
	    if (dest_cobj) {
		  dest_cobj->set_object(prop_idx, src, 0);
	    }
	    vvp_vector4_t res(32, BIT4_0);
	    res.set_bit(0, BIT4_1);
	    thr->push_vec4(res);
      } else {
	    // Cast fails
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %config_db/get/v <dest_signal>
 * Pop field_name and inst_name from string stack.
 * Look up vec4 value in config_db, store to dest_signal.
 * Push 1 to vec4 stack if found, 0 if not found.
 */
bool of_CONFIG_DB_GET_V(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Get context path from thread's scope
      std::string context_path;
      __vpiScope*scope = vthread_scope(thr);
      if (scope) {
            const char*full_name = scope->vpi_get_str(vpiFullName);
            if (full_name) {
                  context_path = full_name;
            }
      }

      // Look up in config_db
      vvp_vector4_t value;
      bool found = vvp_config_db::instance().get_vec4(context_path, inst_name, field_name, value);

      if (found) {
            // Store value to destination signal
            vvp_net_ptr_t ptr(net, 0);
            vvp_send_vec4(ptr, value, thr->wt_context);
            vvp_vector4_t res(32, BIT4_0);
            res.set_bit(0, BIT4_1);
            thr->push_vec4(res);
      } else {
            thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %config_db/get/o <dest_signal>
 * Pop field_name and inst_name from string stack.
 * Look up object value in config_db, store to dest_signal.
 * Push 1 to vec4 stack if found, 0 if not found.
 */
bool of_CONFIG_DB_GET_O(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Get context path from thread's scope
      std::string context_path;
      __vpiScope*scope = vthread_scope(thr);
      if (scope) {
            const char*full_name = scope->vpi_get_str(vpiFullName);
            if (full_name) {
                  context_path = full_name;
            }
      }

      // Look up in config_db
      vvp_object_t value;
      bool found = vvp_config_db::instance().get_object(context_path, inst_name, field_name, value);

      if (found) {
            // Store value to destination signal
            vvp_net_ptr_t ptr(net, 0);
            vvp_send_object(ptr, value, thr->wt_context);
            vvp_vector4_t res(32, BIT4_0);
            res.set_bit(0, BIT4_1);
            thr->push_vec4(res);
      } else {
            thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %config_db/set/v <width>
 * Pop field_name and inst_name from string stack, pop vec4 from vec4 stack.
 * Store in config_db.
 */
bool of_CONFIG_DB_SET_V(vthread_t thr, vvp_code_t)
{
      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Note: UVM's set(null, inst_name, field, value) means the context is null
      // (i.e., use inst_name as the absolute path). The parser skips the context
      // argument, so we should NOT add the calling scope's path. Just use "null"
      // as context_path which make_key will handle correctly.
      std::string context_path = "null";

      // Pop vec4 from vec4 stack
      vvp_vector4_t value = thr->pop_vec4();

      // Store in config_db
      vvp_config_db::instance().set_vec4(context_path, inst_name, field_name, value);

      return true;
}

/*
 * %config_db/set/o
 * Pop field_name and inst_name from string stack, pop object from object stack.
 * Store in config_db.
 */
bool of_CONFIG_DB_SET_O(vthread_t thr, vvp_code_t)
{
      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Note: UVM's set(null, inst_name, field, value) means the context is null
      // (i.e., use inst_name as the absolute path). The parser skips the context
      // argument, so we should NOT add the calling scope's path. Just use "null"
      // as context_path which make_key will handle correctly.
      std::string context_path = "null";

      // Pop object from object stack
      vvp_object_t value;
      thr->pop_object(value);

      // Store in config_db
      vvp_config_db::instance().set_object(context_path, inst_name, field_name, value);

      return true;
}

/*
 * %config_db/get/dar <index_register>
 * Pop field_name and inst_name from string stack.
 * Pop darray from object stack, peek base object for context.
 * Look up object value in config_db, store to darray element at index.
 * Pop base object when done.
 * Push 1 to vec4 stack if found, 0 if not found.
 */
bool of_CONFIG_DB_GET_DAR(vthread_t thr, vvp_code_t cp)
{
      int idx_reg = cp->number;
      long idx = thr->words[idx_reg].w_int;

      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Pop darray from object stack (was pushed by %prop/obj)
      vvp_object_t darray_obj;
      thr->pop_object(darray_obj);
      vvp_darray*darray = darray_obj.peek<vvp_darray>();

      // Peek base object (still on stack from before %prop/obj)
      vvp_object_t&base_obj = thr->peek_object();

      // Get context from base object's m_full_name property if available
      std::string context_path = "";
      vvp_cobject*cobj = base_obj.peek<vvp_cobject>();
      if (cobj && inst_name.empty()) {
            // Look up m_full_name property (property index 3 in uvm_component)
            // Property layout: 0=m_name, 1=m_verbosity, 2=m_parent, 3=m_full_name, ...
            // Only access if the class has at least 4 properties (is a uvm_component or derived)
            const class_type* ct = cobj->get_class_type();
            if (ct->property_count() > 3) {
                  std::string full_name = cobj->get_string(3);
                  if (!full_name.empty()) {
                        context_path = full_name;
                  }
            }
      }

      // Pop base object now that we've extracted context
      vvp_object_t base_tmp;
      thr->pop_object(base_tmp);

      // Look up in config_db using context from base object
      vvp_object_t value;
      bool found = vvp_config_db::instance().get_object(context_path, inst_name, field_name, value);

      if (found && darray) {
            // Store value to darray element
            darray->set_word(idx, value);
            vvp_vector4_t res(32, BIT4_0);
            res.set_bit(0, BIT4_1);
            thr->push_vec4(res);
      } else {
            // Not found OR couldn't store (darray is null)
            thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %config_db/get/prop <property_index>
 * Pop field_name and inst_name from string stack.
 * Pop base object from object stack.
 * Look up object value in config_db, store to property of base object.
 * Push 1 to vec4 stack if found, 0 if not found.
 */
bool of_CONFIG_DB_GET_PROP(vthread_t thr, vvp_code_t cp)
{
      unsigned prop_idx = cp->number;

      // Pop field_name and inst_name from string stack
      std::string field_name = thr->pop_str();
      std::string inst_name = thr->pop_str();

      // Pop base object from object stack
      vvp_object_t base_obj;
      thr->pop_object(base_obj);

      // Try to get context from base object's m_full_name, fall back to thread scope
      std::string context_path;
      vvp_cobject*cobj = base_obj.peek<vvp_cobject>();
      if (cobj) {
            // Look up m_full_name property (property index 3 in uvm_component)
            // Property layout: 0=m_name, 1=m_verbosity, 2=m_parent, 3=m_full_name, ...
            // Only access if the class has at least 4 properties (is a uvm_component or derived)
            const class_type* ct = cobj->get_class_type();
            if (ct->property_count() > 3) {
                  std::string full_name = cobj->get_string(3);
                  if (!full_name.empty()) {
                        context_path = full_name;
                  }
            }
      }

      // Fall back to thread scope if no context from object
      if (context_path.empty()) {
            __vpiScope*scope = vthread_scope(thr);
            if (scope) {
                  const char*full_name = scope->vpi_get_str(vpiFullName);
                  if (full_name) {
                        context_path = full_name;
                  }
            }
      }

      bool found = false;

      // Try to get as object first (for class-type properties)
      vvp_object_t obj_value;
      if (vvp_config_db::instance().get_object(context_path, inst_name, field_name, obj_value)) {
            if (cobj) {
                  cobj->set_object(prop_idx, obj_value, 0);
                  found = true;
            }
      }

      // If not found as object, try as vec4 (for enum/int properties)
      if (!found) {
            vvp_vector4_t vec_value;
            if (vvp_config_db::instance().get_vec4(context_path, inst_name, field_name, vec_value)) {
                  if (cobj) {
                        cobj->set_vec4(prop_idx, vec_value);
                        found = true;
                  }
            }
      }

      if (found) {
            vvp_vector4_t res(32, BIT4_0);
            res.set_bit(0, BIT4_1);
            thr->push_vec4(res);
      } else {
            // Not found OR couldn't store (base object is null)
            thr->push_vec4(vvp_vector4_t(32, BIT4_0));
      }

      return true;
}

/*
 * %cast2
 */
bool of_CAST2(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t&val = thr->peek_vec4();
      unsigned wid = val.size();

      for (unsigned idx = 0 ; idx < wid ; idx += 1) {
	    switch (val.value(idx)) {
		case BIT4_0:
		case BIT4_1:
		  break;
		default:
		  val.set_bit(idx, BIT4_0);
		  break;
	    }
      }

      return true;
}

bool do_cast_vec_dar(vthread_t thr, vvp_code_t cp, bool as_vec4)
{
      unsigned wid = cp->number;

      vvp_object_t obj;
      thr->pop_object(obj);

      vvp_darray*darray = obj.peek<vvp_darray>();
      assert(darray);

      vvp_vector4_t vec = darray->get_bitstream(as_vec4);
      if (vec.size() != wid) {
	    cerr << thr->get_fileline()
	         << "VVP error: size mismatch when casting dynamic array to vector." << endl;
            thr->push_vec4(vvp_vector4_t(wid));
            schedule_stop(0);
            return false;
      }
      thr->push_vec4(vec);
      return true;
}

/*
 * %cast/vec2/dar <wid>
 */
bool of_CAST_VEC2_DAR(vthread_t thr, vvp_code_t cp)
{
      return do_cast_vec_dar(thr, cp, false);
}

/*
 * %cast/vec4/dar <wid>
 */
bool of_CAST_VEC4_DAR(vthread_t thr, vvp_code_t cp)
{
      return do_cast_vec_dar(thr, cp, true);
}

/*
 * %cast/vec4/str <wid>
 *
 * Convert string to vec4. The string contains binary data where each
 * character represents 8 bits. If the string is shorter than wid/8 bytes,
 * the missing low-order bytes are treated as zero (this happens when
 * %pushv/str drops trailing zero bytes).
 */
bool of_CAST_VEC4_STR(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;
      string str = thr->pop_str();

      vvp_vector4_t vec(wid, BIT4_0);

      // String can be shorter than wid/8 bytes if trailing zeros were dropped.
      // Allow short strings and treat missing bytes as zero.
      unsigned str_bits = 8 * str.length();
      if (str_bits > wid) {
	    cerr << thr->get_fileline()
	         << "VVP error: string too long when casting to vector "
	         << "(string has " << str_bits << " bits, target is " << wid << " bits)." << endl;
            thr->push_vec4(vec);
            schedule_stop(0);
            return false;
      }

      // Convert string bytes to vector bits.
      // String byte 0 is the MSB, but the vector is stored with LSB first.
      // We iterate from the end of the string (LSB) backwards.
      unsigned sdx = str.length();
      unsigned vdx = 0;
      while (sdx > 0 && vdx < wid) {
            char ch = str[--sdx];
            for (unsigned bdx = 0; bdx < 8 && vdx + bdx < wid; bdx += 1) {
                  if (ch & (1 << bdx))
                        vec.set_bit(vdx + bdx, BIT4_1);
            }
            vdx += 8;
      }

      thr->push_vec4(vec);
      return true;
}

static void do_CMPE(vthread_t thr, const vvp_vector4_t&lval, const vvp_vector4_t&rval)
{
      // Operands may have different sizes - extend the smaller to match the larger
      if (rval.size() != lval.size()) {
	    unsigned wid = (lval.size() > rval.size()) ? lval.size() : rval.size();
	    // Zero-extend both operands to the larger width and compare
	    vvp_vector4_t lval_ext = lval;
	    vvp_vector4_t rval_ext = rval;
	    lval_ext.resize(wid, BIT4_0);
	    rval_ext.resize(wid, BIT4_0);
	    // Recursively call with extended operands
	    return do_CMPE(thr, lval_ext, rval_ext);
      }

      if (lval.has_xz() || rval.has_xz()) {

	    unsigned wid = lval.size();
	    vvp_bit4_t eq  = BIT4_1;
	    vvp_bit4_t eeq = BIT4_1;

	    for (unsigned idx = 0 ; idx < wid ; idx += 1) {
		  vvp_bit4_t lv = lval.value(idx);
		  vvp_bit4_t rv = rval.value(idx);

		  if (lv != rv)
			eeq = BIT4_0;

		  if (eq==BIT4_1 && (bit4_is_xz(lv) || bit4_is_xz(rv)))
			eq = BIT4_X;
		  if ((lv == BIT4_0) && (rv==BIT4_1))
			eq = BIT4_0;
		  if ((lv == BIT4_1) && (rv==BIT4_0))
			eq = BIT4_0;

		  if (eq == BIT4_0)
			break;
	    }

	    thr->flags[4] = eq;
	    thr->flags[6] = eeq;

      } else {
	      // If there are no XZ bits anywhere, then the results of
	      // == match the === test.
	    thr->flags[4] = thr->flags[6] = (lval.eeq(rval)? BIT4_1 : BIT4_0);
      }
}

/*
 *  %cmp/e
 *
 * Pop the operands from the stack, and do not replace them. The
 * results are written to flag bits:
 *
 *	4: eq  (equal)
 *
 *	6: eeq (case equal)
 */
bool of_CMPE(vthread_t thr, vvp_code_t)
{
	// We are going to pop these and push nothing in their
	// place, but for now it is more efficient to use a constant
	// reference. When we finish, pop the stack without copies.
      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPE(thr, lval, rval);

      thr->pop_vec4(2);
      return true;
}

bool of_CMPNE(vthread_t thr, vvp_code_t)
{
	// We are going to pop these and push nothing in their
	// place, but for now it is more efficient to use a constant
	// reference. When we finish, pop the stack without copies.
      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPE(thr, lval, rval);

      thr->flags[4] =  ~thr->flags[4];
      thr->flags[6] =  ~thr->flags[6];

      thr->pop_vec4(2);
      return true;
}

/*
 * %cmpi/e <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments.
 */
bool of_CMPIE(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      const vvp_vector4_t&lval = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t rval (wid, BIT4_0);
      get_immediate_rval (cp, rval);

      do_CMPE(thr, lval, rval);

      thr->pop_vec4(1);
      return true;
}

bool of_CMPINE(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      const vvp_vector4_t&lval = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t rval (wid, BIT4_0);
      get_immediate_rval (cp, rval);

      do_CMPE(thr, lval, rval);

      thr->flags[4] =  ~thr->flags[4];
      thr->flags[6] =  ~thr->flags[6];

      thr->pop_vec4(1);
      return true;
}



static void do_CMPS(vthread_t thr, const vvp_vector4_t&lval, const vvp_vector4_t&rval)
{
      // Operands may have different sizes - sign-extend the smaller to match the larger
      if (rval.size() != lval.size()) {
	    unsigned wid = (lval.size() > rval.size()) ? lval.size() : rval.size();
	    // Sign-extend both operands to the larger width
	    vvp_vector4_t lval_ext = lval;
	    vvp_vector4_t rval_ext = rval;
	    // Get sign bits before resize
	    vvp_bit4_t lval_sign = lval.size() > 0 ? lval.value(lval.size()-1) : BIT4_0;
	    vvp_bit4_t rval_sign = rval.size() > 0 ? rval.value(rval.size()-1) : BIT4_0;
	    // Resize with sign bit
	    lval_ext.resize(wid, lval_sign);
	    rval_ext.resize(wid, rval_sign);
	    // Recursively call with extended operands
	    return do_CMPS(thr, lval_ext, rval_ext);
      }

	// If either value has XZ bits, then the eq and lt values are
	// known already to be X. Just calculate the eeq result as a
	// special case and short circuit the rest of the compare.
      if (lval.has_xz() || rval.has_xz()) {
	    thr->flags[4] = BIT4_X; // eq
	    thr->flags[5] = BIT4_X; // lt
	    thr->flags[6] = lval.eeq(rval)? BIT4_1 : BIT4_0;
	    return;
      }

	// Past this point, we know we are dealing only with fully
	// defined values.
      unsigned wid = lval.size();

      const vvp_bit4_t sig1 = lval.value(wid-1);
      const vvp_bit4_t sig2 = rval.value(wid-1);

	// If the lval is <0 and the rval is >=0, then we know the result.
      if ((sig1 == BIT4_1) && (sig2 == BIT4_0)) {
	    thr->flags[4] = BIT4_0; // eq;
	    thr->flags[5] = BIT4_1; // lt;
	    thr->flags[6] = BIT4_0; // eeq
	    return;
      }

	// If the lval is >=0 and the rval is <0, then we know the result.
      if ((sig1 == BIT4_0) && (sig2 == BIT4_1)) {
	    thr->flags[4] = BIT4_0; // eq;
	    thr->flags[5] = BIT4_0; // lt;
	    thr->flags[6] = BIT4_0; // eeq
	    return;
      }

	// The values have the same sign, so we have to look at the
	// actual value. Scan from the MSB down. As soon as we find a
	// bit that differs, we know the result.

      for (unsigned idx = 1 ;  idx < wid ;  idx += 1) {
	    vvp_bit4_t lv = lval.value(wid-1-idx);
	    vvp_bit4_t rv = rval.value(wid-1-idx);

	    if (lv == rv)
		  continue;

	    thr->flags[4] = BIT4_0; // eq
	    thr->flags[6] = BIT4_0; // eeq

	    if (lv==BIT4_0) {
		  thr->flags[5] = BIT4_1; // lt
	    } else {
		  thr->flags[5] = BIT4_0; // lt
	    }
	    return;
      }

	// If we survive the loop above, then the values must be equal.
      thr->flags[4] = BIT4_1;
      thr->flags[5] = BIT4_0;
      thr->flags[6] = BIT4_1;
}

/*
 *  %cmp/s
 *
 * Pop the operands from the stack, and do not replace them. The
 * results are written to flag bits:
 *
 *	4: eq  (equal)
 *	5: lt  (less than)
 *	6: eeq (case equal)
 */
bool of_CMPS(vthread_t thr, vvp_code_t)
{
	// We are going to pop these and push nothing in their
	// place, but for now it is more efficient to use a constant
	// reference. When we finish, pop the stack without copies.
      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPS(thr, lval, rval);

      thr->pop_vec4(2);
      return true;
}

/*
 * %cmpi/s <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments.
 */
bool of_CMPIS(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      const vvp_vector4_t&lval = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t rval (wid, BIT4_0);
      get_immediate_rval (cp, rval);

      do_CMPS(thr, lval, rval);

      thr->pop_vec4(1);
      return true;
}

bool of_CMPSTR(vthread_t thr, vvp_code_t)
{
      string re = thr->pop_str();
      string le = thr->pop_str();

      int rc = strcmp(le.c_str(), re.c_str());

      vvp_bit4_t eq;
      vvp_bit4_t lt;

      if (rc == 0) {
	    eq = BIT4_1;
	    lt = BIT4_0;
      } else if (rc < 0) {
	    eq = BIT4_0;
	    lt = BIT4_1;
      } else {
	    eq = BIT4_0;
	    lt = BIT4_0;
      }

      thr->flags[4] = eq;
      thr->flags[5] = lt;

      return true;
}

/*
 * %cmp/obj
 *    Compare two objects (queues, dynamic arrays, etc.) for equality.
 *    Pops two objects from the object stack and compares them.
 *    Sets flag 4 to 1 if equal, 0 otherwise.
 */
bool of_CMPOBJ(vthread_t thr, vvp_code_t)
{
      vvp_object_t re;
      vvp_object_t le;
      thr->pop_object(re);
      thr->pop_object(le);

      vvp_bit4_t eq = BIT4_0;

      /* If both are null/empty, they're equal */
      if (le.test_nil() && re.test_nil()) {
	    eq = BIT4_1;
      }
      /* If one is null and other isn't, not equal */
      else if (le.test_nil() || re.test_nil()) {
	    eq = BIT4_0;
      }
      /* For queues and dynamic arrays, compare element by element */
      else {
	    vvp_darray*le_arr = le.peek<vvp_darray>();
	    vvp_darray*re_arr = re.peek<vvp_darray>();

	    if (le_arr && re_arr) {
		  /* Both are arrays - compare sizes first */
		  size_t le_size = le_arr->get_size();
		  size_t re_size = re_arr->get_size();

		  if (le_size == re_size) {
			eq = BIT4_1;
			/* Compare elements */
			for (size_t i = 0; i < le_size && eq == BIT4_1; i++) {
			      vvp_vector4_t le_val;
			      vvp_vector4_t re_val;
			      le_arr->get_word(i, le_val);
			      re_arr->get_word(i, re_val);
			      if (!le_val.eeq(re_val))
				    eq = BIT4_0;
			}
		  }
	    } else {
		  /* For non-array objects, assume not equal */
		  eq = BIT4_0;
	    }
      }

      thr->flags[4] = eq;
      thr->flags[5] = BIT4_0; /* lt flag not meaningful for object comparison */

      return true;
}

static void of_CMPU_the_hard_way(vthread_t thr, unsigned wid,
				 const vvp_vector4_t&lval,
				 const vvp_vector4_t&rval)
{
      vvp_bit4_t eq = BIT4_1;
      vvp_bit4_t eeq = BIT4_1;

      for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {
	    vvp_bit4_t lv = lval.value(idx);
	    vvp_bit4_t rv = rval.value(idx);

	    if (lv != rv)
		  eeq = BIT4_0;

	    if (eq==BIT4_1 && (bit4_is_xz(lv) || bit4_is_xz(rv)))
		  eq = BIT4_X;
	    if ((lv == BIT4_0) && (rv==BIT4_1))
		  eq = BIT4_0;
	    if ((lv == BIT4_1) && (rv==BIT4_0))
		  eq = BIT4_0;

	    if (eq == BIT4_0)
		  break;

      }

      thr->flags[4] = eq;
      thr->flags[5] = BIT4_X;
      thr->flags[6] = eeq;
}

static void do_CMPU(vthread_t thr, const vvp_vector4_t&lval, const vvp_vector4_t&rval)
{
      vvp_bit4_t eq = BIT4_1;
      vvp_bit4_t lt = BIT4_0;

      // Operands may have different sizes - extend the smaller to match the larger
      unsigned wid = lval.size();
      if (rval.size() != lval.size()) {
	    wid = (lval.size() > rval.size()) ? lval.size() : rval.size();
	    // Zero-extend both operands to the larger width and compare
	    vvp_vector4_t lval_ext = lval;
	    vvp_vector4_t rval_ext = rval;
	    lval_ext.resize(wid, BIT4_0);
	    rval_ext.resize(wid, BIT4_0);
	    // Recursively call with extended operands
	    return do_CMPU(thr, lval_ext, rval_ext);
      }

      unsigned long*larray = lval.subarray(0,wid);
      if (larray == 0) return of_CMPU_the_hard_way(thr, wid, lval, rval);

      unsigned long*rarray = rval.subarray(0,wid);
      if (rarray == 0) {
	    delete[]larray;
	    return of_CMPU_the_hard_way(thr, wid, lval, rval);
      }

      unsigned words = (wid+CPU_WORD_BITS-1) / CPU_WORD_BITS;

      for (unsigned wdx = 0 ; wdx < words ; wdx += 1) {
	    if (larray[wdx] == rarray[wdx])
		  continue;

	    eq = BIT4_0;
	    if (larray[wdx] < rarray[wdx])
		  lt = BIT4_1;
	    else
		  lt = BIT4_0;
      }

      delete[]larray;
      delete[]rarray;

      thr->flags[4] = eq;
      thr->flags[5] = lt;
      thr->flags[6] = eq;
}

bool of_CMPU(vthread_t thr, vvp_code_t)
{

      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPU(thr, lval, rval);

      thr->pop_vec4(2);
      return true;
}

/*
 * %cmpi/u <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments.
 */
bool of_CMPIU(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      const vvp_vector4_t&lval = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t rval (wid, BIT4_0);
      get_immediate_rval (cp, rval);

      do_CMPU(thr, lval, rval);

      thr->pop_vec4(1);
      return true;
}


/*
 * %cmp/x
 */
bool of_CMPX(vthread_t thr, vvp_code_t)
{
      vvp_bit4_t eq = BIT4_1;
      vvp_vector4_t rval = thr->pop_vec4();
      vvp_vector4_t lval = thr->pop_vec4();

      assert(rval.size() == lval.size());
      unsigned wid = lval.size();

      for (unsigned idx = 0 ; idx < wid ; idx += 1) {
	    vvp_bit4_t lv = lval.value(idx);
	    vvp_bit4_t rv = rval.value(idx);
	    if ((lv != rv) && !bit4_is_xz(lv) && !bit4_is_xz(rv)) {
		  eq = BIT4_0;
		  break;
	    }
      }

      thr->flags[4] = eq;
      return true;
}

static void do_CMPWE(vthread_t thr, const vvp_vector4_t&lval, const vvp_vector4_t&rval)
{
      // Operands may have different sizes - extend the smaller to match the larger
      if (rval.size() != lval.size()) {
	    unsigned wid = (lval.size() > rval.size()) ? lval.size() : rval.size();
	    // Zero-extend both operands to the larger width
	    vvp_vector4_t lval_ext = lval;
	    vvp_vector4_t rval_ext = rval;
	    lval_ext.resize(wid, BIT4_0);
	    rval_ext.resize(wid, BIT4_0);
	    // Recursively call with extended operands
	    return do_CMPWE(thr, lval_ext, rval_ext);
      }

      if (lval.has_xz() || rval.has_xz()) {

	    unsigned wid = lval.size();
	    vvp_bit4_t eq  = BIT4_1;

	    for (unsigned idx = 0 ; idx < wid ; idx += 1) {
		  vvp_bit4_t lv = lval.value(idx);
		  vvp_bit4_t rv = rval.value(idx);

		  if (bit4_is_xz(rv))
			continue;
		  if ((eq == BIT4_1) && bit4_is_xz(lv))
			eq = BIT4_X;
		  if ((lv == BIT4_0) && (rv==BIT4_1))
			eq = BIT4_0;
		  if ((lv == BIT4_1) && (rv==BIT4_0))
			eq = BIT4_0;

		  if (eq == BIT4_0)
			break;
	    }

	    thr->flags[4] = eq;

      } else {
	      // If there are no XZ bits anywhere, then the results of
	      // ==? match the === test.
	    thr->flags[4] = (lval.eeq(rval)? BIT4_1 : BIT4_0);
      }
}

bool of_CMPWE(vthread_t thr, vvp_code_t)
{
	// We are going to pop these and push nothing in their
	// place, but for now it is more efficient to use a constant
	// reference. When we finish, pop the stack without copies.
      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPWE(thr, lval, rval);

      thr->pop_vec4(2);
      return true;
}

bool of_CMPWNE(vthread_t thr, vvp_code_t)
{
	// We are going to pop these and push nothing in their
	// place, but for now it is more efficient to use a constant
	// reference. When we finish, pop the stack without copies.
      const vvp_vector4_t&rval = thr->peek_vec4(0);
      const vvp_vector4_t&lval = thr->peek_vec4(1);

      do_CMPWE(thr, lval, rval);

      thr->flags[4] =  ~thr->flags[4];

      thr->pop_vec4(2);
      return true;
}

bool of_CMPWR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();

      vvp_bit4_t eq = (l == r)? BIT4_1 : BIT4_0;
      vvp_bit4_t lt = (l <  r)? BIT4_1 : BIT4_0;

      thr->flags[4] = eq;
      thr->flags[5] = lt;

      return true;
}

/*
 * %cmp/z
 */
bool of_CMPZ(vthread_t thr, vvp_code_t)
{
      vvp_bit4_t eq = BIT4_1;
      vvp_vector4_t rval = thr->pop_vec4();
      vvp_vector4_t lval = thr->pop_vec4();

      assert(rval.size() == lval.size());
      unsigned wid = lval.size();

      for (unsigned idx = 0 ; idx < wid ; idx += 1) {
	    vvp_bit4_t lv = lval.value(idx);
	    vvp_bit4_t rv = rval.value(idx);
	    if ((lv != rv) && (rv != BIT4_Z) && (lv != BIT4_Z)) {
		  eq = BIT4_0;
		  break;
	    }
      }

      thr->flags[4] = eq;
      return true;
}

/*
 *  %concat/str;
 */
bool of_CONCAT_STR(vthread_t thr, vvp_code_t)
{
      string text = thr->pop_str();
      thr->peek_str(0).append(text);
      return true;
}

/*
 *  %concati/str <string>;
 */
bool of_CONCATI_STR(vthread_t thr, vvp_code_t cp)
{
      const char*text = cp->text;
      thr->peek_str(0).append(filter_string(text));
      return true;
}

/*
 * %concat/vec4
 */
bool of_CONCAT_VEC4(vthread_t thr, vvp_code_t)
{
      const vvp_vector4_t&lsb = thr->peek_vec4(0);
      const vvp_vector4_t&msb = thr->peek_vec4(1);

	// The result is the size of the top two vectors in the stack.
      vvp_vector4_t res (msb.size() + lsb.size(), BIT4_X);

	// Build up the result.
      res.set_vec(0, lsb);
      res.set_vec(lsb.size(), msb);

	// Rearrange the stack to pop the inputs and push the
	// result. Do that by actually popping only 1 stack position
	// and replacing the new top with the new value.
      thr->pop_vec4(1);
      thr->peek_vec4() = res;

      return true;
}

/*
 * %concati/vec4 <vala>, <valb>, <wid>
 *
 * Concat the immediate value to the LOW bits of the concatenation.
 * Get the HIGH bits from the top of the vec4 stack.
 */
bool of_CONCATI_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned wid  = cp->number;

      vvp_vector4_t&msb = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t lsb (wid, BIT4_0);
      get_immediate_rval (cp, lsb);

      vvp_vector4_t res (msb.size()+lsb.size(), BIT4_X);
      res.set_vec(0, lsb);
      res.set_vec(lsb.size(), msb);

      msb = res;
      return true;
}

/*
 * %cvt/rv
 */
bool of_CVT_RV(vthread_t thr, vvp_code_t)
{
      double val;
      vvp_vector4_t val4 = thr->pop_vec4();
      vector4_to_value(val4, val, false);
      thr->push_real(val);
      return true;
}

/*
 * %cvt/rv/s
 */
bool of_CVT_RV_S(vthread_t thr, vvp_code_t)
{
      double val;
      vvp_vector4_t val4 = thr->pop_vec4();
      vector4_to_value(val4, val, true);
      thr->push_real(val);
      return true;
}

/*
 * %cvt/sr <idx>
 * Pop the top value from the real stack, convert it to a 64bit signed
 * and save it to the indexed register.
 */
bool of_CVT_SR(vthread_t thr, vvp_code_t cp)
{
      double r = thr->pop_real();
      thr->words[cp->bit_idx[0]].w_int = i64round(r);

      return true;
}

/*
 * %cvt/ur <idx>
 */
bool of_CVT_UR(vthread_t thr, vvp_code_t cp)
{
      double r = thr->pop_real();
      thr->words[cp->bit_idx[0]].w_uint = vlg_round_to_u64(r);

      return true;
}

/*
 * %cvt/vr <wid>
 */
bool of_CVT_VR(vthread_t thr, vvp_code_t cp)
{
      double r = thr->pop_real();
      unsigned wid = cp->number;

      vvp_vector4_t tmp(wid, r);
      thr->push_vec4(tmp);
      return true;
}

/*
 * This implements the %deassign instruction. All we do is write a
 * long(1) to port-3 of the addressed net. This turns off an active
 * continuous assign activated by %cassign/v
 */
bool of_DEASSIGN(vthread_t, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned base  = cp->bit_idx[0];
      unsigned width = cp->bit_idx[1];

      vvp_signal_value*fil = dynamic_cast<vvp_signal_value*> (net->fil);
      assert(fil);
      vvp_fun_signal_vec*sig = dynamic_cast<vvp_fun_signal_vec*>(net->fun);
      assert(sig);

      if (base >= fil->value_size()) return true;
      if (base+width > fil->value_size()) width = fil->value_size() - base;

      bool full_sig = base == 0 && width == fil->value_size();

	// This is the net that is forcing me...
      if (vvp_net_t*src = sig->cassign_link) {
	    if (! full_sig) {
		  fprintf(stderr, "Sorry: when a signal is assigning a "
		          "register, I cannot deassign part of it.\n");
		  exit(1);
	    }
	      // And this is the pointer to be removed.
	    vvp_net_ptr_t dst_ptr (net, 1);
	    src->unlink(dst_ptr);
	    sig->cassign_link = 0;
      }

	/* Do we release all or part of the net? */
      if (full_sig) {
	    sig->deassign();
      } else {
	    sig->deassign_pv(base, width);
      }

      return true;
}

bool of_DEASSIGN_WR(vthread_t, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_real*sig = dynamic_cast<vvp_fun_signal_real*>(net->fun);
      assert(sig);

	// This is the net that is forcing me...
      if (vvp_net_t*src = sig->cassign_link) {
	      // And this is the pointer to be removed.
	    vvp_net_ptr_t dst_ptr (net, 1);
	    src->unlink(dst_ptr);
	    sig->cassign_link = 0;
      }

      sig->deassign();

      return true;
}

/*
 * %debug/thr
 */
bool of_DEBUG_THR(vthread_t thr, vvp_code_t cp)
{
      const char*text = cp->text;
      thr->debug_dump(cerr, text);
      return true;
}

/*
 * The delay takes two 32bit numbers to make up a 64bit time.
 *
 *   %delay <low>, <hig>
 */
bool of_DELAY(vthread_t thr, vvp_code_t cp)
{
      vvp_time64_t low = cp->bit_idx[0];
      vvp_time64_t hig = cp->bit_idx[1];

      vvp_time64_t delay = (hig << 32) | low;

      if (delay == 0) schedule_inactive(thr);
      else schedule_vthread(thr, delay);
      return false;
}

bool of_DELAYX(vthread_t thr, vvp_code_t cp)
{
      vvp_time64_t delay;

      assert(cp->number < vthread_s::WORDS_COUNT);
      delay = thr->words[cp->number].w_uint;
      if (delay == 0) schedule_inactive(thr);
      else schedule_vthread(thr, delay);
      return false;
}

bool of_DELETE_ELEM(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      int64_t idx_val = thr->words[3].w_int;
      if (thr->flags[4] == BIT4_1) {
	    cerr << thr->get_fileline()
	         << "Warning: skipping queue delete() with undefined index."
	         << endl;
	    return true;
      }
      if (idx_val < 0) {
	    cerr << thr->get_fileline()
	         << "Warning: skipping queue delete() with negative index."
	         << endl;
	    return true;
      }
      size_t idx = idx_val;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: skipping delete(" << idx
	         << ") on empty queue." << endl;
      } else {
	    size_t size = queue->get_size();
	    if (idx >= size) {
		  cerr << thr->get_fileline()
		       << "Warning: skipping out of range delete(" << idx
		       << ") on queue of size " << size << "." << endl;
	    } else {
		  queue->erase(idx);
	    }
      }

      return true;
}

/* %delete/obj <label>
 *
 * This operator works by assigning a nil to the target object. This
 * causes any value that might be there to be garbage collected, thus
 * deleting the object.
 */
bool of_DELETE_OBJ(vthread_t thr, vvp_code_t cp)
{
	/* set the value into port 0 of the destination. */
      vvp_net_ptr_t ptr (cp->net, 0);
      vvp_send_object(ptr, vvp_object_t(), thr->wt_context);

      return true;
}

/* %delete/tail <label>, idx
 *
 * Remove all elements after the one specified.
 */
bool of_DELETE_TAIL(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      assert(queue);

      unsigned idx = thr->words[cp->bit_idx[0]].w_int;
      queue->erase_tail(idx);

      return true;
}

static bool do_disable(vthread_t thr, vthread_t match)
{
      bool flag = false;

	/* Pull the target thread out of its scope if needed. */
      thr->parent_scope->threads.erase(thr);

	/* Turn the thread off by setting is program counter to
	   zero and setting an OFF bit. */
      thr->pc = codespace_null();
      thr->i_was_disabled = 1;
      thr->i_have_ended = 1;

	/* Turn off all the children of the thread. Simulate a %join
	   for as many times as needed to clear the results of all the
	   %forks that this thread has done. */
      while (! thr->children.empty()) {

	    vthread_t tmp = *(thr->children.begin());
	    assert(tmp);
	    assert(tmp->parent == thr);
	    thr->i_am_joining = 0;
	    if (do_disable(tmp, match))
		  flag = true;

	    vthread_reap(tmp);
      }

      vthread_t parent = thr->parent;
      if (parent && parent->i_am_joining) {
	      // If a parent is waiting in a %join, wake it up. Note
	      // that it is possible to be waiting in a %join yet
	      // already scheduled if multiple child threads are
	      // ending. So check if the thread is already scheduled
	      // before scheduling it again.
	    parent->i_am_joining = 0;
	    if (! parent->i_have_ended)
		  schedule_vthread(parent, 0, true);

	    do_join(parent, thr);

      } else if (parent) {
	      /* If the parent is yet to %join me, let its %join
		 do the reaping. */
	      //assert(tmp->is_scheduled == 0);

      } else {
	      /* No parent at all. Goodbye. */
	    vthread_reap(thr);
      }

      return flag || (thr == match);
}

/*
 * Implement the %disable instruction by scanning the target scope for
 * all the target threads. Kill the target threads and wake up a
 * parent that is attempting a %join.
 */
bool of_DISABLE(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*scope = static_cast<__vpiScope*>(cp->handle);

      bool disabled_myself_flag = false;

      while (! scope->threads.empty()) {
	    set<vthread_t>::iterator cur = scope->threads.begin();

	    if (do_disable(*cur, thr))
		  disabled_myself_flag = true;
      }

      return ! disabled_myself_flag;
}

/*
 * Similar to `of_DISABLE`. But will only disable a single thread of the
 * specified scope. The disabled thread will be the thread closest to the
 * current thread in thread hierarchy. This can either be the current thread,
 * either the thread itself or one of its parents.
 * This is used for SystemVerilog flow control instructions like `return`,
 * `continue` and `break`.
 */

bool of_DISABLE_FLOW(vthread_t thr, vvp_code_t cp)
{
      const __vpiScope*scope = static_cast<__vpiScope*>(cp->handle);
      vthread_t cur = thr;

      while (cur && cur->parent_scope != scope)
	    cur = cur->parent;

      assert(cur);
      if (cur)
	    return !do_disable(cur, thr);

      return false;
}

/*
 * Implement the %disable/fork (SystemVerilog) instruction by disabling
 * all the detached children of the given thread.
 */
bool of_DISABLE_FORK(vthread_t thr, vvp_code_t)
{
	/* If a %disable/fork is being executed then the parent thread
	 * cannot be waiting in a join. */
      assert(! thr->i_am_joining);

	/* There should be no active children to disable. */
      assert(thr->children.empty());

	/* Disable any detached children. */
      while (! thr->detached_children.empty()) {
	    vthread_t child = *(thr->detached_children.begin());
	    assert(child);
	    assert(child->parent == thr);
	      /* Disabling the children can never match the parent thread. */
	    bool res = do_disable(child, thr);
	    assert(! res);
	    vthread_reap(child);
      }

      return true;
}

/*
 * This function divides a 2-word number {high, a} by a 1-word
 * number. Assume that high < b.
 */
static unsigned long divide2words(unsigned long a, unsigned long b,
				  unsigned long high)
{
      unsigned long result = 0;
      while (high > 0) {
	    unsigned long tmp_result = ULONG_MAX / b;
	    unsigned long remain = ULONG_MAX % b;

	    remain += 1;
	    if (remain >= b) {
		  remain -= b;
		  tmp_result += 1;
	    }

	      // Now 0x1_0...0 = b*tmp_result + remain
	      // high*0x1_0...0 = high*(b*tmp_result + remain)
	      // high*0x1_0...0 = high*b*tmp_result + high*remain

	      // We know that high*0x1_0...0 >= high*b*tmp_result, and
	      // we know that high*0x1_0...0 > high*remain. Use
	      // high*remain as the remainder for another iteration,
	      // and add tmp_result*high into the current estimate of
	      // the result.
	    result += tmp_result * high;

	      // The new iteration starts with high*remain + a.
	    remain = multiply_with_carry(high, remain, high);
	    a += remain;
            if(a < remain)
              high += 1;

	      // Now result*b + {high,a} == the input {high,a}. It is
	      // possible that the new high >= 1. If so, it will
	      // certainly be less than high from the previous
	      // iteration. Do another iteration and it will shrink,
	      // eventually to 0.
      }

	// high is now 0, so a is the remaining remainder, so we can
	// finish off the integer divide with a simple a/b.

      return result + a/b;
}

static unsigned long* divide_bits(unsigned long*ap, const unsigned long*bp, unsigned wid)
{
	// Do all our work a cpu-word at a time. The "words" variable
	// is the number of words of the wid.
      unsigned words = (wid+CPU_WORD_BITS-1) / CPU_WORD_BITS;

      unsigned btop = words-1;
      while (btop > 0 && bp[btop] == 0)
	    btop -= 1;

	// Detect divide by 0, and exit.
      if (btop==0 && bp[0]==0)
	    return 0;

	// The result array will eventually accumulate the result. The
	// diff array is a difference that we use in the intermediate.
      unsigned long*diff  = new unsigned long[words];
      unsigned long*result= new unsigned long[words];
      for (unsigned idx = 0 ; idx < words ; idx += 1)
	    result[idx] = 0;

      for (unsigned cur = words-btop ; cur > 0 ; cur -= 1) {
	    unsigned cur_ptr = cur-1;
	    unsigned long cur_res;
	    if (ap[cur_ptr+btop] >= bp[btop]) {
		  unsigned long high = 0;
		  if (cur_ptr+btop+1 < words)
			high = ap[cur_ptr+btop+1];
		  cur_res = divide2words(ap[cur_ptr+btop], bp[btop], high);

	    } else if (cur_ptr+btop+1 >= words) {
		  continue;

	    } else if (ap[cur_ptr+btop+1] == 0) {
		  continue;

	    } else {
		  cur_res = divide2words(ap[cur_ptr+btop], bp[btop],
					 ap[cur_ptr+btop+1]);
	    }

	      // cur_res is a guesstimate of the result this far. It
	      // may be 1 too big. (But it will also be >0) Try it,
	      // and if the difference comes out negative, then adjust.

	      // diff = (bp * cur_res)  << cur_ptr;
	    multiply_array_imm(diff+cur_ptr, bp, words-cur_ptr, cur_res);
	      // ap -= diff
	    unsigned long carry = 1;
	    for (unsigned idx = cur_ptr ; idx < words ; idx += 1)
		  ap[idx] = add_with_carry(ap[idx], ~diff[idx], carry);

	      // ap has the diff subtracted out of it. If cur_res was
	      // too large, then ap will turn negative. (We easily
	      // tell that ap turned negative by looking at
	      // carry&1. If it is 0, then it is *negative*.) In that
	      // case, we know that cur_res was too large by 1. Correct by
	      // adding 1b back in and reducing cur_res.
	    if ((carry&1) == 0) {
		    // Keep adding b back in until the remainder
		    // becomes positive again.
		  do {
			cur_res -= 1;
			carry = 0;
			for (unsigned idx = cur_ptr ; idx < words ; idx += 1)
			      ap[idx] = add_with_carry(ap[idx], bp[idx-cur_ptr], carry);
		  } while (carry == 0);
	    }

	    result[cur_ptr] = cur_res;
      }

	// Now ap contains the remainder and result contains the
	// desired result. We should find that:
	//  input-a = bp * result + ap;

      delete[]diff;
      return result;
}

/*
 * %div
 */
bool of_DIV(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t vala = thr->pop_vec4();

      // Handle width mismatch by padding smaller operand to larger width
      unsigned wid_a = vala.size();
      unsigned wid_b = valb.size();
      unsigned wid = (wid_a > wid_b) ? wid_a : wid_b;
      if (wid_a < wid) vala.resize(wid, BIT4_0);
      if (wid_b < wid) valb.resize(wid, BIT4_0);

      unsigned long*ap = vala.subarray(0, wid);
      if (ap == 0) {
	    vvp_vector4_t tmp(wid, BIT4_X);
	    thr->push_vec4(tmp);
	    return true;
      }

      unsigned long*bp = valb.subarray(0, wid);
      if (bp == 0) {
	    delete[]ap;
	    vvp_vector4_t tmp(wid, BIT4_X);
	    thr->push_vec4(tmp);
	    return true;
      }

	// If the value fits in a single CPU word, then do it the easy way.
      if (wid <= CPU_WORD_BITS) {
	    if (bp[0] == 0) {
		  vvp_vector4_t tmp(wid, BIT4_X);
		  thr->push_vec4(tmp);
	    } else {
		  ap[0] /= bp[0];
		  vala.setarray(0, wid, ap);
		  thr->push_vec4(vala);
	    }
	    delete[]ap;
	    delete[]bp;
	    return true;
      }

      unsigned long*result = divide_bits(ap, bp, wid);
      if (result == 0) {
	    delete[]ap;
	    delete[]bp;
	    vvp_vector4_t tmp(wid, BIT4_X);
	    thr->push_vec4(tmp);
	    return true;
      }

	// Now ap contains the remainder and result contains the
	// desired result. We should find that:
	//  input-a = bp * result + ap;

      vala.setarray(0, wid, result);
      thr->push_vec4(vala);
      delete[]ap;
      delete[]bp;
      delete[]result;

      return true;
}


static void negate_words(unsigned long*val, unsigned words)
{
      unsigned long carry = 1;
      for (unsigned idx = 0 ; idx < words ; idx += 1)
	    val[idx] = add_with_carry(0, ~val[idx], carry);
}

/*
 * %div/s
 */
bool of_DIV_S(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t&vala = thr->peek_vec4();

      // Handle width mismatch by sign-extending smaller operand to larger width
      unsigned wid_a = vala.size();
      unsigned wid_b = valb.size();
      unsigned wid = (wid_a > wid_b) ? wid_a : wid_b;
      vvp_bit4_t sign_a = (wid_a > 0) ? vala.value(wid_a - 1) : BIT4_0;
      vvp_bit4_t sign_b = (wid_b > 0) ? valb.value(wid_b - 1) : BIT4_0;
      if (wid_a < wid) vala.resize(wid, sign_a);
      if (wid_b < wid) valb.resize(wid, sign_b);
      unsigned words = (wid + CPU_WORD_BITS - 1) / CPU_WORD_BITS;

	// Get the values, left in right, in binary form. If there is
	// a problem with either (caused by an X or Z bit) then we
	// know right away that the entire result is X.
      unsigned long*ap = vala.subarray(0, wid);
      if (ap == 0) {
	    vvp_vector4_t tmp(wid, BIT4_X);
	    vala = tmp;
	    return true;
      }

      unsigned long*bp = valb.subarray(0, wid);
      if (bp == 0) {
	    delete[]ap;
	    vvp_vector4_t tmp(wid, BIT4_X);
	    vala = tmp;
	    return true;
      }

	// Sign extend the bits in the array to fill out the array.
      unsigned long sign_mask = 0;
      if (unsigned long sign_bits = (words*CPU_WORD_BITS) - wid) {
	    sign_mask = -1UL << (CPU_WORD_BITS-sign_bits);
	    if (ap[words-1] & (sign_mask>>1))
		  ap[words-1] |= sign_mask;
	    if (bp[words-1] & (sign_mask>>1))
		  bp[words-1] |= sign_mask;
      }

	// If the value fits in a single word, then use the native divide.
      if (wid <= CPU_WORD_BITS) {
	    if (bp[0] == 0) {
		  vvp_vector4_t tmp(wid, BIT4_X);
		  vala = tmp;
	    } else if (((long)ap[0] == LONG_MIN) && ((long)bp[0] == -1)) {
		  vvp_vector4_t tmp(wid, BIT4_0);
		  tmp.set_bit(wid-1, BIT4_1);
		  vala = tmp;
	    } else {
		  long tmpa = (long) ap[0];
		  long tmpb = (long) bp[0];
		  long res = tmpa / tmpb;
		  ap[0] = ((unsigned long)res) & ~sign_mask;
		  vala.setarray(0, wid, ap);
	    }
	    delete[]ap;
	    delete[]bp;
	    return true;
      }

	// We need to the actual division to positive integers. Make
	// them positive here, and remember the negations.
      bool negate_flag = false;
      if ( ((long) ap[words-1]) < 0 ) {
	    negate_flag = true;
	    negate_words(ap, words);
      }
      if ( ((long) bp[words-1]) < 0 ) {
	    negate_flag ^= true;
	    negate_words(bp, words);
      }

      unsigned long*result = divide_bits(ap, bp, wid);
      if (result == 0) {
	    delete[]ap;
	    delete[]bp;
	    vvp_vector4_t tmp(wid, BIT4_X);
	    vala = tmp;
	    return true;
      }

      if (negate_flag) {
	    negate_words(result, words);
      }

      result[words-1] &= ~sign_mask;

      vala.setarray(0, wid, result);
      delete[]ap;
      delete[]bp;
      delete[]result;
      return true;
}

bool of_DIV_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(l / r);

      return true;
}

/*
 * %dup/obj
 * %dup/real
 * %dup/vec4
 *
 * Push a duplicate of the object on the appropriate stack.
 */
bool of_DUP_OBJ(vthread_t thr, vvp_code_t)
{
      vvp_object_t src = thr->peek_object();

        // If it is null push a new null object
      if (src.test_nil())
	    thr->push_object(vvp_object_t());
      else
	    thr->push_object(src.duplicate());

      return true;
}

bool of_DUP_REAL(vthread_t thr, vvp_code_t)
{
      thr->push_real(thr->peek_real(0));
      return true;
}

bool of_DUP_VEC4(vthread_t thr, vvp_code_t)
{
      thr->push_vec4(thr->peek_vec4(0));
      return true;
}

/*
 * This terminates the current thread. If there is a parent who is
 * waiting for me to die, then I schedule it. At any rate, I mark
 * myself as a zombie by setting my pc to 0.
 */
bool of_END(vthread_t thr, vvp_code_t)
{
      assert(! thr->waiting_for_event);
      thr->i_have_ended = 1;
      thr->pc = codespace_null();

	/* Fully detach any detached children. */
      while (! thr->detached_children.empty()) {
	    vthread_t child = *(thr->detached_children.begin());
	    assert(child);
	    assert(child->parent == thr);
	    assert(child->i_am_detached);
	    child->parent = 0;
	    child->i_am_detached = 0;
	    thr->detached_children.erase(thr->detached_children.begin());
      }

	/* It is an error to still have active children running at this
	 * point in time. They should have all been detached or joined. */
      assert(thr->children.empty());

	/* If I have a parent who is waiting for me, then mark that I
	   have ended, and schedule that parent. Also, finish the
	   %join for the parent. */
      if (!thr->i_am_detached && thr->parent && thr->parent->i_am_joining) {
	    vthread_t tmp = thr->parent;
	    assert(! thr->i_am_detached);

	    tmp->i_am_joining = 0;
	    schedule_vthread(tmp, 0, true);
	    do_join(tmp, thr);
	    return false;
      }

	/* If this thread is not fully detached then remove it from the
	 * parents detached_children set and reap it. */
      if (thr->i_am_detached) {
	    vthread_t tmp = thr->parent;
	    assert(tmp);
	    size_t res = tmp->detached_children.erase(thr);
	    assert(res == 1);
	      /* If the parent is waiting for the detached children to
	       * finish then the last detached child needs to tell the
	       * parent to wake up when it is finished. */
	    if (tmp->i_am_waiting && tmp->detached_children.empty()) {
		  tmp->i_am_waiting = 0;
		  schedule_vthread(tmp, 0, true);
	    }
	      /* Fully detach this thread so it will be reaped below. */
	    thr->i_am_detached = 0;
	    thr->parent = 0;
      }

	/* If I have no parent, then no one can %join me and there is
	 * no reason to stick around. This can happen, for example if
	 * I am an ``initial'' thread. */
      if (thr->parent == 0) {
	    vthread_reap(thr);
	    return false;
      }

	/* If I make it this far, then I have a parent who may wish
	   to %join me. Remain a zombie so that it can. */

      return false;
}

/*
 * %event <var-label>
 */
bool of_EVENT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr (cp->net, 0);
      vvp_vector4_t tmp (1, BIT4_X);
      vvp_send_vec4(ptr, tmp, thr->wt_context);
      return true;
}

/*
 * %event/nb <var-label>, <delay>
 */
bool of_EVENT_NB(vthread_t thr, vvp_code_t cp)
{
      vvp_time64_t delay;

      delay = thr->words[cp->bit_idx[0]].w_uint;
      schedule_propagate_event(cp->net, delay);
      return true;
}

bool of_EVCTL(vthread_t thr, vvp_code_t cp)
{
      assert(thr->event == 0 && thr->ecount == 0);
      thr->event = cp->net;
      thr->ecount = thr->words[cp->bit_idx[0]].w_uint;
      return true;
}
bool of_EVCTLC(vthread_t thr, vvp_code_t)
{
      thr->event = 0;
      thr->ecount = 0;
      return true;
}

bool of_EVCTLI(vthread_t thr, vvp_code_t cp)
{
      assert(thr->event == 0 && thr->ecount == 0);
      thr->event = cp->net;
      thr->ecount = cp->bit_idx[0];
      return true;
}

bool of_EVCTLS(vthread_t thr, vvp_code_t cp)
{
      assert(thr->event == 0 && thr->ecount == 0);
      thr->event = cp->net;
      int64_t val = thr->words[cp->bit_idx[0]].w_int;
      if (val < 0) val = 0;
      thr->ecount = val;
      return true;
}

bool of_FLAG_GET_VEC4(vthread_t thr, vvp_code_t cp)
{
      int flag = cp->number;
      assert(flag < vthread_s::FLAGS_COUNT);

      vvp_vector4_t val (1, thr->flags[flag]);
      thr->push_vec4(val);

      return true;
}

/*
 * %flag_inv <flag1>
 */
bool of_FLAG_INV(vthread_t thr, vvp_code_t cp)
{
      int flag1 = cp->bit_idx[0];

      thr->flags[flag1] = ~ thr->flags[flag1];
      return true;
}

/*
 * %flag_mov <flag1>, <flag2>
 */
bool of_FLAG_MOV(vthread_t thr, vvp_code_t cp)
{
      int flag1 = cp->bit_idx[0];
      int flag2 = cp->bit_idx[1];

      thr->flags[flag1] = thr->flags[flag2];
      return true;
}

/*
 * %flag_or <flag1>, <flag2>
 */
bool of_FLAG_OR(vthread_t thr, vvp_code_t cp)
{
      int flag1 = cp->bit_idx[0];
      int flag2 = cp->bit_idx[1];

      thr->flags[flag1] = thr->flags[flag1] | thr->flags[flag2];
      return true;
}

bool of_FLAG_SET_IMM(vthread_t thr, vvp_code_t cp)
{
      int flag = cp->number;
      int vali = cp->bit_idx[0];

      assert(flag < vthread_s::FLAGS_COUNT);
      assert(vali >= 0 && vali < 4);

      static const vvp_bit4_t map_bit[4] = {BIT4_0, BIT4_1, BIT4_Z, BIT4_X};
      thr->flags[flag] = map_bit[vali];
      return true;
}

bool of_FLAG_SET_VEC4(vthread_t thr, vvp_code_t cp)
{
      int flag = cp->number;
      assert(flag < vthread_s::FLAGS_COUNT);

      const vvp_vector4_t&val = thr->peek_vec4();
      thr->flags[flag] = val.value(0);
      thr->pop_vec4(1);

      return true;
}

/*
 * the %force/link instruction connects a source node to a
 * destination node. The destination node must be a signal, as it is
 * marked with the source of the force so that it may later be
 * unlinked without specifically knowing the source that this
 * instruction used.
 */
bool of_FORCE_LINK(vthread_t, vvp_code_t cp)
{
      vvp_net_t*dst = cp->net;
      vvp_net_t*src = cp->net2;

      assert(dst->fil);
      dst->fil->force_link(dst, src);

      return true;
}

/*
 * The %force/vec4 instruction invokes a force assign of a constant value
 * to a signal. The instruction arguments are:
 *
 *     %force/vec4 <net> ;
 *
 * where the <net> is the net label assembled into a vvp_net pointer,
 * and the value to be forced is popped from the vec4 stack.\.
 *
 * The instruction writes a vvp_vector4_t value to port-2 of the
 * target signal.
 */
bool of_FORCE_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_vector4_t value = thr->pop_vec4();

	/* Send the force value to the filter on the node. */

      assert(net->fil);
      if (value.size() != net->fil->filter_size())
	    value = coerce_to_width(value, net->fil->filter_size());

      net->force_vec4(value, vvp_vector2_t(vvp_vector2_t::FILL1, net->fil->filter_size()));

      return true;
}

/*
 * %force/vec4/off <net>, <off>
 */
bool of_FORCE_VEC4_OFF(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned base_idx = cp->bit_idx[0];
      long base = thr->words[base_idx].w_int;
      vvp_vector4_t value = thr->pop_vec4();
      unsigned wid = value.size();

      assert(net->fil);

      if (thr->flags[4] == BIT4_1)
	    return true;

	// This is the width of the target vector.
      unsigned use_size = net->fil->filter_size();

      if (base >= (long)use_size)
	    return true;
      if (base < -(long)use_size)
	    return true;

      if ((base + wid) > use_size)
	    wid = use_size - base;

	// Make a mask of which bits are to be forced, 0 for unforced
	// bits and 1 for forced bits.
      vvp_vector2_t mask (vvp_vector2_t::FILL0, use_size);
      for (unsigned idx = 0 ; idx < wid ; idx += 1)
	    mask.set_bit(base+idx, 1);

      vvp_vector4_t tmp (use_size, BIT4_Z);

	// vvp_net_t::force_vec4 propagates all the bits of the
	// forced vector value, regardless of the mask. This
	// ensures the unforced bits retain their current value.
      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*>(net->fil);
      assert(sig);
      sig->vec4_value(tmp);

      tmp.set_vec(base, value);

      net->force_vec4(tmp, mask);
      return true;
}

/*
 * %force/vec4/off/d <net>, <off>, <del>
 */
bool of_FORCE_VEC4_OFF_D(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      unsigned base_idx = cp->bit_idx[0];
      long base = thr->words[base_idx].w_int;

      unsigned delay_idx = cp->bit_idx[1];
      vvp_time64_t delay = thr->words[delay_idx].w_uint;

      vvp_vector4_t value = thr->pop_vec4();

      assert(net->fil);

      if (thr->flags[4] == BIT4_1)
	    return true;

	// This is the width of the target vector.
      unsigned use_size = net->fil->filter_size();

      if (base >= (long)use_size)
	    return true;
      if (base < -(long)use_size)
	    return true;

      schedule_force_vector(net, base, use_size, value, delay);
      return true;
}

bool of_FORCE_WR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net  = cp->net;
      double value = thr->pop_real();

      net->force_real(value, vvp_vector2_t(vvp_vector2_t::FILL1, 1));

      return true;
}

/*
 * The %fork instruction causes a new child to be created and pushed
 * in front of any existing child. This causes the new child to be
 * added to the list of children, and for me to be the parent of the
 * new child.
 */
bool of_FORK(vthread_t thr, vvp_code_t cp)
{
      vthread_t child = vthread_new(cp->cptr2, cp->scope);
      child->i_am_forked_task = 1;  // Mark as forked (not called) - affects context management

      if (cp->scope->is_automatic()) {
              /* The context allocated for this child is the top entry
                 on the write context stack. */
            child->wt_context = thr->wt_context;
            child->rd_context = thr->wt_context;

            // Store '@' (implicit this) for context-independent access.
            // Find '@' variable in the scope and store its net and value.
            vvp_context_t wt_ctx = thr->wt_context;
            for (unsigned idx = 0; idx < cp->scope->intern.size(); ++idx) {
                  vpiHandle item = cp->scope->intern[idx];
                  if (!item) continue;
                  if (item->get_type_code() != vpiClassVar) continue;
                  const char* name = item->vpi_get_str(vpiName);
                  if (!name || strcmp(name, "@") != 0) continue;

                  __vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
                  if (!var) continue;
                  vvp_net_t*net = var->get_net();
                  if (!net || !net->fun) continue;

                  vvp_fun_signal_object_aa*fun_aa =
                        dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
                  if (fun_aa && wt_ctx) {
                        child->fork_this_net_ = net;
                        child->fork_this_obj_ = fun_aa->get_object_from_context(wt_ctx);
                  }
                  break;
            }
      }

      // Propagate fork_this from parent if this is a nested fork
      if (child->fork_this_net_ == 0 && thr->fork_this_net_ != 0) {
            child->fork_this_net_ = thr->fork_this_net_;
            if (!thr->fork_this_obj_.test_nil()) {
                  child->fork_this_obj_ = thr->fork_this_obj_;
            } else if (thr->wt_context) {
                  vvp_fun_signal_object_aa*fun_aa =
                        dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
                  if (fun_aa) {
                        child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
                  }
            }
      }

      child->parent = thr;
      thr->children.insert(child);

      if (thr->i_am_in_function) {
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;
      } else {
	    schedule_vthread(child, 0, true);
      }
      return true;
}

/*
 * %fork/virt <method_name>, <base_code>, <base_scope>
 * Virtual task call: look up the method in the object's actual class type
 * and fork to that method. Similar to %callf/virt but for tasks.
 */
bool of_FORK_VIRT(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*base_scope = cp->scope;
      if (!base_scope) {
	    // No scope - fall back to regular fork
	    vthread_t child = vthread_new(cp->cptr2, cp->scope);
	    child->i_am_forked_task = 1;  // Mark as forked task
	    child->parent = thr;
	    thr->children.insert(child);
	    if (thr->i_am_in_function) {
		  child->is_scheduled = 1;
		  child->i_am_in_function = 1;
		  vthread_run(child);
		  running_thread = thr;
	    } else {
		  schedule_vthread(child, 0, true);
	    }
	    return true;
      }

      // Get the method name from the scope's basename
      const char*method_name = base_scope->scope_name();
      if (!method_name) method_name = "unknown";

      // Find the '@' (this) variable in the base scope and get the object from it
      vvp_object_t obj;
      bool found_this = false;

      // Get the write context - this is where the '@' parameter was stored
      // by %store/obj before this %fork/virt call. The context-based lookup
      // takes priority because for nested calls like child.run(), the @ was
      // explicitly set up in the context.
      vvp_context_t wt_ctx = vthread_get_wt_context();

      // First try to get @ from the context (this handles nested task calls
      // where the target object was explicitly stored before the fork)
      for (unsigned idx = 0; idx < base_scope->intern.size(); ++idx) {
	    vpiHandle item = base_scope->intern[idx];
	    if (!item) continue;
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name = item->vpi_get_str(vpiName);
		  if (name && strcmp(name, "@") == 0) {
			__vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t*net = var->get_net();
			      if (net && net->fun) {
				    vvp_fun_signal_object_aa*fun_aa =
					  dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
				    if (fun_aa && wt_ctx) {
					  obj = fun_aa->get_object_from_context(wt_ctx);
					  if (!obj.test_nil()) {
						found_this = true;
					  }
				    }
				    if (!found_this) {
					  vvp_fun_signal_object*fun =
						dynamic_cast<vvp_fun_signal_object*>(net->fun);
					  if (fun) {
						obj = fun->get_object();
						if (!obj.test_nil()) {
						      found_this = true;
						}
					  }
				    }
			      }
			}
			break;
		  }
	    }
      }

      // Fall back to fork_this if we didn't find @ in the context
      // (this handles the case where we're in a forked task chain)
      if (!found_this && thr->fork_this_net_ != 0 && !thr->fork_this_obj_.test_nil()) {
	    obj = thr->fork_this_obj_;
	    found_this = true;
      }

      // Get target code and scope for the method call
      vvp_code_t target_code = cp->cptr2;
      __vpiScope*target_scope = base_scope;

      // If we found 'this', try to do virtual dispatch and validate the object
      // The validation is critical: we need to ensure the object's method matches
      // the intended method. In UVM, both sequence and sequencer have wait_for_grant,
      // but they're different methods. We validate by checking if the object's method
      // entry point is compatible (same method or override in same class hierarchy).
      bool valid_this = false;
      if (found_this && !obj.test_nil()) {
	    vvp_cobject*cobj = obj.peek<vvp_cobject>();
	    if (cobj) {
		  const class_type*actual_class = cobj->get_class_type();
		  if (actual_class) {
			const class_type::method_info*method = actual_class->get_method(method_name);
			if (method && method->entry) {
			      // Check if this method is the one we're supposed to call.
			      // The base_scope tells us which class's method we want.
			      // If the object's class is in the same hierarchy as base_scope's class,
			      // then the method is valid.
			      bool method_is_compatible = false;

			      // Get the class that base_scope belongs to
			      // The base_scope is the method scope (e.g., Base.run),
			      // so we need to get the parent which is the class scope (e.g., Base)
			      const char* base_scope_class_name = 0;
			      __vpiScope*class_scope = base_scope->scope;
			      if (class_scope) {
				    base_scope_class_name = class_scope->scope_def_name();
			      }

			      // Simple check: if the base scope's method entry matches the object's,
			      // or if the base scope's class name is in the object's class hierarchy
			      if (method->entry == cp->cptr2) {
				    // Same entry point - definitely the right method
				    method_is_compatible = true;
			      } else if (base_scope_class_name) {
				    // Check if actual_class inherits from base_scope's class
				    const class_type*check = actual_class;
				    while (check != 0) {
					  if (check->class_name() == base_scope_class_name) {
						// Found the base class - method is compatible
						method_is_compatible = true;
						break;
					  }
					  check = check->get_parent();
				    }
			      }

			      if (method_is_compatible) {
				    target_code = method->entry;
				    target_scope = method->scope;
				    valid_this = true;
			      } else {
				    // Object has method but it's from a different class hierarchy
				    found_this = false;
			      }
			} else {
			      // Object doesn't have this method - wrong object type!
			      found_this = false;
			}
		  }
	    }
      }

      // If context-based lookup returned wrong object type, try object stack
      if (!found_this && thr->has_objects()) {
	    // Check if there's an object on the stack that has the method
	    vvp_object_t&stack_obj = thr->peek_object();
	    vvp_cobject*cobj = stack_obj.peek<vvp_cobject>();
	    if (cobj) {
		  const class_type*actual_class = cobj->get_class_type();
		  if (actual_class) {
			const class_type::method_info*method = actual_class->get_method(method_name);
			if (method && method->entry) {
			      obj = stack_obj;
			      thr->pop_object(1);  // Remove from stack since we're using it
			      target_code = method->entry;
			      target_scope = method->scope;
			      found_this = true;
			      valid_this = true;
			}
		  }
	    }
      }

      // Final validation: ensure obj is used only if it's the valid this
      if (found_this && !valid_this) {
	    // We found something but it's not a valid this - don't use it
	    obj.reset();
      }

      // Create child thread with resolved method
      vthread_t child = vthread_new(target_code, target_scope);
      child->i_am_forked_task = 1;  // Mark as forked (not called) - affects context management

      if (target_scope && target_scope->is_automatic()) {
	    // If virtual dispatch changed the scope, we need a NEW context
	    // for the new scope, not the parent's context which was allocated
	    // for a potentially different scope layout.
	    if (target_scope != base_scope) {
		  // Allocate new context for the virtual dispatch target scope
		  vvp_context_t new_context = vthread_alloc_context(target_scope);
		  child->wt_context = new_context;
		  child->rd_context = new_context;

		  // Copy all matching parameters from base scope context to target scope context
		  // Parameters are identified by having the same name in both scopes
		  vvp_context_t base_ctx = wt_ctx; // Current write context has base scope's values
		  bool found_at_fork = false;
		  for (unsigned base_idx = 0; base_idx < base_scope->intern.size(); ++base_idx) {
			vpiHandle base_item = base_scope->intern[base_idx];
			if (!base_item) continue;
			int base_type = base_item->get_type_code();
			const char* base_name_tmp = base_item->vpi_get_str(vpiName);
			if (!base_name_tmp) continue;
			// Copy to string to avoid buffer reuse by subsequent vpi_get_str calls
			std::string base_name_str(base_name_tmp);
			const char* base_name = base_name_str.c_str();

			// Handle class object variables
			if (base_type == vpiClassVar) {
			      __vpiBaseVar*base_var = dynamic_cast<__vpiBaseVar*>(base_item);
			      if (!base_var) continue;
			      vvp_net_t*base_net = base_var->get_net();
			      if (!base_net || !base_net->fun) continue;
			      vvp_fun_signal_object_aa*base_fun =
				    dynamic_cast<vvp_fun_signal_object_aa*>(base_net->fun);
			      if (!base_fun) continue;

			      // Get value from base context
			      vvp_object_t val = base_fun->get_object_from_context(base_ctx);

			      // Debug: trace ALL class variables being copied
			      // fprintf(stderr, "DEBUG FORK_VIRT param: base=%s target=%s name=%s val.nil=%d idx=%u ctx=%p\n",
			// (debug removed)

			      // Track if we found @
			      if (strcmp(base_name, "@") == 0) {
				    found_at_fork = true;
			      }

			      if (val.test_nil()) continue;

			      // Find matching variable in target scope
			      for (unsigned tgt_idx = 0; tgt_idx < target_scope->intern.size(); ++tgt_idx) {
				    vpiHandle tgt_item = target_scope->intern[tgt_idx];
				    if (!tgt_item) continue;
				    if (tgt_item->get_type_code() != vpiClassVar) continue;
				    const char* tgt_name = tgt_item->vpi_get_str(vpiName);
				    if (!tgt_name || strcmp(base_name, tgt_name) != 0) continue;

				    __vpiBaseVar*tgt_var = dynamic_cast<__vpiBaseVar*>(tgt_item);
				    if (!tgt_var) continue;
				    vvp_net_t*tgt_net = tgt_var->get_net();
				    if (!tgt_net || !tgt_net->fun) continue;
				    vvp_fun_signal_object_aa*tgt_fun =
					  dynamic_cast<vvp_fun_signal_object_aa*>(tgt_net->fun);
				    if (!tgt_fun) continue;

				    // Copy value to target context
				    tgt_fun->set_object_in_context(new_context, val);
				    break;
			      }
			}
		  }
		  if (!found_at_fork) {
			// fprintf(stderr, "DEBUG FORK_VIRT: WARNING @ not found in base=%s\n",
			// (debug removed)
		  }

		  // Store '@' (implicit this) in child thread for context-independent access.
		  // Find the '@' variable in the TARGET scope and store its net pointer.
		  for (unsigned tgt_idx = 0; tgt_idx < target_scope->intern.size(); ++tgt_idx) {
			vpiHandle tgt_item = target_scope->intern[tgt_idx];
			if (!tgt_item) continue;
			if (tgt_item->get_type_code() != vpiClassVar) continue;
			const char* tgt_name = tgt_item->vpi_get_str(vpiName);
			if (!tgt_name || strcmp(tgt_name, "@") != 0) continue;

			__vpiBaseVar*tgt_var = dynamic_cast<__vpiBaseVar*>(tgt_item);
			if (!tgt_var) continue;
			vvp_net_t*tgt_net = tgt_var->get_net();
			if (tgt_net) {
			      child->fork_this_net_ = tgt_net;
			      child->fork_this_obj_ = obj;  // Store the '@' value
			}
			break;
		  }
	    } else {
		  // Same scope - use the context that was already allocated by %alloc
		  // and has all parameters stored via %store/obj before this fork.
		  // Don't allocate a new context - the existing wt_context is correct.
		  child->wt_context = thr->wt_context;
		  child->rd_context = thr->wt_context;
		  // fprintf(stderr, "DEBUG FORK_VIRT same_scope: using existing ctx=%p\n", thr->wt_context);

		  // Store '@' (implicit this) in child thread for context-independent access.
		  // Find the '@' variable in the base scope and store its net pointer.
		  for (unsigned idx = 0; idx < base_scope->intern.size(); ++idx) {
			vpiHandle item = base_scope->intern[idx];
			if (!item) continue;
			if (item->get_type_code() != vpiClassVar) continue;
			const char* name = item->vpi_get_str(vpiName);
			if (!name || strcmp(name, "@") != 0) continue;

			__vpiBaseVar*var = dynamic_cast<__vpiBaseVar*>(item);
			if (!var) continue;
			vvp_net_t*net = var->get_net();
			if (net) {
			      child->fork_this_net_ = net;
			      child->fork_this_obj_ = obj;  // Store the '@' value
			}
			break;
		  }
	    }
      }

      child->parent = thr;
      thr->children.insert(child);

      if (thr->i_am_in_function) {
	    child->is_scheduled = 1;
	    child->i_am_in_function = 1;
	    vthread_run(child);
	    running_thread = thr;
      } else {
	    schedule_vthread(child, 0, true);
      }
      return true;
}

bool of_FREE(vthread_t thr, vvp_code_t cp)
{
        /* Pop the child context from the read context stack. */
      vvp_context_t child_context = thr->rd_context;
      thr->rd_context = vvp_get_stacked_context(child_context);

        /* Free the context. */
      vthread_free_context(child_context, cp->scope);

      return true;
}

/*
 * %inv
 *
 * Logically, this pops a value, inverts is (Verilog style, with Z and
 * X converted to X) and pushes the result. We can more efficiently
 * just to the invert in place.
 */
bool of_INV(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t&val = thr->peek_vec4();
      val.invert();
      return true;
}


/*
 * Index registers, arithmetic.
 */

static inline int64_t get_as_64_bit(uint32_t low_32, uint32_t high_32)
{
      int64_t low = low_32;
      int64_t res = high_32;

      res <<= 32;
      res |= low;
      return res;
}

bool of_IX_ADD(vthread_t thr, vvp_code_t cp)
{
      thr->words[cp->number].w_int += get_as_64_bit(cp->bit_idx[0],
                                                    cp->bit_idx[1]);
      return true;
}

bool of_IX_SUB(vthread_t thr, vvp_code_t cp)
{
      thr->words[cp->number].w_int -= get_as_64_bit(cp->bit_idx[0],
                                                    cp->bit_idx[1]);
      return true;
}

bool of_IX_MUL(vthread_t thr, vvp_code_t cp)
{
      thr->words[cp->number].w_int *= get_as_64_bit(cp->bit_idx[0],
                                                    cp->bit_idx[1]);
      return true;
}

bool of_IX_LOAD(vthread_t thr, vvp_code_t cp)
{
      thr->words[cp->number].w_int = get_as_64_bit(cp->bit_idx[0],
                                                   cp->bit_idx[1]);
      return true;
}

bool of_IX_MOV(vthread_t thr, vvp_code_t cp)
{
      thr->words[cp->bit_idx[0]].w_int = thr->words[cp->bit_idx[1]].w_int;
      return true;
}

bool of_IX_GETV(vthread_t thr, vvp_code_t cp)
{
      unsigned index = cp->bit_idx[0];
      vvp_net_t*net = cp->net;

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*>(net->fil);
      if (sig == 0) {
	    assert(net->fil);
	    cerr << thr->get_fileline()
	         << "%%ix/getv error: Net arg not a vector signal? "
		 << typeid(*net->fil).name() << endl;
      }
      assert(sig);

      vvp_vector4_t vec;
      sig->vec4_value(vec);
      bool overflow_flag;
      uint64_t val;
      bool known_flag = vector4_to_value(vec, overflow_flag, val);

      if (known_flag)
	    thr->words[index].w_uint = val;
      else
	    thr->words[index].w_uint = 0;

	/* Set bit 4 as a flag if the input is unknown. */
      thr->flags[4] = known_flag ? (overflow_flag ? BIT4_X : BIT4_0) : BIT4_1;

      return true;
}

bool of_IX_GETV_S(vthread_t thr, vvp_code_t cp)
{
      unsigned index = cp->bit_idx[0];
      vvp_net_t*net = cp->net;

      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*>(net->fil);
      if (sig == 0) {
	    assert(net->fil);
	    cerr << thr->get_fileline()
	         << "%%ix/getv/s error: Net arg not a vector signal? "
		 << "fun=" << typeid(*net->fil).name()
		 << ", fil=" << (net->fil? typeid(*net->fil).name() : "<>")
		 << endl;
      }
      assert(sig);

      vvp_vector4_t vec;
      sig->vec4_value(vec);
      int64_t val;
      bool known_flag = vector4_to_value(vec, val, true, true);

      if (known_flag)
	    thr->words[index].w_int = val;
      else
	    thr->words[index].w_int = 0;

	/* Set bit 4 as a flag if the input is unknown. */
      thr->flags[4] = known_flag? BIT4_0 : BIT4_1;

      return true;
}

static uint64_t vec4_to_index(vthread_t thr, bool signed_flag)
{
	// Get all the information we need about the vec4 vector, then
	// pop it away. We only need the bool bits and the length.
      const vvp_vector4_t&val = thr->peek_vec4();
      unsigned val_size = val.size();
      unsigned long*bits = val.subarray(0, val_size, false);
      thr->pop_vec4(1);

	// If there are X/Z bits, then the subarray will give us a nil
	// pointer. Set a flag to indicate the error, and give up.
      if (bits == 0) {
	    thr->flags[4] = BIT4_1;
	    return 0;
      }

      uint64_t v = 0;
      thr->flags[4] = BIT4_0;

      assert(sizeof(bits[0]) <= sizeof(v));

      v = 0;
      for (unsigned idx = 0 ; idx < val_size ; idx += 8*sizeof(bits[0])) {
	    uint64_t tmp = bits[idx/8/sizeof(bits[0])];
	    if (idx < 8*sizeof(v)) {
		  v |= tmp << idx;
	    } else {
		  bool overflow = signed_flag && (v >> 63) ? ~tmp != 0 : tmp != 0;
		  if (overflow) {
			thr->flags[4] = BIT4_X;
			break;
		  }
	    }
      }

	// Set the high bits that are not necessarily filled in by the
	// subarray function.
      if (val_size < 8*sizeof(v)) {
	    if (signed_flag && (v & (static_cast<uint64_t>(1)<<(val_size-1)))) {
		    // Propagate the sign bit...
		  v |= (~static_cast<uint64_t>(0)) << val_size;

	    } else {
		    // Fill with zeros.
		  v &= ~((~static_cast<uint64_t>(0)) << val_size);
	    }

      }

      delete[]bits;
      return v;
}

/*
 * %ix/vec4 <idx>
 */
bool of_IX_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned use_idx = cp->number;
      thr->words[use_idx].w_uint = vec4_to_index(thr, false);
      return true;
}

/*
 * %ix/vec4/s <idx>
 */
bool of_IX_VEC4_S(vthread_t thr, vvp_code_t cp)
{
      unsigned use_idx = cp->number;
      thr->words[use_idx].w_uint = vec4_to_index(thr, true);
      return true;
}

/*
 * The various JMP instruction work simply by pulling the new program
 * counter from the instruction and resuming. If the jump is
 * conditional, then test the bit for the expected value first.
 */
bool of_JMP(vthread_t thr, vvp_code_t cp)
{
      thr->pc = cp->cptr;

	/* Normally, this returns true so that the processor just
	   keeps going to the next instruction. However, if there was
	   a $stop or vpiStop, returning false here can break the
	   simulation out of a hung loop. */
      if (schedule_stopped()) {
	    schedule_vthread(thr, 0, false);
	    return false;
      }

      return true;
}

/*
 * %jmp/0 <pc>, <flag>
 */
bool of_JMP0(vthread_t thr, vvp_code_t cp)
{
      if (thr->flags[cp->bit_idx[0]] == BIT4_0)
	    thr->pc = cp->cptr;

	/* Normally, this returns true so that the processor just
	   keeps going to the next instruction. However, if there was
	   a $stop or vpiStop, returning false here can break the
	   simulation out of a hung loop. */
      if (schedule_stopped()) {
	    schedule_vthread(thr, 0, false);
	    return false;
      }

      return true;
}

/*
 * %jmp/0xz <pc>, <flag>
 */
bool of_JMP0XZ(vthread_t thr, vvp_code_t cp)
{
      if (thr->flags[cp->bit_idx[0]] != BIT4_1)
	    thr->pc = cp->cptr;

	/* Normally, this returns true so that the processor just
	   keeps going to the next instruction. However, if there was
	   a $stop or vpiStop, returning false here can break the
	   simulation out of a hung loop. */
      if (schedule_stopped()) {
	    schedule_vthread(thr, 0, false);
	    return false;
      }

      return true;
}

/*
 * %jmp/1 <pc>, <flag>
 */
bool of_JMP1(vthread_t thr, vvp_code_t cp)
{
      if (thr->flags[cp->bit_idx[0]] == BIT4_1)
	    thr->pc = cp->cptr;

	/* Normally, this returns true so that the processor just
	   keeps going to the next instruction. However, if there was
	   a $stop or vpiStop, returning false here can break the
	   simulation out of a hung loop. */
      if (schedule_stopped()) {
	    schedule_vthread(thr, 0, false);
	    return false;
      }

      return true;
}

/*
 * %jmp/1xz <pc>, <flag>
 */
bool of_JMP1XZ(vthread_t thr, vvp_code_t cp)
{
      if (thr->flags[cp->bit_idx[0]] != BIT4_0)
	    thr->pc = cp->cptr;

	/* Normally, this returns true so that the processor just
	   keeps going to the next instruction. However, if there was
	   a $stop or vpiStop, returning false here can break the
	   simulation out of a hung loop. */
      if (schedule_stopped()) {
	    schedule_vthread(thr, 0, false);
	    return false;
      }

      return true;
}

/*
 * The %join instruction causes the thread to wait for one child
 * to die.  If a child is already dead (and a zombie) then I reap
 * it and go on. Otherwise, I mark myself as waiting in a join so that
 * children know to wake me when they finish.
 */

static void do_join(vthread_t thr, vthread_t child)
{
      assert(child->parent == thr);

        /* If the immediate child thread is in an automatic scope... */
      if (child->wt_context) {
            // Original context swap logic for function returns.
            // This swaps the function's context from wt_context to rd_context
            // so the caller can read return values.
            if (thr->wt_context != thr->rd_context) {
                    /* Pop the child context from the write context stack. */
                  vvp_context_t child_context = thr->wt_context;
                  thr->wt_context = vvp_get_stacked_context(child_context);

                    /* Push the child context onto the read context stack */
                  vvp_set_stacked_context(child_context, thr->rd_context);
                  thr->rd_context = child_context;
            }
      }

      vthread_reap(child);
}

static bool do_join_opcode(vthread_t thr)
{
      assert( !thr->i_am_joining );
      assert( !thr->children.empty());

	// Are there any children that have already ended? If so, then
	// join with that one.
      for (set<vthread_t>::iterator cur = thr->children.begin()
		 ; cur != thr->children.end() ; ++cur) {
	    vthread_t curp = *cur;
	    if (! curp->i_have_ended)
		  continue;

	      // found something!
	    do_join(thr, curp);
	    return true;
      }

	// Otherwise, tell my children to awaken me when they end,
	// then pause.
      thr->i_am_joining = 1;
      return false;
}

bool of_JOIN(vthread_t thr, vvp_code_t)
{
      return do_join_opcode(thr);
}

/*
 * This %join/detach <n> instruction causes the thread to detach
 * threads that were created by an earlier %fork.
 */
bool of_JOIN_DETACH(vthread_t thr, vvp_code_t cp)
{
      unsigned long count = cp->number;

      assert(count == thr->children.size());

      while (! thr->children.empty()) {
	    vthread_t child = *thr->children.begin();
	    assert(child->parent == thr);

	      // If the child shares the parent's automatic context, we need
	      // to allocate a separate context for the child. Otherwise,
	      // when the parent task completes and frees its context, the
	      // detached child would crash trying to access freed memory.
	    if (child->wt_context != 0 && thr->wt_context == child->wt_context) {
		  __vpiScope*child_scope = child->parent_scope;
		  if (child_scope && child_scope->is_automatic()) {
			// Allocate and copy context for the detached child
			vvp_context_t new_context = vthread_copy_context(child_scope, child->wt_context);
			child->wt_context = new_context;
			child->rd_context = new_context;
		  }
	    }
	    if (child->i_have_ended) {
		    // If the child has already ended, then reap it.
		  vthread_reap(child);

	    } else {
		  size_t res = child->parent->children.erase(child);
		  assert(res == 1);
		  child->i_am_detached = 1;
		  thr->detached_children.insert(child);
	    }
      }

      return true;
}

/*
 * %load/ar <array-label>, <index>;
*/
bool of_LOAD_AR(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      double word;

	/* The result is 0.0 if the address is undefined. */
      if (thr->flags[4] == BIT4_1) {
	    word = 0.0;
      } else {
	    unsigned adr = thr->words[idx].w_int;
	    word = cp->array->get_word_r(adr);
      }

      thr->push_real(word);
      return true;
}

template <typename ELEM>
static bool load_dar(vthread_t thr, vvp_code_t cp)
{
      int64_t adr = thr->words[3].w_int;
      vvp_net_t*net = cp->net;
      assert(net);

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();

      ELEM word;
      if (darray &&
          (adr >= 0) && (thr->flags[4] == BIT4_0)) // A defined address >= 0
	    darray->get_word(adr, word);
      else
	    dq_default(word, obj->size());

      vthread_push(thr, word);
      return true;
}

/*
 * %load/dar/r <array-label>;
 */
bool of_LOAD_DAR_R(vthread_t thr, vvp_code_t cp)
{
      return load_dar<double>(thr, cp);
}

/*
 * %load/dar/str <array-label>;
 */
bool of_LOAD_DAR_STR(vthread_t thr, vvp_code_t cp)
{
      return load_dar<string>(thr, cp);
}

/*
 * %load/dar/vec4 <array-label>;
 */
bool of_LOAD_DAR_VEC4(vthread_t thr, vvp_code_t cp)
{
      return load_dar<vvp_vector4_t>(thr, cp);
}

/*
 * %load/dar/o <array-label>;
 * Load an object from a darray/queue at the index in word register 3.
 */
bool of_LOAD_DAR_O(vthread_t thr, vvp_code_t cp)
{
      int64_t adr = thr->words[3].w_int;
      vvp_net_t*net = cp->net;
      assert(net);

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();

      vvp_object_t word;
      if (darray &&
          (adr >= 0) && (thr->flags[4] == BIT4_0)) // A defined address >= 0
	    darray->get_word(adr, word);
      // else word remains nil

      thr->push_object(word);
      return true;
}

/*
 * %load/obj <var-label>
 */
bool of_LOAD_OBJ(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      // Check if we're loading '@' (implicit this) and have a stored value.
      // This handles forked tasks where context swaps would otherwise cause
      // '@' to be inaccessible.
      //
      // IMPORTANT: Only use fork_this_obj_ when the net matches fork_this_net_
      // exactly. Do NOT use fork_this_obj_ for any '@' variable because nested
      // function calls (like constructors) have their own '@' which should be
      // loaded from the context, not from the forked task's '@'.
      if (thr->fork_this_net_ != 0 && !thr->fork_this_obj_.test_nil()) {
	    if (net == thr->fork_this_net_) {
		  thr->push_object(thr->fork_this_obj_);
		  return true;
	    }
	    // Note: Removed the overly broad net_is_this_variable check here.
	    // That check would incorrectly return fork_this_obj_ for a constructor's
	    // own '@' variable, causing the wrong class instance to be used.
      }

      vvp_fun_signal_object*fun = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(fun);

      vvp_object_t val = fun->get_object();

      thr->push_object(val);

      return true;
}

/*
 * %load/obja <index>
 *    Loads the object from array, using index <index> as the index
 *    value. If flags[4] == 1, the calculation of <index> may have
 *    failed, so push nil.
 */
bool of_LOAD_OBJA(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      vvp_object_t word;

	/* The result is 0.0 if the address is undefined. */
      if (thr->flags[4] == BIT4_1) {
	    ; // Return nil
      } else {
	    unsigned adr = thr->words[idx].w_int;
	    cp->array->get_word_obj(adr, word);
      }

      thr->push_object(word);
      return true;
}

/*
 * %load/scope <scope-label>
 *    Load a scope reference (for virtual interface assignment).
 *    The scope pointer is wrapped in a vvp_scope_ref object and
 *    pushed onto the object stack.
 */
bool of_LOAD_SCOPE(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*scope = cp->scope;
      vvp_object_t val(new vvp_scope_ref(scope));
      thr->push_object(val);
      return true;
}

/*
 * %load/real <var-label>
 */
bool of_LOAD_REAL(vthread_t thr, vvp_code_t cp)
{
      __vpiHandle*tmp = cp->handle;
      t_vpi_value val;

      val.format = vpiRealVal;
      vpi_get_value(tmp, &val);

      thr->push_real(val.value.real);

      return true;
}

/*
 * %load/str <var-label>
 */
bool of_LOAD_STR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;


      vvp_fun_signal_string*fun = dynamic_cast<vvp_fun_signal_string*> (net->fun);
      assert(fun);

      const string&val = fun->get_string();
      thr->push_str(val);

      return true;
}

bool of_LOAD_STRA(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      string word;

      if (thr->flags[4] == BIT4_1) {
	    word = "";
      } else {
	    unsigned adr = thr->words[idx].w_int;
	    word = cp->array->get_word_str(adr);
      }

      thr->push_str(word);
      return true;
}


/*
 * %load/vec4 <net>
 */
bool of_LOAD_VEC4(vthread_t thr, vvp_code_t cp)
{
	// Push a placeholder onto the stack in order to reserve the
	// stack space. Use a reference for the stack top as a target
	// for the load.
      thr->push_vec4(vvp_vector4_t());
      vvp_vector4_t&sig_value = thr->peek_vec4();

      vvp_net_t*net = cp->net;

	// For the %load to work, the functor must actually be a
	// signal functor. Only signals save their vector value.
      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (net->fil);
      if (sig == 0) {
	    cerr << thr->get_fileline()
	         << "%load/v error: Net arg not a signal? "
		 << (net->fil ? typeid(*net->fil).name() :
	                        typeid(*net->fun).name())
	         << endl;
	    assert(sig);
	    return true;
      }

	// Extract the value from the signal and directly into the
	// target stack position.
      sig->vec4_value(sig_value);

      return true;
}

/*
 * %load/vec4a <arr>, <adrx>
 */
bool of_LOAD_VEC4A(vthread_t thr, vvp_code_t cp)
{
      int adr_index = cp->bit_idx[0];

      long adr = thr->words[adr_index].w_int;

	// If flag[3] is set, then the calculation of the address
	// failed, and this load should return X instead of the actual
	// value.
      if (thr->flags[4] == BIT4_1) {
	    vvp_vector4_t tmp (cp->array->get_word_size(), BIT4_X);
	    thr->push_vec4(tmp);
	    return true;
      }

      vvp_vector4_t tmp (cp->array->get_word(adr));
      thr->push_vec4(tmp);
      return true;
}

static void do_verylong_mod(vvp_vector4_t&vala, const vvp_vector4_t&valb,
			    bool left_is_neg, bool right_is_neg)
{
      bool out_is_neg = left_is_neg;
      const int len=vala.size();
      unsigned char *a, *z, *t;
      a = new unsigned char[len+1];
      z = new unsigned char[len+1];
      t = new unsigned char[len+1];

      unsigned char carry;
      unsigned char temp;

      int mxa = -1, mxz = -1;
      int i;
      int current, copylen;

      unsigned lb_carry = left_is_neg? 1 : 0;
      unsigned rb_carry = right_is_neg? 1 : 0;
      for (int idx = 0 ;  idx < len ;  idx += 1) {
	    unsigned lb = vala.value(idx);
	    unsigned rb = valb.value(idx);

	    if ((lb | rb) & 2) {
		  delete []t;
		  delete []z;
		  delete []a;
		  vvp_vector4_t tmp(len, BIT4_X);
		  vala = tmp;
		  return;
	    }

	    if (left_is_neg) {
		  lb = (1-lb) + lb_carry;
		  lb_carry = (lb & ~1)? 1 : 0;
		  lb &= 1;
	    }
	    if (right_is_neg) {
		  rb = (1-rb) + rb_carry;
		  rb_carry = (rb & ~1)? 1 : 0;
		  rb &= 1;
	    }

	    z[idx]=lb;
	    a[idx]=1-rb;	// for 2s complement add..
      }

      z[len]=0;
      a[len]=1;

      for(i=len-1;i>=0;i--) {
	    if(! a[i]) {
		  mxa=i;
		  break;
	    }
      }

      for(i=len-1;i>=0;i--) {
	    if(z[i]) {
		  mxz=i;
		  break;
	    }
      }

      if((mxa>mxz)||(mxa==-1)) {
	    if(mxa==-1) {
		  delete []t;
		  delete []z;
		  delete []a;
		  vvp_vector4_t tmpx (len, BIT4_X);
		  vala = tmpx;
		  return;
	    }

	    goto tally;
      }

      copylen = mxa + 2;
      current = mxz - mxa;

      while(current > -1) {
	    carry = 1;
	    for(i=0;i<copylen;i++) {
		  temp = z[i+current] + a[i] + carry;
		  t[i] = (temp&1);
		  carry = (temp>>1);
	    }

	    if(carry) {
		  for(i=0;i<copylen;i++) {
			z[i+current] = t[i];
		  }
	    }

	    current--;
      }

 tally:

      vvp_vector4_t tmp (len, BIT4_X);
      carry = out_is_neg? 1 : 0;
      for (int idx = 0 ;  idx < len ;  idx += 1) {
	    unsigned ob = z[idx];
	    if (out_is_neg) {
		  ob = (1-ob) + carry;
		  carry = (ob & ~1)? 1 : 0;
		  ob = ob & 1;
	    }
	    tmp.set_bit(idx, ob?BIT4_1:BIT4_0);
      }
      vala = tmp;
      delete []t;
      delete []z;
      delete []a;
}

bool of_MAX_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      if (r != r)
	    thr->push_real(l);
      else if (l != l)
	    thr->push_real(r);
      else if (r < l)
	    thr->push_real(l);
      else
	    thr->push_real(r);
      return true;
}

bool of_MIN_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      if (r != r)
	    thr->push_real(l);
      else if (l != l)
	    thr->push_real(r);
      else if (r < l)
	    thr->push_real(r);
      else
	    thr->push_real(l);
      return true;
}

bool of_MOD(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t&vala = thr->peek_vec4();

      // Handle width mismatch by padding smaller operand to larger width
      unsigned wid_a = vala.size();
      unsigned wid_b = valb.size();
      unsigned wid = (wid_a > wid_b) ? wid_a : wid_b;
      if (wid_a < wid) vala.resize(wid, BIT4_0);
      if (wid_b < wid) valb.resize(wid, BIT4_0);

      if(wid <= 8*sizeof(unsigned long long)) {
	    unsigned long long lv = 0, rv = 0;

	    for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {
		  unsigned long long lb = vala.value(idx);
		  unsigned long long rb = valb.value(idx);

		  if ((lb | rb) & 2)
			goto x_out;

		  lv |= (unsigned long long) lb << idx;
		  rv |= (unsigned long long) rb << idx;
	    }

	    if (rv == 0)
		  goto x_out;

	    lv %= rv;

	    for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {
		  vala.set_bit(idx, (lv&1)?BIT4_1 : BIT4_0);
		  lv >>= 1;
	    }

	    return true;

      } else {
	    do_verylong_mod(vala, valb, false, false);
	    return true;
      }

 x_out:
      vala = vvp_vector4_t(wid, BIT4_X);
      return true;
}

/*
 * %mod/s
 */
bool of_MOD_S(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t&vala = thr->peek_vec4();

      // Handle width mismatch by padding smaller operand to larger width
      // For signed operations, we sign-extend the smaller operand
      unsigned wid_a = vala.size();
      unsigned wid_b = valb.size();
      unsigned wid = (wid_a > wid_b) ? wid_a : wid_b;
      vvp_bit4_t sign_a = (wid_a > 0) ? vala.value(wid_a - 1) : BIT4_0;
      vvp_bit4_t sign_b = (wid_b > 0) ? valb.value(wid_b - 1) : BIT4_0;
      if (wid_a < wid) vala.resize(wid, sign_a);
      if (wid_b < wid) valb.resize(wid, sign_b);

	/* Handle the case that we can fit the bits into a long-long
	   variable. We cause use native % to do the work. */
      if(wid <= 8*sizeof(long long)) {
	    long long lv = 0, rv = 0;

	    for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {
		  long long lb = vala.value(idx);
		  long long rb = valb.value(idx);

		  if ((lb | rb) & 2)
			goto x_out;

		  lv |= (long long) lb << idx;
		  rv |= (long long) rb << idx;
	    }

	    if (rv == 0)
		  goto x_out;

	    if ((lv == LLONG_MIN) && (rv == -1))
		  goto zero_out;

	      /* Sign extend the signed operands when needed. */
	    if (wid < 8*sizeof(long long)) {
		  if (lv & (1LL << (wid-1)))
			lv |= -1ULL << wid;
		  if (rv & (1LL << (wid-1)))
			rv |= -1ULL << wid;
	    }

	    lv %= rv;

	    for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {
		  vala.set_bit(idx, (lv&1)? BIT4_1 : BIT4_0);
		  lv >>= 1;
	    }

	      // vala is the top of the stack, edited in place, so we
	      // do not need to push the result.

	    return true;

      } else {

	    bool left_is_neg  = vala.value(vala.size()-1) == BIT4_1;
	    bool right_is_neg = valb.value(valb.size()-1) == BIT4_1;
	    do_verylong_mod(vala, valb, left_is_neg, right_is_neg);
	    return true;
      }

 x_out:
      vala = vvp_vector4_t(wid, BIT4_X);
      return true;
 zero_out:
      vala = vvp_vector4_t(wid, BIT4_0);
      return true;
}

/*
 * %mod/wr
 */
bool of_MOD_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(fmod(l,r));

      return true;
}

/*
 * %pad/s <wid>
 */
bool of_PAD_S(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      vvp_vector4_t&val = thr->peek_vec4();
      unsigned old_size = val.size();

	// Sign-extend.
      if (old_size < wid)
	    val.resize(wid, val.value(old_size-1));
      else
	    val.resize(wid);

      return true;
}

/*
 * %pad/u <wid>
 */
bool of_PAD_U(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      vvp_vector4_t&val = thr->peek_vec4();
      val.resize(wid, BIT4_0);

      return true;
}

/*
 * %part/s <wid>
 * %part/u <wid>
 * Two values are popped from the stack. First, pop the canonical
 * index of the part select, and second is the value to be
 * selected. The result is pushed back to the stack.
 */
static bool of_PART_base(vthread_t thr, vvp_code_t cp, bool signed_flag)
{
      unsigned wid = cp->number;

      vvp_vector4_t base4 = thr->pop_vec4();
      vvp_vector4_t&value = thr->peek_vec4();

      vvp_vector4_t res (wid, BIT4_X);

	// NOTE: This is treating the vector as signed. Is that correct?
      int32_t base;
      bool value_ok = vector4_to_value(base4, base, signed_flag);
      if (! value_ok) {
	    value = res;
	    return true;
      }

      if (base >= (int32_t)value.size()) {
	    value = res;
	    return true;
      }

      if ((base+(int)wid) <= 0) {
	    value = res;
	    return true;
      }

      long vbase = 0;
      if (base < 0) {
	    vbase = -base;
	    wid -= vbase;
	    base = 0;
      }

      if ((base+wid) > value.size()) {
	    wid = value.size() - base;
      }

      res .set_vec(vbase, value.subvalue(base, wid));
      value = res;

      return true;
}

bool of_PART_S(vthread_t thr, vvp_code_t cp)
{
      return of_PART_base(thr, cp, true);
}

bool of_PART_U(vthread_t thr, vvp_code_t cp)
{
      return of_PART_base(thr, cp, false);
}

/*
 * %parti/s <wid>, <basei>, <base_wid>
 * %parti/u <wid>, <basei>, <base_wid>
 *
 * Pop the value to be selected. The result is pushed back to the stack.
 */
static bool of_PARTI_base(vthread_t thr, vvp_code_t cp, bool signed_flag)
{
      unsigned wid = cp->number;
      uint32_t base = cp->bit_idx[0];
      uint32_t bwid = cp->bit_idx[1];

      vvp_vector4_t&value = thr->peek_vec4();

      vvp_vector4_t res (wid, BIT4_X);

	// NOTE: This is treating the vector as signed. Is that correct?
      int32_t use_base = base;
      if (signed_flag && bwid < 32 && (base&(1<<(bwid-1)))) {
	    use_base |= -1UL << bwid;
      }

      if (use_base >= (int32_t)value.size()) {
	    value = res;
	    return true;
      }

      if ((use_base+(int32_t)wid) <= 0) {
	    value = res;
	    return true;
      }

      long vbase = 0;
      if (use_base < 0) {
	    vbase = -use_base;
	    wid -= vbase;
	    use_base = 0;
      }

      if ((use_base+wid) > value.size()) {
	    wid = value.size() - use_base;
      }

      res .set_vec(vbase, value.subvalue(use_base, wid));
      value = res;

      return true;
}

bool of_PARTI_S(vthread_t thr, vvp_code_t cp)
{
      return of_PARTI_base(thr, cp, true);
}

bool of_PARTI_U(vthread_t thr, vvp_code_t cp)
{
      return of_PARTI_base(thr, cp, false);
}

/*
 * %mul
 */
bool of_MUL(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t r = thr->pop_vec4();
	// Rather then pop l, use it directly from the stack. When we
	// assign to 'l', that will edit the top of the stack, which
	// replaces a pop and a pull.
      vvp_vector4_t&l = thr->peek_vec4();

      l.mul(r);
      return true;
}

/*
 * %muli <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments, and push
 * the result.
 */
bool of_MULI(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      vvp_vector4_t&l = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t r (wid, BIT4_0);
      get_immediate_rval (cp, r);

      l.mul(r);
      return true;
}

bool of_MUL_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(l * r);

      return true;
}

bool of_NAND(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valr = thr->pop_vec4();
      vvp_vector4_t&vall = thr->peek_vec4();
      assert(vall.size() == valr.size());
      unsigned wid = vall.size();

      for (unsigned idx = 0 ; idx < wid ; idx += 1) {
	    vvp_bit4_t lb = vall.value(idx);
	    vvp_bit4_t rb = valr.value(idx);
	    vall.set_bit(idx, ~(lb&rb));
      }

      return true;
}

/*
 * %new/cobj <vpi_object>
 * This creates a new cobject (SystemVerilog class object) and pushes
 * it to the stack. The <vpi-object> is a __vpiHandle that is a
 * vpiClassDefn object that defines the item to be created.
 */
bool of_NEW_COBJ(vthread_t thr, vvp_code_t cp)
{
      const class_type*defn = dynamic_cast<const class_type*> (cp->handle);
      assert(defn);

      vvp_object_t tmp (new vvp_cobject(defn));
      thr->push_object(tmp);
      return true;
}

/*
 * %factory/type_override
 *
 * This opcode registers a type override with the factory.
 * The override_type is popped first, then the original_type.
 * When original_type is later created via %factory/create,
 * the factory will create override_type instead.
 */
bool of_FACTORY_TYPE_OVERRIDE(vthread_t thr, vvp_code_t)
{
      // Pop override type first (reverse order on stack)
      string override_type = thr->pop_str();
      string original_type = thr->pop_str();

      vvp_factory_registry::instance().set_type_override(original_type, override_type);
      return true;
}

/*
 * %factory/create
 *
 * This opcode creates a class object by looking up the class type name
 * in the UVM factory registry. The type name is popped from the string
 * stack, and the resulting object is pushed to the object stack.
 *
 * If a type override is registered for this type, the override type
 * is created instead. This enables UVM factory override patterns.
 *
 * If the class is not found in the factory, a null object is pushed
 * and an error message is displayed.
 */
bool of_FACTORY_CREATE(vthread_t thr, vvp_code_t)
{
      // Pop the type name from the string stack
      string type_name = thr->pop_str();

      // Look up the class in the factory registry WITH OVERRIDE SUPPORT
      // This checks for type overrides first
      class_type* defn = vvp_factory_registry::instance().find_class_with_override(type_name);
      if (defn == nullptr) {
	    vpi_printf("UVM_FATAL: Factory cannot find class '%s'\n",
		       type_name.c_str());
	    // Push null object
	    vvp_object_t null_obj;
	    thr->push_object(null_obj);
	    return true;
      }

      // Create the new object
      vvp_object_t tmp(new vvp_cobject(defn));

      // Look up the "new" method (constructor) for this class
      const class_type::method_info* ctor = defn->get_method("new");

      if (ctor == nullptr || ctor->entry == nullptr || ctor->scope == nullptr) {
	    // No constructor - just return the uninitialized object
	    thr->push_object(tmp);
	    return true;
      }

      // Allocate context for the constructor scope (automatic function)
      __vpiScope* ctor_scope = ctor->scope;
      vvp_context_t child_context = vthread_alloc_context(ctor_scope);

      // Push context onto write context stack
      vvp_set_stacked_context(child_context, thr->wt_context);
      thr->wt_context = child_context;

      // Find the '@' (this) variable in the constructor scope and store the object
      for (unsigned idx = 0; idx < ctor_scope->intern.size(); ++idx) {
	    vpiHandle item = ctor_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name = item->vpi_get_str(vpiName);
		  if (name && strcmp(name, "@") == 0) {
			__vpiBaseVar* var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t* net = var->get_net();
			      if (net) {
				    vvp_net_ptr_t ptr(net, 0);
				    vvp_send_object(ptr, tmp, child_context);
			      }
			}
			break;
		  }
	    }
      }

      // Create child thread to run the constructor
      vthread_t child = vthread_new(ctor->entry, ctor_scope);
      child->wt_context = child_context;
      child->rd_context = child_context;

      // Propagate fork_this from parent if parent has it set
      if (thr->fork_this_net_ != 0) {
	    child->fork_this_net_ = thr->fork_this_net_;
	    if (!thr->fork_this_obj_.test_nil()) {
		  child->fork_this_obj_ = thr->fork_this_obj_;
	    } else if (thr->wt_context) {
		  vvp_fun_signal_object_aa*fun_aa =
			dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
		  if (fun_aa) {
			child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
		  }
	    }
      }

      // Mark child as direct child of current thread
      child->parent = thr;
      thr->children.insert(child);

      // Execute the constructor
      assert(ctor_scope->get_type_code() == vpiFunction);
      child->is_scheduled = 1;
      child->i_am_in_function = 1;
      vthread_run(child);
      running_thread = thr;

      // Get the resulting object from the '@' variable
      vvp_object_t result;
      for (unsigned idx = 0; idx < ctor_scope->intern.size(); ++idx) {
	    vpiHandle item = ctor_scope->intern[idx];
	    if (item->get_type_code() == vpiClassVar) {
		  const char* name = item->vpi_get_str(vpiName);
		  if (name && strcmp(name, "@") == 0) {
			__vpiBaseVar* var = dynamic_cast<__vpiBaseVar*>(item);
			if (var) {
			      vvp_net_t* net = var->get_net();
			      if (net && net->fun) {
				    vvp_fun_signal_object_aa* fun_aa =
					  dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
				    if (fun_aa) {
					  result = fun_aa->get_object_from_context(child_context);
				    }
			      }
			}
			break;
		  }
	    }
      }

      // Pop the context
      thr->wt_context = vvp_get_stacked_context(child_context);

      // Free the context
      vthread_free_context(child_context, ctor_scope);

      // Join with child thread (vthread_reap will handle cleanup)
      if (child->i_have_ended) {
	    vthread_reap(child);
      }

      // Push the result
      if (result.test_nil()) {
	    thr->push_object(tmp);  // Fall back to original object
      } else {
	    thr->push_object(result);
      }
      return true;
}

bool of_NEW_DARRAY(vthread_t thr, vvp_code_t cp)
{
      const char*text = cp->text;
      size_t size = thr->words[cp->bit_idx[0]].w_int;
      unsigned word_wid;
      size_t n;

      vvp_object_t obj;
      if (strcmp(text,"b8") == 0) {
	    obj = new vvp_darray_atom<uint8_t>(size);
      } else if (strcmp(text,"b16") == 0) {
	    obj = new vvp_darray_atom<uint16_t>(size);
      } else if (strcmp(text,"b32") == 0) {
	    obj = new vvp_darray_atom<uint32_t>(size);
      } else if (strcmp(text,"b64") == 0) {
	    obj = new vvp_darray_atom<uint64_t>(size);
      } else if (strcmp(text,"sb8") == 0) {
	    obj = new vvp_darray_atom<int8_t>(size);
      } else if (strcmp(text,"sb16") == 0) {
	    obj = new vvp_darray_atom<int16_t>(size);
      } else if (strcmp(text,"sb32") == 0) {
	    obj = new vvp_darray_atom<int32_t>(size);
      } else if (strcmp(text,"sb64") == 0) {
	    obj = new vvp_darray_atom<int64_t>(size);
      } else if ((1 == sscanf(text, "b%u%zn", &word_wid, &n)) &&
                 (n == strlen(text))) {
	    obj = new vvp_darray_vec2(size, word_wid);
      } else if ((1 == sscanf(text, "sb%u%zn", &word_wid, &n)) &&
                 (n == strlen(text))) {
	    obj = new vvp_darray_vec2(size, word_wid);
      } else if ((1 == sscanf(text, "v%u%zn", &word_wid, &n)) &&
                 (n == strlen(text))) {
	    obj = new vvp_darray_vec4(size, word_wid);
      } else if ((1 == sscanf(text, "sv%u%zn", &word_wid, &n)) &&
                 (n == strlen(text))) {
	    obj = new vvp_darray_vec4(size, word_wid);
      } else if (strcmp(text,"r") == 0) {
	    obj = new vvp_darray_real(size);
      } else if (strcmp(text,"S") == 0) {
	    obj = new vvp_darray_string(size);
      } else if (strcmp(text,"o") == 0) {
	    obj = new vvp_darray_object(size);
      } else {
	    cerr << get_fileline()
	         << "Internal error: Unsupported dynamic array type: "
	         << text << "." << endl;
	    assert(0);
      }

      thr->push_object(obj);

      return true;
}

bool of_NOOP(vthread_t, vvp_code_t)
{
      return true;
}

/*
 * %nor/r
 */
bool of_NORR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_1;

      for (unsigned idx = 0 ;  idx < val.size() ;  idx += 1) {

	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_1) {
		  lb = BIT4_0;
		  break;
	    }

	    if (rb != BIT4_0)
		  lb = BIT4_X;
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);

      return true;
}

/*
 * Push a null to the object stack.
 */
bool of_NULL(vthread_t thr, vvp_code_t)
{
      vvp_object_t tmp;
      thr->push_object(tmp);
      return true;
}

/*
 * %and/r
 */
bool of_ANDR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_1;

      for (unsigned idx = 0 ; idx < val.size() ; idx += 1) {
	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_0) {
		  lb = BIT4_0;
		  break;
	    }

	    if (rb != 1)
		  lb = BIT4_X;
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);

      return true;
}

/*
 * %nand/r
 */
bool of_NANDR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_0;
      for (unsigned idx = 0 ; idx < val.size() ; idx += 1) {

	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_0) {
		  lb = BIT4_1;
		  break;
	    }

	    if (rb != BIT4_1)
		  lb = BIT4_X;
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);

      return true;
}

/*
 * %or/r
 */
bool of_ORR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_0;
      for (unsigned idx = 0 ; idx < val.size() ; idx += 1) {
	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_1) {
		  lb = BIT4_1;
		  break;
	    }

	    if (rb != BIT4_0)
		  lb = BIT4_X;
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);
      return true;
}

/*
 * %xor/r
 */
bool of_XORR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_0;
      for (unsigned idx = 0 ; idx < val.size() ; idx += 1) {

	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_1)
		  lb = ~lb;
	    else if (rb != BIT4_0) {
		  lb = BIT4_X;
		  break;
	    }
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);
      return true;
}

/*
 * %xnor/r
 */
bool of_XNORR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t val = thr->pop_vec4();

      vvp_bit4_t lb = BIT4_1;
      for (unsigned idx = 0 ; idx < val.size() ; idx += 1) {

	    vvp_bit4_t rb = val.value(idx);
	    if (rb == BIT4_1)
		  lb = ~lb;
	    else if (rb != BIT4_0) {
		  lb = BIT4_X;
		  break;
	    }
      }

      vvp_vector4_t res (1, lb);
      thr->push_vec4(res);
      return true;
}

/*
 * %or
 */
bool of_OR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t&vala = thr->peek_vec4();
      vala |= valb;
      return true;
}

/*
 * %nor
 */
bool of_NOR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valr = thr->pop_vec4();
      vvp_vector4_t&vall = thr->peek_vec4();
      assert(vall.size() == valr.size());
      unsigned wid = vall.size();

      for (unsigned idx = 0 ; idx < wid ; idx += 1) {
	    vvp_bit4_t lb = vall.value(idx);
	    vvp_bit4_t rb = valr.value(idx);
	    vall.set_bit(idx, ~(lb|rb));
      }

      return true;
}

/*
 * %pop/obj <num>, <skip>
 */
bool of_POP_OBJ(vthread_t thr, vvp_code_t cp)
{
      unsigned cnt = cp->bit_idx[0];
      unsigned skip = cp->bit_idx[1];

      thr->pop_object(cnt, skip);
      return true;
}

/*
 * %pop/real <number>
 */
bool of_POP_REAL(vthread_t thr, vvp_code_t cp)
{
      unsigned cnt = cp->number;
      thr->pop_real(cnt);
      return true;
}

/*
 *  %pop/str <number>
 */
bool of_POP_STR(vthread_t thr, vvp_code_t cp)
{
      unsigned cnt = cp->number;
      thr->pop_str(cnt);
      return true;
}

/*
 *  %pop/vec4 <number>
 */
bool of_POP_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned cnt = cp->number;
      thr->pop_vec4(cnt);
      return true;
}

/*
 * %pow
 * %pow/s
 */
static bool of_POW_base(vthread_t thr, bool signed_flag)
{
      vvp_vector4_t valb = thr->pop_vec4();
      vvp_vector4_t vala = thr->pop_vec4();

      unsigned wid = vala.size();

      vvp_vector2_t xv2 = vvp_vector2_t(vala, true);
      vvp_vector2_t yv2 = vvp_vector2_t(valb, true);


        /* If we have an X or Z in the arguments return X. */
      if (xv2.is_NaN() || yv2.is_NaN()) {
	    vvp_vector4_t tmp (wid, BIT4_X);
	    thr->push_vec4(tmp);
	    return true;
      }

	// Is the exponent negative? If so, table 5-6 in IEEE1364-2005
	// defines what value is returned.
      if (signed_flag && yv2.value(yv2.size()-1)) {
	    int a_val;
	    vvp_bit4_t pad = BIT4_0, lsb = BIT4_0;
	    if (vector2_to_value(xv2, a_val, true)) {
		  if (a_val == 0) {
			pad = BIT4_X; lsb = BIT4_X;
		  }
		  if (a_val == 1) {
			pad = BIT4_0; lsb = BIT4_1;
		  }
		  if (a_val == -1) {
			if (yv2.value(0)) {
			      pad = BIT4_1; lsb = BIT4_1;
			} else {
			      pad = BIT4_0; lsb = BIT4_1;
			}
		  }
	    }
	    vvp_vector4_t tmp (wid, pad);
	    tmp.set_bit(0, lsb);
	    thr->push_vec4(tmp);
	    return true;
      }

      vvp_vector2_t result = pow(xv2, yv2);

        /* Copy only what we need of the result. If the result is too
	   small, zero-pad it. */
      for (unsigned jdx = 0;  jdx < wid;  jdx += 1) {
	    if (jdx >= result.size())
		  vala.set_bit(jdx, BIT4_0);
	    else
		  vala.set_bit(jdx, result.value(jdx) ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(vala);

      return true;
}

bool of_POW(vthread_t thr, vvp_code_t)
{
      return of_POW_base(thr, false);
}

bool of_POW_S(vthread_t thr, vvp_code_t)
{
      return of_POW_base(thr, true);
}

bool of_POW_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(pow(l,r));

      return true;
}

/*
 * %obj/dar/size
 *
 * Pop a darray object from the object stack and push its size onto
 * the vec4 stack as a 32-bit unsigned integer.
 * Used for getting size of nested dynamic array elements, e.g., arr[i].size()
 */
bool of_OBJ_DAR_SIZE(vthread_t thr, vvp_code_t)
{
      vvp_object_t obj;
      thr->pop_object(obj);

      vvp_darray*dar = obj.peek<vvp_darray>();
      size_t size = 0;
      if (dar) {
	    size = dar->get_size();
      }

      // Push size as 32-bit unsigned
      vvp_vector4_t result(32);
      for (unsigned i = 0; i < 32; i++) {
	    result.set_bit(i, (size >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(result);

      return true;
}

/*
 * %prop/dar/size <pid>
 *
 * Get the size of a dynamic array property from the cobject on the object stack.
 * Push the size onto the vec4 stack as a 32-bit unsigned integer.
 * Does NOT pop the object from the object stack.
 */
bool of_PROP_DAR_SIZE(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (cobj == 0) {
	    cerr << thr->get_fileline()
	         << "Error: %prop/dar/size on null object." << endl;
	    thr->push_vec4(vvp_vector4_t(32, BIT4_X));
	    return true;
      }

      // Get the darray property value
      vvp_object_t dar_obj;
      cobj->get_object(pid, dar_obj, 0);

      vvp_darray*dar = dar_obj.peek<vvp_darray>();
      size_t size = 0;
      if (dar) {
	    size = dar->get_size();
      }

      // Push size as 32-bit unsigned
      vvp_vector4_t result(32);
      for (unsigned i = 0; i < 32; i++) {
	    result.set_bit(i, (size >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(result);

      return true;
}

/*
 * %prop/q/popf <pid>, <wid>
 *
 * Pop front element from a queue property and push to vec4 stack.
 * The cobject is on the object stack (peeked, not popped).
 */
bool of_PROP_Q_POPF(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;
      unsigned wid = cp->bit_idx[0];

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (cobj == 0) {
	    cerr << thr->get_fileline()
	         << "Error: %prop/q/popf on null object." << endl;
	    thr->push_vec4(vvp_vector4_t(wid, BIT4_X));
	    return true;
      }

      // Get the queue property value
      vvp_object_t queue_obj;
      cobj->get_object(pid, queue_obj, 0);

      vvp_queue_vec4*queue = queue_obj.peek<vvp_queue_vec4>();
      if (queue && queue->get_size() > 0) {
	    vvp_vector4_t value;
	    queue->get_word(0, value);
	    queue->pop_front();
	    // Pad or truncate to requested width
	    value.resize(wid);
	    thr->push_vec4(value);
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: %prop/q/popf on empty or null queue." << endl;
	    thr->push_vec4(vvp_vector4_t(wid, BIT4_X));
      }

      return true;
}

/*
 * %prop/q/popb <pid>, <wid>
 *
 * Pop back element from a queue property and push to vec4 stack.
 * The cobject is on the object stack (peeked, not popped).
 */
bool of_PROP_Q_POPB(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;
      unsigned wid = cp->bit_idx[0];

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (cobj == 0) {
	    cerr << thr->get_fileline()
	         << "Error: %prop/q/popb on null object." << endl;
	    thr->push_vec4(vvp_vector4_t(wid, BIT4_X));
	    return true;
      }

      // Get the queue property value
      vvp_object_t queue_obj;
      cobj->get_object(pid, queue_obj, 0);

      vvp_queue_vec4*queue = queue_obj.peek<vvp_queue_vec4>();
      if (queue && queue->get_size() > 0) {
	    size_t last_idx = queue->get_size() - 1;
	    vvp_vector4_t value;
	    queue->get_word(last_idx, value);
	    queue->pop_back();
	    // Pad or truncate to requested width
	    value.resize(wid);
	    thr->push_vec4(value);
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: %prop/q/popb on empty or null queue." << endl;
	    thr->push_vec4(vvp_vector4_t(wid, BIT4_X));
      }

      return true;
}

/*
 * %prop/q/popf/o <pid>
 *
 * Pop front element from a queue property of objects and push to object stack.
 * The cobject is on the object stack (peeked, not popped).
 */
bool of_PROP_Q_POPF_O(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (cobj == 0) {
	    cerr << thr->get_fileline()
	         << "Error: %prop/q/popf/o on null object." << endl;
	    thr->push_object(vvp_object_t());  // push null
	    return true;
      }

      // Get the queue property value
      vvp_object_t queue_obj;
      cobj->get_object(pid, queue_obj, 0);

      vvp_queue_object*queue = queue_obj.peek<vvp_queue_object>();
      if (queue && queue->get_size() > 0) {
	    vvp_object_t value;
	    queue->get_word(0, value);
	    queue->pop_front();
	    thr->push_object(value);
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: %prop/q/popf/o on empty or null queue." << endl;
	    thr->push_object(vvp_object_t());  // push null
      }

      return true;
}

/*
 * %prop/q/popb/o <pid>
 *
 * Pop back element from a queue property of objects and push to object stack.
 * The cobject is on the object stack (peeked, not popped).
 */
bool of_PROP_Q_POPB_O(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (cobj == 0) {
	    cerr << thr->get_fileline()
	         << "Error: %prop/q/popb/o on null object." << endl;
	    thr->push_object(vvp_object_t());  // push null
	    return true;
      }

      // Get the queue property value
      vvp_object_t queue_obj;
      cobj->get_object(pid, queue_obj, 0);

      vvp_queue_object*queue = queue_obj.peek<vvp_queue_object>();
      if (queue && queue->get_size() > 0) {
	    size_t last_idx = queue->get_size() - 1;
	    vvp_object_t value;
	    queue->get_word(last_idx, value);
	    queue->pop_back();
	    thr->push_object(value);
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: %prop/q/popb/o on empty or null queue." << endl;
	    thr->push_object(vvp_object_t());  // push null
      }

      return true;
}

/*
 * %prop/obj <pid>, <idx>
 *
 * Load an object value from the cobject and push it onto the object stack.
 */
bool of_PROP_OBJ(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;
      unsigned idx = cp->bit_idx[0];

      if (idx != 0) {
	    assert(idx < vthread_s::WORDS_COUNT);
	    idx = thr->words[idx].w_uint;
      }

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();

      if (!cobj) {
	    // Object is null - push null object and continue gracefully
	    // This can happen when accessing properties of uninitialized objects
	    vvp_object_t val;
	    thr->push_object(val);
	    return true;
      }

      vvp_object_t val;
      cobj->get_object(pid, val, idx);

      thr->push_object(val);

      return true;
}

static void get_from_obj(unsigned pid, vvp_cobject*cobj, double&val)
{
      val = cobj->get_real(pid);
}

static void get_from_obj(unsigned pid, vvp_cobject*cobj, string&val)
{
      val = cobj->get_string(pid);
}

static void get_from_obj(unsigned pid, vvp_cobject*cobj, vvp_vector4_t&val)
{
      cobj->get_vec4(pid, val);
}

template <typename ELEM>
static bool prop(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	      // Push a default value and continue gracefully
	    ELEM val = ELEM();
	    vthread_push(thr, val);
	    return true;
      }

      ELEM val;
      get_from_obj(pid, cobj, val);
      vthread_push(thr, val);

      return true;
}

/*
 * %prop/r <pid>
 *
 * Load a real value from the cobject and push it onto the real value
 * stack.
 */
bool of_PROP_R(vthread_t thr, vvp_code_t cp)
{
      return prop<double>(thr, cp);
}

/*
 * %prop/str <pid>
 *
 * Load a string value from the cobject and push it onto the real value
 * stack.
 */
bool of_PROP_STR(vthread_t thr, vvp_code_t cp)
{
      return prop<string>(thr, cp);
}

/*
 * %prop/v <pid>
 *
 * Load a property <pid> from the cobject on the top of the stack into
 * the vector space at <base>.
 */
bool of_PROP_V(vthread_t thr, vvp_code_t cp)
{
      return prop<vvp_vector4_t>(thr, cp);
}

bool of_PUSHI_REAL(vthread_t thr, vvp_code_t cp)
{
      double mant = cp->bit_idx[0];
      uint32_t imant = cp->bit_idx[0];
      int exp = cp->bit_idx[1];

	// Detect +infinity
      if (exp==0x3fff && imant==0) {
	    thr->push_real(INFINITY);
	    return true;
      }
	// Detect -infinity
      if (exp==0x7fff && imant==0) {
	    thr->push_real(-INFINITY);
	    return true;
      }
	// Detect NaN
      if (exp==0x3fff) {
	    thr->push_real(nan(""));
	    return true;
      }

      double sign = (exp & 0x4000)? -1.0 : 1.0;

      exp &= 0x1fff;

      mant = sign * ldexp(mant, exp - 0x1000);
      thr->push_real(mant);
      return true;
}

bool of_PUSHI_STR(vthread_t thr, vvp_code_t cp)
{
      const char*text = cp->text;
      thr->push_str(filter_string(text));
      return true;
}

/*
 * %pushi/vec4 <vala>, <valb>, <wid>
 */
bool of_PUSHI_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned wid  = cp->number;

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t val (wid, BIT4_0);
      get_immediate_rval (cp, val);

      thr->push_vec4(val);

      return true;
}

/*
 * %pushv/str
 *   Pops a vec4 value, and pushes a string.
 */
bool of_PUSHV_STR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t vec = thr->pop_vec4();

      size_t slen = (vec.size() + 7)/8;
      vector<char>buf;
      buf.reserve(slen);

      for (size_t idx = 0 ; idx < vec.size() ; idx += 8) {
	    char tmp = 0;
	    size_t trans = 8;
	    if (idx+trans > vec.size())
		  trans = vec.size() - idx;

	    for (size_t bdx = 0 ; bdx < trans ; bdx += 1) {
		  if (vec.value(idx+bdx) == BIT4_1)
			tmp |= 1 << bdx;
	    }

	    if (tmp != 0)
		  buf.push_back(tmp);
      }

      string val;
      for (vector<char>::reverse_iterator cur = buf.rbegin()
		 ; cur != buf.rend() ; ++cur) {
	    val.push_back(*cur);
      }

      thr->push_str(val);

      return true;
}

/*
 * %putc/str/vec4 <var>, <mux>
 */
bool of_PUTC_STR_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned muxr = cp->bit_idx[0];
      int32_t mux = muxr? thr->words[muxr].w_int : 0;

      vvp_vector4_t val = thr->pop_vec4();
      assert(val.size() == 8);

      if (mux < 0)
	    return true;

	/* Get the existing value of the string. If we find that the
	   index is too big for the string, then give up. */
      vvp_net_t*net = cp->net;
      vvp_fun_signal_string*fun = dynamic_cast<vvp_fun_signal_string*> (net->fun);
      assert(fun);

      string tmp = fun->get_string();
      if (tmp.size() <= (size_t)mux)
	    return true;

      char val_str = 0;
      for (size_t idx = 0 ; idx < 8 ; idx += 1) {
	    if (val.value(idx)==BIT4_1)
		  val_str |= 1<<idx;
      }

	// It is a quirk of the Verilog standard that putc(..., 'h00)
	// has no effect. Test for that case here.
      if (val_str == 0)
	    return true;

      tmp[mux] = val_str;

      vvp_send_string(vvp_net_ptr_t(cp->net, 0), tmp, thr->wt_context);
      return true;
}

template <typename ELEM, class QTYPE>
static bool qinsert(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      int64_t idx = thr->words[3].w_int;
      ELEM value;
      vvp_net_t*net = cp->net;
      pop_value(thr, value, wid); // Pop the value to store.

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);
      if (idx < 0) {
	    cerr << thr->get_fileline()
	         << "Warning: cannot insert at a negative "
	         << get_queue_type(value)
	         << " index (" << idx << "). ";
	    print_queue_value(value);
	    cerr << " was not added." << endl;
      } else if (thr->flags[4] != BIT4_0) {
	    cerr << thr->get_fileline()
	         << "Warning: cannot insert at an undefined "
	         << get_queue_type(value) << " index. ";
	    print_queue_value(value);
	    cerr << " was not added." << endl;
      } else {
	    unsigned max_size = thr->words[cp->bit_idx[0]].w_int;
	    queue->insert(idx, value, max_size);
      }
      return true;
}

/*
 * %qinsert/real <var-label>
 */
bool of_QINSERT_REAL(vthread_t thr, vvp_code_t cp)
{
      return qinsert<double, vvp_queue_real>(thr, cp);
}

/*
 * %qinsert/str <var-label>
 */
bool of_QINSERT_STR(vthread_t thr, vvp_code_t cp)
{
      return qinsert<string, vvp_queue_string>(thr, cp);
}

/*
 * %qinsert/v <var-label>
 */
bool of_QINSERT_V(vthread_t thr, vvp_code_t cp)
{
      return qinsert<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[1]);
}

/*
 * %qinsert/obj <var-label>
 * Insert object into queue at index (from word register 3).
 */
bool of_QINSERT_OBJ(vthread_t thr, vvp_code_t cp)
{
      return qinsert<vvp_object_t, vvp_queue_object>(thr, cp);
}

/*
 * Helper functions used in the queue pop templates
 */
inline void push_value(vthread_t thr, double value, unsigned)
{
      thr->push_real(value);
}

inline void push_value(vthread_t thr, const string&value, unsigned)
{
      thr->push_str(value);
}

inline void push_value(vthread_t thr, const vvp_vector4_t&value, unsigned wid)
{
      assert(wid == value.size());
      thr->push_vec4(value);
}

inline void push_value(vthread_t thr, const vvp_object_t&value, unsigned)
{
      thr->push_object(value);
}

template <typename ELEM, class QTYPE>
static bool q_pop(vthread_t thr, vvp_code_t cp,
                  void (*get_val_func)(vvp_queue*, ELEM&),
                  const char*loc, unsigned wid)
{
      vvp_net_t*net = cp->net;

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);

      size_t size = queue->get_size();

      ELEM value;
      if (size) {
	    get_val_func(queue, value);
      } else {
	    dq_default(value, wid);
	    cerr << thr->get_fileline()
	         << "Warning: pop_" << loc << "() on empty "
	         << get_queue_type(value) << "." << endl;
      }

      push_value(thr, value, wid);
      return true;
}

template <typename ELEM>
static void get_back_value(vvp_queue*queue, ELEM&value)
{
      queue->get_word(queue->get_size()-1, value);
      queue->pop_back();
}

template <typename ELEM, class QTYPE>
static bool qpop_b(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      return q_pop<ELEM, QTYPE>(thr, cp, get_back_value<ELEM>, "back", wid);
}

/*
 * %qpop/b/real <var-label>
 */
bool of_QPOP_B_REAL(vthread_t thr, vvp_code_t cp)
{
      return qpop_b<double, vvp_queue_real>(thr, cp);
}

/*
 * %qpop/b/str <var-label>
 */
bool of_QPOP_B_STR(vthread_t thr, vvp_code_t cp)
{
      return qpop_b<string, vvp_queue_string>(thr, cp);
}

/*
 * %qpop/b/v <var-label>
 */
bool of_QPOP_B_V(vthread_t thr, vvp_code_t cp)
{
      return qpop_b<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[0]);
}

template <typename ELEM>
static void get_front_value(vvp_queue*queue, ELEM&value)
{
      queue->get_word(0, value);
      queue->pop_front();
}

template <typename ELEM, class QTYPE>
static bool qpop_f(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      return q_pop<ELEM, QTYPE>(thr, cp, get_front_value<ELEM>, "front", wid);
}


/*
 * %qpop/f/real <var-label>
 */
bool of_QPOP_F_REAL(vthread_t thr, vvp_code_t cp)
{
      return qpop_f<double, vvp_queue_real>(thr, cp);
}

/*
 * %qpop/f/str <var-label>
 */
bool of_QPOP_F_STR(vthread_t thr, vvp_code_t cp)
{
      return qpop_f<string, vvp_queue_string>(thr, cp);
}

/*
 * %qpop/f/v <var-label>
 */
bool of_QPOP_F_V(vthread_t thr, vvp_code_t cp)
{
      return qpop_f<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[0]);
}

/*
 * %qpop/b/obj <var-label>
 * Pop object from back of queue and push to object stack.
 */
bool of_QPOP_B_OBJ(vthread_t thr, vvp_code_t cp)
{
      return qpop_b<vvp_object_t, vvp_queue_object>(thr, cp);
}

/*
 * %qpop/f/obj <var-label>
 * Pop object from front of queue and push to object stack.
 */
bool of_QPOP_F_OBJ(vthread_t thr, vvp_code_t cp)
{
      return qpop_f<vvp_object_t, vvp_queue_object>(thr, cp);
}

/*
 * %qshuffle <var-label>
 * Shuffle the queue in place.
 */
bool of_QSHUFFLE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: shuffle() on empty or nil queue." << endl;
	    return true;
      }

      queue->shuffle();
      return true;
}

/*
 * %qreverse <var-label>
 * Reverse the queue in place.
 */
bool of_QREVERSE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: reverse() on empty or nil queue." << endl;
	    return true;
      }

      queue->reverse();
      return true;
}

/*
 * %qsort <var-label>
 * Sort the queue in ascending order.
 */
bool of_QSORT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: sort() on empty or nil queue." << endl;
	    return true;
      }

      queue->sort();
      return true;
}

/*
 * %qrsort <var-label>
 * Sort the queue in descending order.
 */
bool of_QRSORT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: rsort() on empty or nil queue." << endl;
	    return true;
      }

      queue->rsort();
      return true;
}

/*
 * %qsort/m <var-label>, <offset>, <width>
 * Sort the queue by struct member in ascending order.
 * Elements are sorted by the bits at [offset +: width].
 */
bool of_QSORT_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: sort() with clause on empty or nil queue." << endl;
	    return true;
      }

      queue->sort_by_member(member_offset, member_width, false);
      return true;
}

/*
 * %qrsort/m <var-label>, <offset>, <width>
 * Sort the queue by struct member in descending order.
 * Elements are sorted by the bits at [offset +: width].
 */
bool of_QRSORT_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: rsort() with clause on empty or nil queue." << endl;
	    return true;
      }

      queue->sort_by_member(member_offset, member_width, true);
      return true;
}

/*
 * %qmin <var-label>
 * Push a new queue containing the minimum element(s) to the object stack.
 */
bool of_QMIN(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->min_val();
      thr->push_object(result);
      return true;
}

/*
 * %qmax <var-label>
 * Push a new queue containing the maximum element(s) to the object stack.
 */
bool of_QMAX(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->max_val();
      thr->push_object(result);
      return true;
}

/*
 * %qmin/m <var-label>, <offset>, <width>
 * Push a new queue containing element(s) with minimum member value.
 * Uses bit offset and width to extract member value for comparison.
 */
bool of_QMIN_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->min_by_member(member_offset, member_width);
      thr->push_object(result);
      return true;
}

/*
 * %qmax/m <var-label>, <offset>, <width>
 * Push a new queue containing element(s) with maximum member value.
 * Uses bit offset and width to extract member value for comparison.
 */
bool of_QMAX_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->max_by_member(member_offset, member_width);
      thr->push_object(result);
      return true;
}

/*
 * %qsum <var-label>, <width>
 * Push the sum of all elements to the vec4 stack.
 */
bool of_QSUM(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return 0
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result = queue->sum_val(wid);
      thr->push_vec4(result);
      return true;
}

/*
 * %qproduct <var-label>, <width>
 * Push the product of all elements to the vec4 stack.
 */
bool of_QPRODUCT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return 0 for empty queue (undefined behavior)
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result = queue->product_val(wid);
      thr->push_vec4(result);
      return true;
}

/*
 * %dsum <var-label>, <width>
 * Push the sum of all dynamic array elements to the vec4 stack.
 */
bool of_DSUM(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result(wid, BIT4_0);
      for (size_t i = 0; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    result.add(elem);
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dproduct <var-label>, <width>
 * Push the product of all dynamic array elements to the vec4 stack.
 */
bool of_DPRODUCT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result(wid, BIT4_0);
      result.set_bit(0, BIT4_1); // Start with 1
      for (size_t i = 0; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    result.mul(elem);
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dmin <var-label>
 * Push the minimum element of dynamic array to the vec4 stack.
 */
bool of_DMIN(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    vvp_vector4_t val(32, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result;
      darray->get_word(0, result);
      for (size_t i = 1; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    // compare_gtge_signed(a, b) returns BIT4_1 if a > b
	    if (compare_gtge_signed(result, elem, BIT4_0) == BIT4_1) {
		  result = elem;
	    }
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dmax <var-label>
 * Push the maximum element of dynamic array to the vec4 stack.
 */
bool of_DMAX(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    vvp_vector4_t val(32, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result;
      darray->get_word(0, result);
      for (size_t i = 1; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    // compare_gtge_signed(a, b) returns BIT4_1 if a > b
	    if (compare_gtge_signed(elem, result, BIT4_0) == BIT4_1) {
		  result = elem;
	    }
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dand <var-label>, <width>
 * Push the bitwise AND of all dynamic array elements to the vec4 stack.
 */
bool of_DAND(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    // Return all 1s for empty array (AND identity)
	    vvp_vector4_t val(wid, BIT4_1);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result;
      darray->get_word(0, result);
      for (size_t i = 1; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    for (unsigned j = 0; j < result.size(); ++j) {
		  vvp_bit4_t a = result.value(j);
		  vvp_bit4_t b = elem.value(j);
		  vvp_bit4_t r = BIT4_X;
		  if (a == BIT4_0 || b == BIT4_0)
			r = BIT4_0;
		  else if (a == BIT4_1 && b == BIT4_1)
			r = BIT4_1;
		  result.set_bit(j, r);
	    }
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dor <var-label>, <width>
 * Push the bitwise OR of all dynamic array elements to the vec4 stack.
 */
bool of_DOR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    // Return all 0s for empty array (OR identity)
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result;
      darray->get_word(0, result);
      for (size_t i = 1; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    for (unsigned j = 0; j < result.size(); ++j) {
		  vvp_bit4_t a = result.value(j);
		  vvp_bit4_t b = elem.value(j);
		  vvp_bit4_t r = BIT4_X;
		  if (a == BIT4_1 || b == BIT4_1)
			r = BIT4_1;
		  else if (a == BIT4_0 && b == BIT4_0)
			r = BIT4_0;
		  result.set_bit(j, r);
	    }
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dxor <var-label>, <width>
 * Push the bitwise XOR of all dynamic array elements to the vec4 stack.
 */
bool of_DXOR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0 || darray->get_size() == 0) {
	    // Return all 0s for empty array (XOR identity)
	    vvp_vector4_t val(wid, BIT4_0);
	    thr->push_vec4(val);
	    return true;
      }

      vvp_vector4_t result;
      darray->get_word(0, result);
      for (size_t i = 1; i < darray->get_size(); ++i) {
	    vvp_vector4_t elem;
	    darray->get_word(i, elem);
	    for (unsigned j = 0; j < result.size(); ++j) {
		  vvp_bit4_t a = result.value(j);
		  vvp_bit4_t b = elem.value(j);
		  vvp_bit4_t r = BIT4_X;
		  if ((a == BIT4_0 || a == BIT4_1) && (b == BIT4_0 || b == BIT4_1)) {
			r = (a != b) ? BIT4_1 : BIT4_0;
		  }
		  result.set_bit(j, r);
	    }
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %dreverse <var-label>
 * Reverse the dynamic array in place.
 */
bool of_DREVERSE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: reverse() on empty or nil dynamic array." << endl;
	    return true;
      }

      darray->reverse();
      return true;
}

/*
 * %dshuffle <var-label>
 * Shuffle the dynamic array in place.
 */
bool of_DSHUFFLE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: shuffle() on empty or nil dynamic array." << endl;
	    return true;
      }

      darray->shuffle();
      return true;
}

/*
 * %dsort <var-label>
 * Sort the dynamic array in ascending order.
 */
bool of_DSORT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: sort() on empty or nil dynamic array." << endl;
	    return true;
      }

      darray->sort();
      return true;
}

/*
 * %drsort <var-label>
 * Sort the dynamic array in descending order.
 */
bool of_DRSORT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();
      if (darray == 0) {
	    cerr << thr->get_fileline()
	         << "Warning: rsort() on empty or nil dynamic array." << endl;
	    return true;
      }

      darray->rsort();
      return true;
}

/*
 * Helper function to compare two vec4 values with the given operator.
 * cmp_op: 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge
 * Uses signed comparison for lt/le/gt/ge.
 */
static bool vec4_compare(const vvp_vector4_t& elem, const vvp_vector4_t& cmp_val, int cmp_op)
{
      // Convert both vectors to 64-bit integers for comparison.
      // This handles width differences (e.g., 8-bit field vs 32-bit comparison value).
      uint64_t elem_val = 0;
      uint64_t cmp_val_int = 0;

      // Get element value (unsigned interpretation for basic value)
      unsigned elem_wid = elem.size();
      for (unsigned i = 0; i < elem_wid && i < 64; i++) {
	    if (elem.value(i) == BIT4_1)
		  elem_val |= (1ULL << i);
      }

      // Get comparison value (unsigned interpretation for basic value)
      unsigned cmp_wid = cmp_val.size();
      for (unsigned i = 0; i < cmp_wid && i < 64; i++) {
	    if (cmp_val.value(i) == BIT4_1)
		  cmp_val_int |= (1ULL << i);
      }

      switch (cmp_op) {
	    case 0: // eq (==) - unsigned comparison
		  return elem_val == cmp_val_int;
	    case 1: // ne (!=) - unsigned comparison
		  return elem_val != cmp_val_int;
	    case 2: // lt (<) - signed comparison
	    case 3: // le (<=)
	    case 4: // gt (>)
	    case 5: // ge (>=)
		  {
			// Sign extend for signed comparison
			int64_t elem_signed = (int64_t)elem_val;
			int64_t cmp_signed = (int64_t)cmp_val_int;

			// Check if sign extension needed
			if (elem_wid > 0 && elem_wid < 64) {
			      if (elem.value(elem_wid - 1) == BIT4_1) {
				    // Sign extend negative value
				    for (unsigned i = elem_wid; i < 64; i++)
					  elem_signed |= (1ULL << i);
			      }
			}
			if (cmp_wid > 0 && cmp_wid < 64) {
			      if (cmp_val.value(cmp_wid - 1) == BIT4_1) {
				    // Sign extend negative value
				    for (unsigned i = cmp_wid; i < 64; i++)
					  cmp_signed |= (1ULL << i);
			      }
			}

			// Perform signed comparison
			switch (cmp_op) {
			      case 2: return elem_signed < cmp_signed;
			      case 3: return elem_signed <= cmp_signed;
			      case 4: return elem_signed > cmp_signed;
			      case 5: return elem_signed >= cmp_signed;
			}
		  }
		  break;
      }
      return false;
}

/*
 * %qfind <mode>, <cmp_op>
 * Find elements in a queue matching a value with given comparison operator.
 * Mode: 0=find_index (all), 1=find_first_index, 2=find_last_index
 *       3=find (all elements), 4=find_first (first element), 5=find_last (last element)
 * cmp_op: 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge
 * Queue is on object stack, comparison value is on vec4 stack.
 * Pushes result queue onto object stack:
 *   - Modes 0-2: queue of int indices
 *   - Modes 3-5: queue of matching elements (same type as source)
 */
bool of_QFIND(vthread_t thr, vvp_code_t cp)
{
      unsigned mode = cp->number;
      unsigned cmp_op = cp->bit_idx[0];

      // Pop comparison value from vec4 stack
      vvp_vector4_t cmp_val = thr->pop_vec4();

      // Pop queue from object stack
      vvp_object_t queue_obj;
      thr->pop_object(queue_obj);

      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return empty result queue
	    vvp_object_t result;
	    result.reset(new vvp_queue_vec4);
	    thr->push_object(result);
	    return true;
      }

      // Create result queue to hold matching indices or elements
      vvp_queue_vec4*result = new vvp_queue_vec4;
      size_t qsize = queue->get_size();

      // Helper lambda to convert index to vvp_vector4_t
      auto make_idx_vec = [](size_t idx) {
	    vvp_vector4_t vec(32);
	    for (unsigned i = 0; i < 32; i++) {
		  vec.set_bit(i, (idx >> i) & 1 ? BIT4_1 : BIT4_0);
	    }
	    return vec;
      };

      if (mode == 0) {
	    // find_index: return all matching indices
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i), 0);
		  }
	    }
      } else if (mode == 1) {
	    // find_first_index: return first matching index
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i), 0);
			break;
		  }
	    }
      } else if (mode == 2) {
	    // find_last_index: return last matching index
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  queue->get_word(i - 1, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i - 1), 0);
			break;
		  }
	    }
      } else if (mode == 3) {
	    // find: return all matching elements
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
		  }
	    }
      } else if (mode == 4) {
	    // find_first: return first matching element
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      } else if (mode == 5) {
	    // find_last: return last matching element
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  queue->get_word(i - 1, elem);
		  if (vec4_compare(elem, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      }

      vvp_object_t result_obj;
      result_obj.reset(result);
      thr->push_object(result_obj);
      return true;
}

/*
 * %qfind_inside <mode>, <count>
 * Find elements in a queue that match any value in a set.
 * Mode: 0=find_index (all), 1=find_first_index, 2=find_last_index
 *       3=find (all), 4=find_first, 5=find_last
 * Count: number of values in the set
 * The values are on the vec4 stack (popped in reverse order).
 * Queue is on object stack.
 * Pushes result queue (of indices or elements) onto object stack.
 */
bool of_QFIND_INSIDE(vthread_t thr, vvp_code_t cp)
{
      unsigned mode = cp->number;
      unsigned count = cp->bit_idx[0];

      // Pop all comparison values from vec4 stack into a vector
      // Note: values are pushed in order, so we pop in reverse order
      std::vector<vvp_vector4_t> inside_values(count);
      for (unsigned i = count; i > 0; i--) {
	    inside_values[i-1] = thr->pop_vec4();
      }

      // Pop queue from object stack
      vvp_object_t queue_obj;
      thr->pop_object(queue_obj);

      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return empty result queue
	    vvp_object_t result;
	    result.reset(new vvp_queue_vec4);
	    thr->push_object(result);
	    return true;
      }

      // Create result queue to hold matching indices or elements
      vvp_queue_vec4*result = new vvp_queue_vec4;
      size_t qsize = queue->get_size();

      // Helper lambda to convert index to vvp_vector4_t
      auto make_idx_vec = [](size_t idx) {
	    vvp_vector4_t vec(32);
	    for (unsigned i = 0; i < 32; i++) {
		  vec.set_bit(i, (idx >> i) & 1 ? BIT4_1 : BIT4_0);
	    }
	    return vec;
      };

      // Helper lambda to check if element is in the inside set
      auto is_inside = [&inside_values](const vvp_vector4_t& elem) {
	    for (const auto& val : inside_values) {
		  if (vec4_compare(elem, val, 0)) // 0 = equality check
			return true;
	    }
	    return false;
      };

      if (mode == 0) {
	    // find_index: return all matching indices
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (is_inside(elem)) {
			result->push_back(make_idx_vec(i), 0);
		  }
	    }
      } else if (mode == 1) {
	    // find_first_index: return first matching index
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (is_inside(elem)) {
			result->push_back(make_idx_vec(i), 0);
			break;
		  }
	    }
      } else if (mode == 2) {
	    // find_last_index: return last matching index
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  queue->get_word(i - 1, elem);
		  if (is_inside(elem)) {
			result->push_back(make_idx_vec(i - 1), 0);
			break;
		  }
	    }
      } else if (mode == 3) {
	    // find: return all matching elements
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (is_inside(elem)) {
			result->push_back(elem, 0);
		  }
	    }
      } else if (mode == 4) {
	    // find_first: return first matching element
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  queue->get_word(i, elem);
		  if (is_inside(elem)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      } else if (mode == 5) {
	    // find_last: return last matching element
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  queue->get_word(i - 1, elem);
		  if (is_inside(elem)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      }

      vvp_object_t result_obj;
      result_obj.reset(result);
      thr->push_object(result_obj);
      return true;
}

/*
 * %qfind_prop <mode>, <property_index>, <cmp_op>
 * Find elements in an object queue where item.property matches a value.
 * Mode: 0=find_index (all), 1=find_first_index, 2=find_last_index
 * cmp_op: 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge
 * Queue is on object stack, comparison value is on vec4 stack.
 * Pushes result queue (of int indices) onto object stack.
 */
bool of_QFIND_PROP(vthread_t thr, vvp_code_t cp)
{
      unsigned mode = cp->number;
      unsigned prop_idx = cp->bit_idx[0];
      unsigned cmp_op = cp->bit_idx[1];

      // Pop comparison value from vec4 stack
      vvp_vector4_t cmp_val = thr->pop_vec4();

      // Pop queue from object stack
      vvp_object_t queue_obj;
      thr->pop_object(queue_obj);

      // Try to get as object queue
      vvp_queue_object*obj_queue = dynamic_cast<vvp_queue_object*>(queue_obj.peek<vvp_queue>());
      if (obj_queue == 0 || obj_queue->get_size() == 0) {
	    // Return empty result queue
	    vvp_object_t result;
	    result.reset(new vvp_queue_vec4);
	    thr->push_object(result);
	    return true;
      }

      // Create result queue to hold matching indices
      vvp_queue_vec4*result = new vvp_queue_vec4;
      size_t qsize = obj_queue->get_size();

      // Helper lambda to convert index to vvp_vector4_t
      auto make_idx_vec = [](size_t idx) {
	    vvp_vector4_t vec(32);
	    for (unsigned i = 0; i < 32; i++) {
		  vec.set_bit(i, (idx >> i) & 1 ? BIT4_1 : BIT4_0);
	    }
	    return vec;
      };

      if (mode == 0) {
	    // find_index: return all matching indices
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_object_t elem_obj;
		  obj_queue->get_word(i, elem_obj);
		  vvp_cobject*cobj = elem_obj.peek<vvp_cobject>();
		  if (cobj) {
			vvp_vector4_t prop_val;
			cobj->get_vec4(prop_idx, prop_val);
			if (vec4_compare(prop_val, cmp_val, cmp_op)) {
			      result->push_back(make_idx_vec(i), 0);
			}
		  }
	    }
      } else if (mode == 1) {
	    // find_first_index: return first matching index
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_object_t elem_obj;
		  obj_queue->get_word(i, elem_obj);
		  vvp_cobject*cobj = elem_obj.peek<vvp_cobject>();
		  if (cobj) {
			vvp_vector4_t prop_val;
			cobj->get_vec4(prop_idx, prop_val);
			if (vec4_compare(prop_val, cmp_val, cmp_op)) {
			      result->push_back(make_idx_vec(i), 0);
			      break;
			}
		  }
	    }
      } else if (mode == 2) {
	    // find_last_index: return last matching index
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_object_t elem_obj;
		  obj_queue->get_word(i - 1, elem_obj);
		  vvp_cobject*cobj = elem_obj.peek<vvp_cobject>();
		  if (cobj) {
			vvp_vector4_t prop_val;
			cobj->get_vec4(prop_idx, prop_val);
			if (vec4_compare(prop_val, cmp_val, cmp_op)) {
			      result->push_back(make_idx_vec(i - 1), 0);
			      break;
			}
		  }
	    }
      }

      vvp_object_t result_obj;
      result_obj.reset(result);
      thr->push_object(result_obj);
      return true;
}

/*
 * %qfind_struct <packed_mode> <member_off> <member_wid>
 * Find elements in a vec4 queue where item.member matches a value.
 * packed_mode: mode in lower 8 bits, cmp_op in upper bits
 * Mode: 0=find_index (all), 1=find_first_index, 2=find_last_index (return indices)
 *       3=find (all), 4=find_first, 5=find_last (return elements)
 * cmp_op: 0=eq, 1=ne, 2=lt, 3=le, 4=gt, 5=ge
 * Queue is on object stack, comparison value is on vec4 stack.
 * Pushes result queue (of int indices or elements) onto object stack.
 */
bool of_QFIND_STRUCT(vthread_t thr, vvp_code_t cp)
{
      unsigned packed_mode = cp->number;
      unsigned mode = packed_mode & 0xFF;
      unsigned cmp_op = (packed_mode >> 8) & 0xFF;
      unsigned member_off = cp->bit_idx[0];
      unsigned member_wid = cp->bit_idx[1];

      // Pop comparison value from vec4 stack
      vvp_vector4_t cmp_val = thr->pop_vec4();

      // Pop queue from object stack
      vvp_object_t queue_obj;
      thr->pop_object(queue_obj);

      // Try to get as vec4 queue (queue of packed structs)
      vvp_queue_vec4*vec_queue = dynamic_cast<vvp_queue_vec4*>(queue_obj.peek<vvp_queue>());
      if (vec_queue == 0 || vec_queue->get_size() == 0) {
	    // Return empty result queue
	    vvp_object_t result;
	    result.reset(new vvp_queue_vec4);
	    thr->push_object(result);
	    return true;
      }

      // Create result queue to hold matching indices
      vvp_queue_vec4*result = new vvp_queue_vec4;
      size_t qsize = vec_queue->get_size();

      // Helper lambda to convert index to vvp_vector4_t
      auto make_idx_vec = [](size_t idx) {
	    vvp_vector4_t vec(32);
	    for (unsigned i = 0; i < 32; i++) {
		  vec.set_bit(i, (idx >> i) & 1 ? BIT4_1 : BIT4_0);
	    }
	    return vec;
      };

      // Helper lambda to extract member bits from struct element
      auto extract_member = [member_off, member_wid](const vvp_vector4_t& elem) {
	    vvp_vector4_t member(member_wid);
	    for (unsigned i = 0; i < member_wid; i++) {
		  if (member_off + i < elem.size()) {
			member.set_bit(i, elem.value(member_off + i));
		  } else {
			member.set_bit(i, BIT4_X);
		  }
	    }
	    return member;
      };

      if (mode == 0) {
	    // find_index: return all matching indices
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i), 0);
		  }
	    }
      } else if (mode == 1) {
	    // find_first_index: return first matching index
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i), 0);
			break;
		  }
	    }
      } else if (mode == 2) {
	    // find_last_index: return last matching index
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i - 1, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(make_idx_vec(i - 1), 0);
			break;
		  }
	    }
      } else if (mode == 3) {
	    // find: return all matching elements
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
		  }
	    }
      } else if (mode == 4) {
	    // find_first: return first matching element
	    for (size_t i = 0; i < qsize; i++) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      } else if (mode == 5) {
	    // find_last: return last matching element
	    for (size_t i = qsize; i > 0; i--) {
		  vvp_vector4_t elem;
		  vec_queue->get_word(i - 1, elem);
		  vvp_vector4_t member_val = extract_member(elem);
		  if (vec4_compare(member_val, cmp_val, cmp_op)) {
			result->push_back(elem, 0);
			break;
		  }
	    }
      }

      vvp_object_t result_obj;
      result_obj.reset(result);
      thr->push_object(result_obj);
      return true;
}

/*
 * %qunique <var-label>
 * Push a queue with unique elements to the object stack.
 */
bool of_QUNIQUE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->unique_val();
      thr->push_object(result);
      return true;
}

/*
 * %qunique/m <var-label>, <offset>, <width>
 * Push a queue with elements unique by member to the object stack.
 * Uses bit offset and width to extract member value for comparison.
 */
bool of_QUNIQUE_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->unique_by_member(member_offset, member_width);
      thr->push_object(result);
      return true;
}

/*
 * %qunique_index <var-label>
 * Push a queue of indices of first unique occurrences to the object stack.
 */
bool of_QUNIQUE_INDEX(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->unique_index();
      thr->push_object(result);
      return true;
}

/*
 * %qunique_index/m <var-label>, <offset>, <width>
 * Push a queue of indices of first unique occurrences by member to the object stack.
 * Uses bit offset and width to extract member value for comparison.
 */
bool of_QUNIQUE_INDEX_M(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned member_offset = cp->bit_idx[0];
      unsigned member_width = cp->bit_idx[1];

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue_vec4*queue = dynamic_cast<vvp_queue_vec4*>(obj->get_object().peek<vvp_queue>());
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->unique_index_by_member(member_offset, member_width);
      thr->push_object(result);
      return true;
}

/*
 * %qmin_index <var-label>
 * Push a queue of indices of minimum elements to the object stack.
 */
bool of_QMIN_INDEX(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->min_index();
      thr->push_object(result);
      return true;
}

/*
 * %qmax_index <var-label>
 * Push a queue of indices of maximum elements to the object stack.
 */
bool of_QMAX_INDEX(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_queue*queue = obj->get_object().peek<vvp_queue>();
      if (queue == 0 || queue->get_size() == 0) {
	    // Return an empty queue
	    vvp_object_t result;
	    thr->push_object(result);
	    return true;
      }

      vvp_object_t result = queue->max_index();
      thr->push_object(result);
      return true;
}

/*
 * These implement the %release/net and %release/reg instructions. The
 * %release/net instruction applies to a net kind of functor by
 * sending the release/net command to the command port. (See vvp_net.h
 * for details.) The %release/reg instruction is the same, but sends
 * the release/reg command instead. These are very similar to the
 * %deassign instruction.
 */
static bool do_release_vec(vvp_code_t cp, bool net_flag)
{
      vvp_net_t*net = cp->net;
      unsigned base  = cp->bit_idx[0];
      unsigned width = cp->bit_idx[1];

      assert(net->fil);

      if (base >= net->fil->filter_size()) return true;
      if (base+width > net->fil->filter_size())
	    width = net->fil->filter_size() - base;

      bool full_sig = base == 0 && width == net->fil->filter_size();

	// XXXX Can't really do this if this is a partial release?
      net->fil->force_unlink();

	/* Do we release all or part of the net? */
      vvp_net_ptr_t ptr (net, 0);
      if (full_sig) {
	    net->fil->release(ptr, net_flag);
      } else {
	    net->fil->release_pv(ptr, base, width, net_flag);
      }
      net->fun->force_flag(false);

      return true;
}

/*
 * Helper function to call pre_randomize or post_randomize callback on an object.
 * Returns true if the method was found and called, false otherwise.
 */
static bool call_randomize_callback(vthread_t thr, vvp_cobject* cobj,
                                    const vvp_object_t& obj, const char* method_name)
{
      const class_type* defn = cobj->get_class_type();
      if (defn == 0)
	    return false;

      // Look up the method in the class's method table
      const class_type::method_info* method = defn->get_method(method_name);
      if (method == 0 || method->entry == 0 || method->scope == 0)
	    return false;

      // Create a new thread for the method call
      vthread_t child = vthread_new(method->entry, method->scope);

      // If the method scope is automatic (which class methods are),
      // allocate context and set up the '@' (this) variable
      if (method->scope->is_automatic()) {
	    vvp_context_t new_context = vthread_alloc_context(method->scope);
	    child->wt_context = new_context;
	    child->rd_context = new_context;

	    // Find the '@' variable in the method scope and store the object
	    __vpiScope* scope = method->scope;
	    for (unsigned idx = 0; idx < scope->intern.size(); ++idx) {
		  vpiHandle item = scope->intern[idx];
		  if (item && item->get_type_code() == vpiClassVar) {
			const char* name = item->vpi_get_str(vpiName);
			if (name && strcmp(name, "@") == 0) {
			      __vpiBaseVar* var = dynamic_cast<__vpiBaseVar*>(item);
			      if (var) {
				    vvp_net_t* net = var->get_net();
				    if (net && net->fun) {
					  vvp_fun_signal_object_aa* fun_aa =
						dynamic_cast<vvp_fun_signal_object_aa*>(net->fun);
					  if (fun_aa) {
						fun_aa->set_object_in_context(new_context, obj);
					  }
				    }
			      }
			      break;
			}
		  }
	    }
      }

      // Set up parent-child relationship and run the method synchronously
      child->parent = thr;
      thr->children.insert(child);

      child->is_scheduled = 1;
      child->i_am_in_function = 1;
      vthread_run(child);
      running_thread = thr;

      // Clean up the child thread
      if (child->i_have_ended) {
	    do_join(thr, child);
      }

      return true;
}

/*
 * %randomize
 *
 * Pop a class object from the object stack, randomize its 'rand' properties,
 * and push 1 (success) or 0 (failure) to the vec4 stack.
 *
 * Only properties marked with 'rand' or 'randc' qualifier are randomized.
 * Non-rand properties retain their values.
 *
 * Before randomization, calls pre_randomize() if defined.
 * After randomization, calls post_randomize() if defined.
 *
 * Constraint Support:
 * Uses generate-and-test solver with retry mechanism:
 *   1. Generate random values for all rand properties
 *   2. Check constraint bounds extracted from constraint blocks
 *   3. If any hard constraint fails, regenerate (up to MAX_CONSTRAINT_TRIES)
 *   4. Return 0 if constraints cannot be satisfied after retries
 */
static const int MAX_CONSTRAINT_TRIES = 100;

bool of_RANDOMIZE(vthread_t thr, vvp_code_t)
{
      vvp_object_t obj;
      thr->pop_object(obj);
      vvp_cobject* cobj = obj.peek<vvp_cobject>();

      if (cobj == nullptr) {
	    // Object is null, randomize fails
	    vvp_vector4_t res (32, BIT4_0);
	    thr->push_vec4(res);
	    return true;
      }

      // Call pre_randomize() callback if defined
      call_randomize_callback(thr, cobj, obj, "pre_randomize");

      const class_type* defn = cobj->get_class_type();
      size_t nprop = defn->property_count();
      // Check for constraints including inherited constraints from parent classes
      bool has_class_constraints = defn->has_any_constraints();
      const std::vector<class_type::simple_bound_t>& inline_constraints = thr->get_inline_constraints();
      bool has_inline_constraints = !inline_constraints.empty();
      bool has_constraints = has_class_constraints || has_inline_constraints;

      // Process size constraints - these resize dynamic arrays
      // Track which properties have size constraints so we can randomize their elements
      std::set<size_t> darray_props_to_randomize;
      std::map<size_t, unsigned> darray_elem_widths;

      // Track size bounds per property (for size >, <, >=, <= constraints)
      struct size_bounds_t {
	    int64_t min_size;      // -1 means no minimum (or use 0)
	    int64_t max_size;      // -1 means no maximum (use large default)
	    int64_t exact_size;    // -1 means no exact constraint
	    unsigned elem_width;
	    bool has_any;          // true if any size constraint exists
	    size_bounds_t() : min_size(-1), max_size(-1), exact_size(-1), elem_width(8), has_any(false) {}
      };
      std::map<size_t, size_bounds_t> size_bounds;

      // Collect property-based size constraints to apply AFTER source properties are randomized
      struct deferred_size_constraint {
	    size_t prop_idx;
	    size_t src_prop_idx;
	    int64_t offset;       // For 's': offset to add; for 'd': divisor
	    unsigned elem_width;
	    bool is_division;     // true if size = src_prop / offset
      };
      std::vector<deferred_size_constraint> deferred_size_constraints;

      // Helper lambda to evaluate condition for conditional constraints
      // Returns true if the condition is satisfied (or if there's no condition)
      auto evaluate_condition = [&](const class_type::simple_bound_t& bound) -> bool {
	    if (!bound.has_condition)
		  return true;  // No condition means always applies

	    // First check if inline constraints set the condition property to a specific value
	    // This handles cases like: randomize() with { burst == BURST4; }
	    // where the condition property (burst) will be constrained to a specific value
	    int64_t cond_val = 0;
	    bool found_inline_value = false;
	    for (const auto& inline_bound : inline_constraints) {
		  // Look for equality constraint on the condition property
		  if (inline_bound.property_idx == bound.cond_prop_idx &&
		      inline_bound.op == '=' && inline_bound.has_const_bound) {
			cond_val = inline_bound.const_bound;
			found_inline_value = true;
			break;
		  }
	    }

	    // If no inline constraint found, use the current property value
	    if (!found_inline_value) {
		  vvp_vector4_t cond_prop_val;
		  cobj->get_vec4(bound.cond_prop_idx, cond_prop_val);

		  if (cond_prop_val.size() <= 64) {
			for (unsigned i = 0; i < cond_prop_val.size(); i++) {
			      if (cond_prop_val.value(i) == BIT4_1)
				    cond_val |= (int64_t(1) << i);
			}
		  }
	    }

	    int64_t cond_bound_val = bound.cond_has_const ? bound.cond_const : 0;
	    if (!bound.cond_has_const && bound.cond_prop2_idx < nprop) {
		  vvp_vector4_t cond_prop2_val;
		  cobj->get_vec4(bound.cond_prop2_idx, cond_prop2_val);
		  if (cond_prop2_val.size() <= 64) {
			for (unsigned i = 0; i < cond_prop2_val.size(); i++) {
			      if (cond_prop2_val.value(i) == BIT4_1)
				    cond_bound_val |= (int64_t(1) << i);
			}
		  }
	    }

	    // Evaluate the condition
	    bool result = false;
	    switch (bound.cond_op) {
		  case '>': result = (cond_val > cond_bound_val); break;
		  case '<': result = (cond_val < cond_bound_val); break;
		  case 'G': result = (cond_val >= cond_bound_val); break;
		  case 'L': result = (cond_val <= cond_bound_val); break;
		  case '=': result = (cond_val == cond_bound_val); break;
		  case '!': result = (cond_val != cond_bound_val); break;
		  default: result = true; break;
	    }
	    return result;
      };

      // Helper lambda to collect size bounds
      auto collect_size_bound = [&](const class_type::simple_bound_t& bound) {
	    size_t prop_idx = bound.property_idx;
	    unsigned elem_width = (unsigned)bound.weight;
	    if (elem_width == 0) elem_width = 8;

	    size_bounds_t& sb = size_bounds[prop_idx];
	    sb.has_any = true;
	    sb.elem_width = elem_width;

	    switch (bound.op) {
		  case 'S':  // size == N (exact)
			// First matching exact size wins (for conditional constraints)
			if (sb.exact_size < 0)
			      sb.exact_size = bound.const_bound;
			break;
		  case 'M':  // size >= N (minimum)
			if (sb.min_size < 0 || (int64_t)bound.const_bound > sb.min_size)
			      sb.min_size = bound.const_bound;
			break;
		  case 'm':  // size > N (strict minimum, means >= N+1)
			if (sb.min_size < 0 || (int64_t)(bound.const_bound + 1) > sb.min_size)
			      sb.min_size = bound.const_bound + 1;
			break;
		  case 'X':  // size <= N (maximum)
			if (sb.max_size < 0 || (int64_t)bound.const_bound < sb.max_size)
			      sb.max_size = bound.const_bound;
			break;
		  case 'x':  // size < N (strict maximum, means <= N-1)
			if (sb.max_size < 0 || (int64_t)(bound.const_bound - 1) < sb.max_size)
			      sb.max_size = bound.const_bound - 1;
			break;
		  default:
			break;
	    }
      };

      // Process class-level size constraints (including inherited)
      const class_type* cls = defn;
      while (cls != nullptr) {
	    for (size_t b = 0; b < cls->constraint_bound_count(); b++) {
		  const class_type::simple_bound_t& bound = cls->get_constraint_bound(b);
		  // Handle all size constraint operators
		  if (bound.op == 'S' || bound.op == 'M' || bound.op == 'X' ||
		      bound.op == 'm' || bound.op == 'x') {
			// Check condition before collecting size bound
			if (evaluate_condition(bound))
			      collect_size_bound(bound);
		  }
		  else if (bound.op == 's') {
			// Property-based size constraint - defer until source is randomized
			// If offset is negative, it indicates division (divisor = -offset)
			// Check condition before deferring
			if (evaluate_condition(bound)) {
			      deferred_size_constraint dsc;
			      dsc.prop_idx = bound.property_idx;
			      dsc.src_prop_idx = bound.bound_prop_idx;
			      dsc.offset = bound.const_bound;
			      dsc.elem_width = (unsigned)bound.weight;
			      if (dsc.elem_width == 0) dsc.elem_width = 8;
			      dsc.is_division = (bound.const_bound < 0);
			      if (dsc.is_division) dsc.offset = -bound.const_bound;  // Store positive divisor
			      deferred_size_constraints.push_back(dsc);
			}
		  }
	    }
	    cls = cls->get_parent();
      }

      // Process inline size constraints (from randomize() with {...})
      for (const auto& bound : inline_constraints) {
	    // Handle all size constraint operators
	    if (bound.op == 'S' || bound.op == 'M' || bound.op == 'X' ||
	        bound.op == 'm' || bound.op == 'x') {
		  collect_size_bound(bound);
	    }
	    else if (bound.op == 's') {
		  // Property-based size constraint - defer until source is randomized
		  // If offset is negative, it indicates division (divisor = -offset)
		  deferred_size_constraint dsc;
		  dsc.prop_idx = bound.property_idx;
		  dsc.src_prop_idx = bound.bound_prop_idx;
		  dsc.offset = bound.const_bound;
		  dsc.elem_width = (unsigned)bound.weight;
		  if (dsc.elem_width == 0) dsc.elem_width = 8;
		  dsc.is_division = (bound.const_bound < 0);
		  if (dsc.is_division) dsc.offset = -bound.const_bound;  // Store positive divisor
		  deferred_size_constraints.push_back(dsc);
	    }
      }

      // Apply collected size bounds - determine target sizes and resize arrays
      for (auto& pair : size_bounds) {
	    size_t prop_idx = pair.first;
	    size_bounds_t& sb = pair.second;
	    if (!sb.has_any) continue;

	    // Determine target size based on bounds
	    size_t target_size;
	    if (sb.exact_size >= 0) {
		  // Exact size constraint takes precedence
		  target_size = (size_t)sb.exact_size;
	    } else {
		  // Apply min/max bounds
		  int64_t min_s = (sb.min_size >= 0) ? sb.min_size : 0;
		  int64_t max_s = (sb.max_size >= 0) ? sb.max_size : 100;  // Default max if unbounded
		  if (max_s < min_s) max_s = min_s;  // Ensure valid range

		  // Pick random size in [min_s, max_s]
		  if (max_s == min_s) {
			target_size = (size_t)min_s;
		  } else {
			target_size = (size_t)(min_s + (rand() % (max_s - min_s + 1)));
		  }
	    }

	    // Get current object (if any)
	    vvp_object_t cur_obj;
	    cobj->get_object(prop_idx, cur_obj, 0);
	    vvp_darray* cur_dar = cur_obj.peek<vvp_darray>();

	    // If array doesn't exist or has wrong size, create a new one
	    if (cur_dar == 0 || cur_dar->get_size() != target_size) {
		  vvp_darray_vec4* new_dar = new vvp_darray_vec4(target_size, sb.elem_width);
		  vvp_object_t new_dar_obj(new_dar);
		  cobj->set_object(prop_idx, new_dar_obj, 0);
	    }

	    // Mark this property for element randomization
	    darray_props_to_randomize.insert(prop_idx);
	    darray_elem_widths[prop_idx] = sb.elem_width;
      }

      // Randomize elements of dynamic arrays with size constraints
      // Apply element constraints (>= and <= bounds from inline constraints)
      // Supports both global constraints (apply to all elements) and
      // element-specific constraints (e.g., data[0] == 42)
      for (size_t prop_idx : darray_props_to_randomize) {
	    vvp_object_t dar_obj;
	    cobj->get_object(prop_idx, dar_obj, 0);
	    vvp_darray* dar = dar_obj.peek<vvp_darray>();
	    if (dar) {
		  unsigned elem_width = darray_elem_widths[prop_idx];
		  size_t dar_size = dar->get_size();

		  // Default constraints for all elements (global constraints without element index)
		  int64_t default_elem_min = 0;
		  int64_t default_elem_max = (1LL << elem_width) - 1;
		  if (elem_width >= 64) default_elem_max = INT64_MAX;

		  // Collect global (non-indexed) excluded and discrete values
		  std::vector<int64_t> default_excluded_vals;
		  std::vector<int64_t> default_discrete_vals;

		  // Structure for weighted ranges in foreach dist constraints
		  struct elem_weighted_range_t {
			int64_t low, high, weight;
			bool weight_per_value;
		  };
		  std::vector<elem_weighted_range_t> default_weighted_ranges;

		  // Collect >= and <= bounds separately for weighted range pairing
		  struct weighted_bound_t { int64_t val; int64_t weight; bool weight_per_value; };
		  std::vector<weighted_bound_t> ge_bounds_elem;  // >= bounds
		  std::vector<weighted_bound_t> le_bounds_elem;  // <= bounds

		  // Lambda to process a constraint bound for dynamic array element constraints
		  auto process_darray_elem_bound = [&](const class_type::simple_bound_t& bound) {
			if (bound.property_idx != prop_idx) return;
			if (!bound.has_const_bound) return;
			if (bound.is_soft) return;
			// Skip size constraints - only element constraints
			if (bound.op == 'S' || bound.op == 's' || bound.op == 'M' ||
			    bound.op == 'X' || bound.op == 'm' || bound.op == 'x') return;
			// Skip element-indexed constraints here - handle them per-element
			if (bound.has_element_idx) return;

			// For weighted dist: collect bounds with weights for later pairing
			if (bound.weight > 1 || (bound.op == 'G' || bound.op == 'L')) {
			      if (bound.op == 'G') {
				    ge_bounds_elem.push_back({bound.const_bound, bound.weight, bound.weight_per_value});
				    return;
			      } else if (bound.op == 'L') {
				    le_bounds_elem.push_back({bound.const_bound, bound.weight, bound.weight_per_value});
				    return;
			      }
			}

			switch (bound.op) {
			      case '>':  // value > const
				    if (bound.const_bound + 1 > default_elem_min)
					  default_elem_min = bound.const_bound + 1;
				    break;
			      case 'G':  // value >= const (handled above for weighted)
				    if (bound.const_bound > default_elem_min)
					  default_elem_min = bound.const_bound;
				    break;
			      case '<':  // value < const
				    if (bound.const_bound - 1 < default_elem_max)
					  default_elem_max = bound.const_bound - 1;
				    break;
			      case 'L':  // value <= const (handled above for weighted)
				    if (bound.const_bound < default_elem_max)
					  default_elem_max = bound.const_bound;
				    break;
			      case '!':  // value != const (exclusion)
				    default_excluded_vals.push_back(bound.const_bound);
				    break;
			      case '=':  // value == const (discrete value)
				    default_discrete_vals.push_back(bound.const_bound);
				    break;
			      default:
				    break;
			}
		  };

		  // First, collect named constraints from the class hierarchy
		  // This enables named foreach constraints on dynamic arrays:
		  // constraint c { foreach(data[i]) data[i] != 0; }
		  const class_type* cls_iter = defn;
		  while (cls_iter != nullptr) {
			for (size_t b = 0; b < cls_iter->constraint_bound_count(); b++) {
			      const class_type::simple_bound_t& bound = cls_iter->get_constraint_bound(b);
			      // Skip disabled constraints (via constraint_mode)
			      if (!bound.constraint_name.empty() &&
				  !cobj->is_constraint_enabled(bound.constraint_name)) continue;
			      process_darray_elem_bound(bound);
			}
			cls_iter = cls_iter->get_parent();
		  }

		  // Then collect from inline constraints
		  for (const auto& bound : inline_constraints) {
			process_darray_elem_bound(bound);
		  }

		  // Pair >= and <= bounds into weighted ranges for foreach dist
		  // Sort both lists by value to pair corresponding bounds
		  std::sort(ge_bounds_elem.begin(), ge_bounds_elem.end(),
		            [](const weighted_bound_t& a, const weighted_bound_t& b) { return a.val < b.val; });
		  std::sort(le_bounds_elem.begin(), le_bounds_elem.end(),
		            [](const weighted_bound_t& a, const weighted_bound_t& b) { return a.val < b.val; });
		  // Pair bounds with matching weights
		  size_t ge_idx = 0;
		  for (const auto& le : le_bounds_elem) {
			if (ge_idx < ge_bounds_elem.size()) {
			      int64_t low = ge_bounds_elem[ge_idx].val;
			      int64_t high = le.val;
			      int64_t weight = ge_bounds_elem[ge_idx].weight;
			      bool weight_per_value = ge_bounds_elem[ge_idx].weight_per_value;
			      if (low <= high) {
				    default_weighted_ranges.push_back({low, high, weight, weight_per_value});
			      }
			      ge_idx++;
			}
		  }

		  // Ensure valid default range
		  if (default_elem_min > default_elem_max) default_elem_min = default_elem_max;
		  int64_t default_range = default_elem_max - default_elem_min + 1;

		  for (size_t idx = 0; idx < dar_size; idx++) {
			int64_t rval;

			// Collect element-specific constraints for this index
			int64_t elem_min = default_elem_min;
			int64_t elem_max = default_elem_max;
			std::vector<int64_t> excluded_vals = default_excluded_vals;
			std::vector<int64_t> discrete_vals = default_discrete_vals;
			bool has_specific_constraint = false;

			// Lambda to process an element-indexed bound
			auto process_element_bound = [&](const class_type::simple_bound_t& bound) {
			      if (bound.property_idx != prop_idx) return;
			      if (!bound.has_const_bound) return;
			      if (bound.is_soft) return;
			      // Only process element-indexed constraints
			      if (!bound.has_element_idx) return;
			      // Check if this constraint is for this specific element
			      if ((size_t)bound.element_idx != idx) return;

			      has_specific_constraint = true;
			      switch (bound.op) {
				    case '>':
					  if (bound.const_bound + 1 > elem_min)
						elem_min = bound.const_bound + 1;
					  break;
				    case 'G':
					  if (bound.const_bound > elem_min)
						elem_min = bound.const_bound;
					  break;
				    case '<':
					  if (bound.const_bound - 1 < elem_max)
						elem_max = bound.const_bound - 1;
					  break;
				    case 'L':
					  if (bound.const_bound < elem_max)
						elem_max = bound.const_bound;
					  break;
				    case '!':
					  excluded_vals.push_back(bound.const_bound);
					  break;
				    case '=':
					  discrete_vals.push_back(bound.const_bound);
					  break;
				    default:
					  break;
			      }
			};

			// First check class-level element-indexed constraints (including inherited)
			const class_type* cls_elem = defn;
			while (cls_elem != nullptr) {
			      for (size_t b = 0; b < cls_elem->constraint_bound_count(); b++) {
				    const class_type::simple_bound_t& bound = cls_elem->get_constraint_bound(b);
				    // Skip disabled constraints (via constraint_mode)
				    if (!bound.constraint_name.empty() &&
				        !cobj->is_constraint_enabled(bound.constraint_name)) continue;
				    process_element_bound(bound);
			      }
			      cls_elem = cls_elem->get_parent();
			}

			// Then check inline constraints
			for (const auto& bound : inline_constraints) {
			      process_element_bound(bound);
			}

			// Ensure valid range
			if (elem_min > elem_max) elem_min = elem_max;
			int64_t range = elem_max - elem_min + 1;

			// If we have discrete values from == constraints, use them
			if (!discrete_vals.empty()) {
			      // If multiple discrete values, pick one randomly for each element
			      // If single value, all elements get that value
			      if (discrete_vals.size() == 1) {
				    rval = discrete_vals[0];
			      } else {
				    rval = discrete_vals[rand() % discrete_vals.size()];
			      }
			} else if (!default_weighted_ranges.empty()) {
			      // Use weighted selection for foreach dist constraints
			      int64_t total_weight = 0;
			      for (const auto& r : default_weighted_ranges) {
				    if (r.weight_per_value) {
					  int64_t range_size = r.high - r.low + 1;
					  total_weight += r.weight * range_size;
				    } else {
					  total_weight += r.weight;
				    }
			      }
			      if (total_weight > 0) {
				    int64_t pick = rand() % total_weight;
				    int64_t cumulative = 0;
				    for (const auto& r : default_weighted_ranges) {
					  int64_t range_weight;
					  int64_t range_size = r.high - r.low + 1;
					  if (r.weight_per_value) {
						range_weight = r.weight * range_size;
					  } else {
						range_weight = r.weight;
					  }
					  cumulative += range_weight;
					  if (pick < cumulative) {
						// Pick random value in this range
						rval = r.low + (rand() % range_size);
						break;
					  }
				    }
			      } else {
				    // Fallback to simple range
				    rval = elem_min + (rand() % range);
			      }
			} else {
			      // Generate constrained random value, avoiding excluded values
			      int retries = 0;
			      const int max_retries = 100;
			      do {
				    rval = elem_min + (rand() % range);
				    // Check if value is excluded
				    bool is_excluded = false;
				    for (int64_t excl : excluded_vals) {
					  if (rval == excl) {
						is_excluded = true;
						break;
					  }
				    }
				    if (!is_excluded) break;
				    retries++;
			      } while (retries < max_retries);
			}

			vvp_vector4_t new_val(elem_width);
			for (unsigned b = 0; b < elem_width && b < 64; b++) {
			      new_val.set_bit(b, ((rval >> b) & 1) ? BIT4_1 : BIT4_0);
			}
			dar->set_word((unsigned)idx, new_val);
		  }
	    }
      }

      // Process array copy constraints (foreach element equality)
      // Track which properties were copied so we skip them during randomization
      std::set<size_t> copied_props;
      const std::map<unsigned, vvp_object_t>& array_copy_sources = thr->get_array_copy_sources();
      for (const auto& bound : inline_constraints) {
	    if (bound.op == 'C') {
		  size_t prop_idx = bound.property_idx;
		  auto src_it = array_copy_sources.find(prop_idx);
		  if (src_it != array_copy_sources.end()) {
			// Get source array
			vvp_darray* src_dar = src_it->second.peek<vvp_darray>();
			if (src_dar) {
			      size_t src_size = src_dar->get_size();
			      // Get target property, resize if needed
			      vvp_object_t target_obj;
			      cobj->get_object(prop_idx, target_obj, 0);
			      vvp_darray* target_dar = target_obj.peek<vvp_darray>();
			      // Create or resize target array
			      if (!target_dar || target_dar->get_size() != src_size) {
				    // Need to create new array - get element width from source
				    unsigned elem_width = 8;
				    if (src_size > 0) {
					  vvp_vector4_t first_elem;
					  src_dar->get_word(0, first_elem);
					  elem_width = first_elem.size();
				    }
				    vvp_darray_vec4* new_dar = new vvp_darray_vec4(src_size, elem_width);
				    vvp_object_t new_dar_obj(new_dar);
				    cobj->set_object(prop_idx, new_dar_obj, 0);
				    cobj->get_object(prop_idx, target_obj, 0);
				    target_dar = target_obj.peek<vvp_darray>();
			      }
			      // Copy elements
			      if (target_dar) {
				    for (size_t idx = 0; idx < src_size; idx++) {
					  vvp_vector4_t elem;
					  src_dar->get_word(idx, elem);
					  target_dar->set_word(idx, elem);
				    }
			      }
			      // Mark as copied so we skip normal randomization
			      copied_props.insert(prop_idx);
			}
		  }
	    }
      }

      // Try to find values that satisfy constraints
      int tries = 0;
      bool success = false;

      do {
	    // Generate random values for all rand properties
	    class_type::inst_t inst = cobj->get_instance();

	    for (size_t i = 0; i < nprop; i++) {
		  // Skip properties that were copied from source arrays
		  if (copied_props.count(i) > 0)
			continue;
		  // Only randomize properties marked with 'rand' or 'randc'
		  // Also respects per-instance rand_mode setting
		  if (!cobj->should_randomize(i))
			continue;

		  // Only randomize vec4-compatible properties (skip strings, objects, etc.)
		  if (!defn->property_supports_vec4(i))
			continue;

		  // Check if this is a randc property (cyclic randomization)
		  bool is_randc = cobj->is_randc(i);

		  // Get array size for this property (1 for scalars)
		  uint64_t array_size = defn->property_array_size(i);

		  // Check if this property has a unique constraint
		  bool has_unique = false;
		  for (size_t uc = 0; uc < defn->unique_constraint_count(); uc++) {
			if (defn->get_unique_constraint_prop(uc) == i) {
			      has_unique = true;
			      break;
			}
		  }

		  // Track used values for unique constraint
		  std::set<int64_t> unique_used_values;

		  // Randomize all array elements
		  for (uint64_t arr_idx = 0; arr_idx < array_size; arr_idx++) {
		  // Try to get the property as vec4 and randomize it
		  vvp_vector4_t val;
		  cobj->get_vec4(i, val, arr_idx);

		  // Generate random value
		  unsigned wid = val.size();
		  if (wid > 0) {
			vvp_vector4_t new_val (wid);

			// Calculate bounds from inline constraints for this property
			int64_t min_val = 0;
			int64_t max_val = (1LL << wid) - 1;
			if (wid >= 64) max_val = INT64_MAX;

			// Apply both inline AND class-level constraint bounds
			// Track excluded values for != constraints
			// Track discrete allowed values for == constraints (from inside/dist)
			// Track range pairs for multiple disjoint ranges (from dist with ranges)
			std::vector<int64_t> excluded_values;

			// For randc properties, add previously used values to exclusion list
			if (is_randc) {
			      const std::set<int64_t>& used_vals = cobj->randc_get_used(i);
			      // Check if all possible values have been used (cycle complete)
			      // For small widths, we can calculate total possible values
			      uint64_t total_values = (wid < 64) ? (1ULL << wid) : UINT64_MAX;
			      if (used_vals.size() >= total_values) {
				    // All values used - clear and start new cycle
				    cobj->randc_clear(i);
			      } else {
				    // Add used values to exclusion list
				    for (int64_t used : used_vals) {
					  excluded_values.push_back(used);
				    }
			      }
			}

			// For unique constraints, add values used in previous array elements
			if (has_unique) {
			      for (int64_t used : unique_used_values) {
				    excluded_values.push_back(used);
			      }
			}

			// Discrete values with weights: (value, weight)
			std::vector<std::pair<int64_t, int64_t>> discrete_values;
			std::vector<class_type::simple_bound_t> ge_bounds;  // >= bounds
			std::vector<class_type::simple_bound_t> le_bounds;  // <= bounds
			// Excluded ranges: (low, high) pairs
			std::vector<std::pair<int64_t, int64_t>> excluded_ranges;
			bool has_simple_bounds = false;

			// First collect class-level constraints (including inherited)
			const class_type* cls = defn;
			while (cls != nullptr) {
			      for (size_t b = 0; b < cls->constraint_bound_count(); b++) {
				    const class_type::simple_bound_t& bound = cls->get_constraint_bound(b);
				    if (bound.property_idx != i) continue;
				    if (!bound.has_const_bound) continue;
				    if (bound.is_soft) continue;
				    // Skip disabled constraints (via constraint_mode)
				    if (!bound.constraint_name.empty() &&
					!cobj->is_constraint_enabled(bound.constraint_name)) continue;
				    // Skip system function constraints - handled by generate_constrained_random()
				    if (bound.sysfunc_type != class_type::SYSFUNC_NONE) continue;
				    // Skip property+offset bounds - handled by generate_constrained_random()
				    if (bound.has_prop_offset) continue;
				    switch (bound.op) {
					  case '>':
						if (bound.const_bound + 1 > min_val)
						      min_val = bound.const_bound + 1;
						has_simple_bounds = true;
						break;
					  case 'G':
						ge_bounds.push_back(bound);
						break;
					  case '<':
						if (bound.const_bound - 1 < max_val)
						      max_val = bound.const_bound - 1;
						has_simple_bounds = true;
						break;
					  case 'L':
						le_bounds.push_back(bound);
						break;
					  case '=':
						discrete_values.push_back({bound.const_bound, bound.weight});
						break;
					  case '!':
						excluded_values.push_back(bound.const_bound);
						break;
					  default:
						break;
				    }
			      }
			      cls = cls->get_parent();
			}

			// Then add inline constraints
			for (const auto& bound : inline_constraints) {
#ifdef DEBUG_CONSTRAINTS
			      fprintf(stderr, "DEBUG: Inline constraint: prop_idx=%zu, op='%c', has_const=%d, const_bound=%lld (checking prop %zu)\n",
			              bound.property_idx, bound.op, bound.has_const_bound, (long long)bound.const_bound, i);
#endif
			      if (bound.property_idx != i) continue;
			      // Handle excluded ranges specially (they don't use has_const_bound)
			      if (bound.is_excluded_range) {
				    if (!bound.is_soft) {
					  excluded_ranges.push_back({bound.excluded_range_low, bound.excluded_range_high});
				    }
				    continue;
			      }
			      if (!bound.has_const_bound) continue;
			      // For value generation, only use hard constraints (non-soft)
			      // Soft constraints are checked afterwards but don't fail randomize()
			      if (bound.is_soft) continue;
			      switch (bound.op) {
				    case '>':  // value > const  =>  min = const+1
					  if (bound.const_bound + 1 > min_val)
						min_val = bound.const_bound + 1;
					  has_simple_bounds = true;
					  break;
				    case 'G':  // value >= const
					  ge_bounds.push_back(bound);
					  break;
				    case '<':  // value < const  =>  max = const-1
					  if (bound.const_bound - 1 < max_val)
						max_val = bound.const_bound - 1;
					  has_simple_bounds = true;
					  break;
				    case 'L':  // value <= const
					  le_bounds.push_back(bound);
					  break;
				    case '=':  // value == const  =>  discrete allowed value
					  discrete_values.push_back({bound.const_bound, bound.weight});
					  break;
				    case '!':  // value != const  =>  exclude value
					  excluded_values.push_back(bound.const_bound);
					  break;
				    default:
					  break;
			      }
			}

			// Build range list from paired >= and <= bounds
			// Ranges with weights: (low, high, weight, weight_per_value)
			struct weighted_range_t {
			      int64_t low, high, weight;
			      bool weight_per_value;
			};
			std::vector<weighted_range_t> ranges;
			if (!ge_bounds.empty() || !le_bounds.empty()) {
			      // Pair up bounds in order (from dist items)
			      size_t ge_idx = 0, le_idx = 0;
			      while (ge_idx < ge_bounds.size() || le_idx < le_bounds.size()) {
				    int64_t low = min_val, high = max_val;
				    int64_t weight = 1;
				    bool weight_per_value = true;
				    if (ge_idx < ge_bounds.size()) {
					  low = ge_bounds[ge_idx].const_bound;
					  weight = ge_bounds[ge_idx].weight;
					  weight_per_value = ge_bounds[ge_idx].weight_per_value;
					  ge_idx++;
				    }
				    if (le_idx < le_bounds.size()) {
					  high = le_bounds[le_idx++].const_bound;
				    }
				    // Clamp to variable bounds
				    if (low < min_val) low = min_val;
				    if (high > max_val) high = max_val;
				    if (low <= high) {
					  ranges.push_back({low, high, weight, weight_per_value});
				    }
			      }
			}

			// Determine generation strategy
			int64_t rval;
			bool generated = false;

			// Helper to check if value is excluded (by single values or ranges)
			auto is_value_excluded = [&](int64_t val) -> bool {
			      for (auto excl : excluded_values) {
				    if (val == excl) return true;
			      }
			      for (auto& rng : excluded_ranges) {
				    if (val >= rng.first && val <= rng.second) return true;
			      }
			      return false;
			};

#ifdef DEBUG_CONSTRAINTS
			fprintf(stderr, "DEBUG: Property %zu: discrete_values.size()=%zu\n", i, discrete_values.size());
			for (size_t dvi = 0; dvi < discrete_values.size(); dvi++) {
			      fprintf(stderr, "DEBUG:   discrete_value[%zu] = %lld (weight=%lld)\n", dvi,
			              (long long)discrete_values[dvi].first, (long long)discrete_values[dvi].second);
			}
#endif

			// Priority 0: Weighted dist constraints - handle both discrete values AND ranges together
			// When dist constraints are present (weights > 1), we need to do weighted selection
			// across both discrete values and ranges, not just discrete values alone.
			// Check if this looks like a dist constraint (weights > 1)
			bool has_weighted_dist = false;
			for (const auto& dv : discrete_values) {
			      if (dv.second > 1) { has_weighted_dist = true; break; }
			}
			for (const auto& r : ranges) {
			      if (r.weight > 1) { has_weighted_dist = true; break; }
			}

			if (has_weighted_dist && (!discrete_values.empty() || !ranges.empty())) {
			      // Calculate total weight from both discrete values and ranges
			      int64_t total_weight = 0;
			      for (const auto& dv : discrete_values) {
				    total_weight += dv.second;
			      }
			      for (const auto& r : ranges) {
				    if (r.weight_per_value) {
					  // := means weight per value
					  int64_t range_size = r.high - r.low + 1;
					  total_weight += r.weight * range_size;
				    } else {
					  // :/ means weight per range
					  total_weight += r.weight;
				    }
			      }

			      // Weighted random selection
			      int64_t pick = rand() % total_weight;
			      int64_t cumulative = 0;

			      // First check discrete values
			      bool found = false;
			      for (size_t j = 0; j < discrete_values.size(); j++) {
				    cumulative += discrete_values[j].second;
				    if (pick < cumulative) {
					  rval = discrete_values[j].first;
					  found = true;
					  break;
				    }
			      }

			      // Then check ranges
			      if (!found) {
				    for (size_t j = 0; j < ranges.size(); j++) {
					  int64_t range_weight;
					  if (ranges[j].weight_per_value) {
						int64_t range_size = ranges[j].high - ranges[j].low + 1;
						range_weight = ranges[j].weight * range_size;
					  } else {
						range_weight = ranges[j].weight;
					  }
					  cumulative += range_weight;
					  if (pick < cumulative) {
						// Selected this range - pick random value within it
						int64_t low = ranges[j].low;
						int64_t high = ranges[j].high;
						int64_t range_size = high - low + 1;
						rval = low + (rand() % range_size);
						found = true;
						break;
					  }
				    }
			      }

			      if (!found && !discrete_values.empty()) {
				    // Fallback to last discrete value
				    rval = discrete_values.back().first;
			      } else if (!found && !ranges.empty()) {
				    // Fallback to last range
				    int64_t low = ranges.back().low;
				    int64_t high = ranges.back().high;
				    rval = low + (rand() % (high - low + 1));
			      }
			      generated = true;
#ifdef DEBUG_CONSTRAINTS
			      fprintf(stderr, "DEBUG: Property %zu: Using weighted dist value %lld\n", i, (long long)rval);
#endif
			}
			// Non-weighted discrete values (from inline constraints like x == val)
			// These take highest priority as they represent explicit value requests
			else if (!discrete_values.empty()) {
			      // Calculate total weight
			      int64_t total_weight = 0;
			      for (const auto& dv : discrete_values) {
				    total_weight += dv.second;
			      }
			      // Weighted random selection
			      int64_t pick = rand() % total_weight;
			      int64_t cumulative = 0;
			      size_t selected = 0;
			      for (size_t j = 0; j < discrete_values.size(); j++) {
				    cumulative += discrete_values[j].second;
				    if (pick < cumulative) {
					  selected = j;
					  break;
				    }
			      }
			      rval = discrete_values[selected].first;
			      generated = true;
#ifdef DEBUG_CONSTRAINTS
			      fprintf(stderr, "DEBUG: Property %zu: Using discrete value %lld\n", i, (long long)rval);
#endif
			}

			// Priority 1: Enum bounds - pick from valid enum values only
			// (only if no explicit value constraint from Priority 0)
			if (!generated) {
			      const std::vector<int64_t>* enum_vals = defn->get_enum_values(i);
			      if (enum_vals != nullptr && !enum_vals->empty()) {
				    // Filter out excluded values (for randc/unique)
				    std::vector<int64_t> available_vals;
				    for (int64_t ev : *enum_vals) {
					  bool is_excluded = false;
					  for (int64_t excl : excluded_values) {
						if (ev == excl) { is_excluded = true; break; }
					  }
					  if (!is_excluded) available_vals.push_back(ev);
				    }
				    // If all enum values are excluded (randc cycle complete),
				    // clear and use all values
				    if (available_vals.empty()) {
					  if (is_randc) {
						cobj->randc_clear(i);
						excluded_values.clear();
					  }
					  available_vals = *enum_vals;
				    }
				    // Pick a random valid enum value
				    size_t idx = rand() % available_vals.size();
				    rval = available_vals[idx];
				    generated = true;
			      }
			}
			// Priority 1.5: Inside array constraint - pick from array elements
			// Handles patterns like: x inside {arr} where arr is a dynamic array
			if (!generated) {
			      for (const auto& bound : inline_constraints) {
				    if (bound.property_idx == i && bound.is_inside_array) {
					  // Get the array from inside_array_prop_idx
					  size_t arr_prop_idx = bound.inside_array_prop_idx;
					  if (arr_prop_idx < defn->property_count()) {
						vvp_object_t arr_obj;
						defn->get_object(inst, arr_prop_idx, arr_obj, 0);
						vvp_darray* darray_ptr = arr_obj.peek<vvp_darray>();
						if (darray_ptr && darray_ptr->get_size() > 0) {
						      // Pick a random element from the array
						      size_t arr_size = darray_ptr->get_size();
						      size_t arr_idx = rand() % arr_size;
						      vvp_vector4_t elem_val;
						      darray_ptr->get_word(arr_idx, elem_val);
						      // Convert to int64_t
						      rval = 0;
						      for (unsigned bi = 0; bi < elem_val.size() && bi < 64; bi++) {
							    if (elem_val.value(bi) == BIT4_1)
								  rval |= (int64_t(1) << bi);
						      }
						      generated = true;
						      break;
						}
					  }
				    }
			      }
			}
			// Priority 2: Multiple disjoint ranges (from dist {[a:b], [c:d], ...})
			// Use weighted random selection based on range weights
			if (!generated && !ranges.empty()) {
			      // Calculate total weight (considering weight_per_value)
			      int64_t total_weight = 0;
			      for (const auto& r : ranges) {
				    if (r.weight_per_value) {
					  // := means weight per value, so multiply by range size
					  int64_t range_size = r.high - r.low + 1;
					  total_weight += r.weight * range_size;
				    } else {
					  // :/ means weight divided across range
					  total_weight += r.weight;
				    }
			      }
			      // Weighted random selection of range
			      int64_t pick = rand() % total_weight;
			      int64_t cumulative = 0;
			      size_t range_idx = 0;
			      for (size_t j = 0; j < ranges.size(); j++) {
				    int64_t range_weight;
				    if (ranges[j].weight_per_value) {
					  int64_t range_size = ranges[j].high - ranges[j].low + 1;
					  range_weight = ranges[j].weight * range_size;
				    } else {
					  range_weight = ranges[j].weight;
				    }
				    cumulative += range_weight;
				    if (pick < cumulative) {
					  range_idx = j;
					  break;
				    }
			      }
			      int64_t low = ranges[range_idx].low;
			      int64_t high = ranges[range_idx].high;
			      int64_t range_size = high - low + 1;
			      int avoid_tries = 0;
			      do {
				    rval = low + (rand() % range_size);
				    if (!is_value_excluded(rval)) break;
				    avoid_tries++;
			      } while (avoid_tries < 100);
			      generated = true;
			}
			// Priority 3: Class-level constraints combined with inline bounds
			// Only execute if no value has been generated yet (e.g., by discrete values)
			if (!generated && has_class_constraints) {
			      rval = defn->generate_constrained_random(inst, i, wid, cobj, inline_constraints);
			      // Combine with inline bounds and excluded values/ranges
			      bool valid = (rval >= min_val && rval <= max_val);
			      if (valid) {
				    valid = !is_value_excluded(rval);
			      }
			      if (!valid && min_val <= max_val) {
				    // Regenerate within inline bounds, avoiding excluded values/ranges
				    int64_t range = max_val - min_val + 1;
				    int avoid_tries = 0;
				    do {
					  rval = min_val + (rand() % range);
					  if (!is_value_excluded(rval)) break;
					  avoid_tries++;
				    } while (avoid_tries < 100);
			      }
			      generated = true;
			}
			// Priority 4: Range constraints from class or inline (> and < bounds)
			// Only execute if no value has been generated yet
			if (!generated && (has_inline_constraints || has_class_constraints) && min_val <= max_val) {
			      // Generate within constraint bounds
			      int64_t range = max_val - min_val + 1;
			      int avoid_tries = 0;
			      do {
				    rval = min_val + (rand() % range);
				    if (!is_value_excluded(rval)) break;
				    avoid_tries++;
			      } while (avoid_tries < 100);
			      generated = true;
			}
			// Priority 5: No constraints - purely random
			// For randc, still need to exclude used values
			// Also need to check excluded ranges
			if (!generated) {
			      bool has_exclusions = (is_randc || has_unique) && (!excluded_values.empty() || !excluded_ranges.empty());
			      int avoid_tries = 0;
			      do {
				    // Generate purely random bits
				    for (unsigned b = 0; b < wid; b++) {
					  new_val.set_bit(b, (rand() & 1) ? BIT4_1 : BIT4_0);
				    }
				    // Check if value is in excluded_values or excluded_ranges
				    if (has_exclusions || !excluded_ranges.empty()) {
					  // Extract generated value
					  rval = 0;
					  for (unsigned b = 0; b < wid && b < 64; b++) {
						if (new_val.value(b) == BIT4_1)
						      rval |= (1LL << b);
					  }
					  if (!is_value_excluded(rval)) {
						generated = true;
						break;
					  }
					  avoid_tries++;
				    } else {
					  break;  // No exclusions to check
				    }
			      } while (avoid_tries < 100);
			}

			// Apply generated value to new_val
			if (generated) {
			      for (unsigned b = 0; b < wid && b < 64; b++) {
				    new_val.set_bit(b, (rval & (1LL << b)) ? BIT4_1 : BIT4_0);
			      }
			}
			cobj->set_vec4(i, new_val, arr_idx);

			// For randc properties, mark the generated value as used
			if (is_randc) {
			      int64_t used_val;
			      if (generated) {
				    used_val = rval;
			      } else {
				    // Extract value from new_val for purely random generation
				    used_val = 0;
				    for (unsigned b = 0; b < wid && b < 64; b++) {
					  if (new_val.value(b) == BIT4_1)
						used_val |= (1LL << b);
				    }
			      }
			      cobj->randc_mark_used(i, used_val);
			}

			// For unique constraints, track the value for this array element
			if (has_unique) {
			      int64_t used_val;
			      if (generated) {
				    used_val = rval;
			      } else {
				    // Extract value from new_val for purely random generation
				    used_val = 0;
				    for (unsigned b = 0; b < wid && b < 64; b++) {
					  if (new_val.value(b) == BIT4_1)
						used_val |= (1LL << b);
				    }
			      }
			      unique_used_values.insert(used_val);
			}
		  }
		  } // end for arr_idx
	    }

	    // Check constraints (handles != and cross-property constraints)
	    success = true;
	    if (has_class_constraints) {
		  // Check if generated values satisfy all class-level constraints
		  // Pass cobj so it can check constraint_mode for each named constraint
		  success = defn->check_constraints(inst, cobj);
	    }
	    // Also check inline constraints
	    // Special handling: multiple '=' constraints on same property are OR'd
	    // (e.g., from "inside {1, 3, 5}" or "dist {1, 3, 5}")
	    if (success && has_inline_constraints) {
		  // Group '=' constraints by property index, tracking if any are hard
		  struct eq_info {
			std::vector<int64_t> values;
			bool has_hard;  // true if any '=' constraint is hard (non-soft)
		  };
		  std::map<size_t, eq_info> eq_constraints;
		  std::vector<class_type::simple_bound_t> other_constraints;

		  for (const auto& bound : inline_constraints) {
			if (bound.property_idx >= nprop) continue;
			if (!bound.has_const_bound) continue;

			// Skip size constraints - they're handled separately
			// and don't need constraint checking
			if (bound.op == 'S' || bound.op == 'M' || bound.op == 'X' ||
			    bound.op == 'm' || bound.op == 'x') continue;

			// Skip constraints on properties that don't support vec4
			// (e.g., object types like dynamic arrays)
			if (!defn->property_supports_vec4(bound.property_idx)) continue;

			if (bound.op == '=') {
			      auto& info = eq_constraints[bound.property_idx];
			      info.values.push_back(bound.const_bound);
			      if (!bound.is_soft) info.has_hard = true;
			} else {
			      other_constraints.push_back(bound);
			}
		  }

		  // Check '=' constraints with OR logic (value matches ANY allowed value)
		  // Only fail if there are hard '=' constraints that don't match
		  for (const auto& kv : eq_constraints) {
			size_t prop_idx = kv.first;
			const eq_info& info = kv.second;

			// If all '=' constraints for this property are soft, skip checking
			if (!info.has_hard) continue;

			vvp_vector4_t val;
			cobj->get_vec4(prop_idx, val);
			int64_t prop_val = 0;
			for (unsigned b = 0; b < val.size() && b < 64; b++) {
			      if (val.value(b) == BIT4_1)
				    prop_val |= (1LL << b);
			}

			bool any_match = false;
			for (int64_t allowed_val : info.values) {
			      if (prop_val == allowed_val) {
				    any_match = true;
				    break;
			      }
			}

			if (!any_match) {
			      success = false;
			      break;
			}
		  }

		  // Check other constraints - handle range pairs with OR logic
		  // Multiple ranges from dist like {[0:10], [200:$]} need OR between ranges
		  if (success) {
			// Group bounds by property for range detection, tracking if any are hard
			struct range_info {
			      std::vector<class_type::simple_bound_t> bounds;
			      bool has_hard;  // true if any range bound is hard
			};
			std::map<size_t, range_info> prop_bounds;
			std::vector<class_type::simple_bound_t> simple_constraints;

			for (const auto& bound : other_constraints) {
			      // >= and <= are range bounds, pair them
			      if (bound.op == 'G' || bound.op == 'L') {
				    auto& info = prop_bounds[bound.property_idx];
				    info.bounds.push_back(bound);
				    if (!bound.is_soft) info.has_hard = true;
			      } else {
				    simple_constraints.push_back(bound);
			      }
			}

			// Check range bounds - group into pairs and OR between pairs
			// Only fail if there are hard range constraints
			for (const auto& kv : prop_bounds) {
			      size_t prop_idx = kv.first;
			      const range_info& info = kv.second;

			      // If all range constraints for this property are soft, skip checking
			      if (!info.has_hard) continue;

			      vvp_vector4_t val;
			      cobj->get_vec4(prop_idx, val);
			      int64_t prop_val = 0;
			      for (unsigned b = 0; b < val.size() && b < 64; b++) {
				    if (val.value(b) == BIT4_1)
					  prop_val |= (1LL << b);
			      }

			      // Pair up >= and <= bounds into ranges
			      std::vector<std::pair<int64_t, int64_t>> ranges;
			      int64_t pending_low = INT64_MIN;
			      bool have_low = false;

			      for (const auto& b : info.bounds) {
				    if (b.op == 'G') {  // >=
					  if (have_low) {
						// Two lows in a row - start new range
						ranges.push_back({pending_low, INT64_MAX});
					  }
					  pending_low = b.const_bound;
					  have_low = true;
				    } else if (b.op == 'L') {  // <=
					  if (have_low) {
						ranges.push_back({pending_low, b.const_bound});
						have_low = false;
					  } else {
						// <= without >= is [INT64_MIN, high]
						ranges.push_back({INT64_MIN, b.const_bound});
					  }
				    }
			      }
			      if (have_low) {
				    ranges.push_back({pending_low, INT64_MAX});
			      }

			      // Check if value is in ANY range (OR logic)
			      bool in_any_range = false;
			      for (const auto& range : ranges) {
				    if (prop_val >= range.first && prop_val <= range.second) {
					  in_any_range = true;
					  break;
				    }
			      }

			      if (!in_any_range && !ranges.empty()) {
				    success = false;
				    break;
			      }
			}

			// Check simple constraints (>, <, !=) with AND logic
			if (success) {
			      for (const auto& bound : simple_constraints) {
				    vvp_vector4_t val;
				    cobj->get_vec4(bound.property_idx, val);
				    int64_t prop_val = 0;
				    for (unsigned b = 0; b < val.size() && b < 64; b++) {
					  if (val.value(b) == BIT4_1)
						prop_val |= (1LL << b);
				    }

				    bool constraint_ok = true;
				    switch (bound.op) {
					  case '>': constraint_ok = (prop_val > bound.const_bound); break;
					  case '<': constraint_ok = (prop_val < bound.const_bound); break;
					  case '!': constraint_ok = (prop_val != bound.const_bound); break;
					  default: break;
				    }
				    if (!constraint_ok && !bound.is_soft) {
					  success = false;
					  break;
				    }
			      }
			}
		  }
	    }

	    tries++;
      } while (!success && tries < MAX_CONSTRAINT_TRIES);

      // Now that source properties are randomized, apply deferred property-based size constraints
      for (const auto& dsc : deferred_size_constraints) {
	    // Read the source property value (now randomized)
	    vvp_vector4_t src_val;
	    cobj->get_vec4(dsc.src_prop_idx, src_val);
	    int64_t src_int = 0;
	    for (unsigned b = 0; b < src_val.size() && b < 64; b++) {
		  if (src_val.value(b) == BIT4_1) src_int |= (1LL << b);
	    }

	    // Calculate target size
	    int64_t target_size_s;
	    if (dsc.is_division) {
		  // Size = src_prop / divisor
		  if (dsc.offset != 0) {
			target_size_s = src_int / dsc.offset;
		  } else {
			target_size_s = 0;  // Division by zero protection
		  }
	    } else {
		  // Size = src_prop + offset
		  target_size_s = src_int + dsc.offset;
	    }
	    if (target_size_s < 0) target_size_s = 0;  // Can't have negative size
	    size_t target_size = (size_t)target_size_s;

	    // Get current object (if any)
	    vvp_object_t cur_obj;
	    cobj->get_object(dsc.prop_idx, cur_obj, 0);
	    vvp_darray* cur_dar = cur_obj.peek<vvp_darray>();

	    // If array doesn't exist or has wrong size, create a new one
	    if (cur_dar == 0 || cur_dar->get_size() != target_size) {
		  vvp_darray_vec4* new_dar = new vvp_darray_vec4(target_size, dsc.elem_width);
		  vvp_object_t new_dar_obj(new_dar);
		  cobj->set_object(dsc.prop_idx, new_dar_obj, 0);
		  cur_dar = new_dar;
	    }

	    // Randomize elements of the newly sized array
	    if (cur_dar) {
		  for (size_t idx = 0; idx < target_size; idx++) {
			vvp_vector4_t new_val(dsc.elem_width);
			for (unsigned b = 0; b < dsc.elem_width; b++) {
			      new_val.set_bit(b, (rand() & 1) ? BIT4_1 : BIT4_0);
			}
			cur_dar->set_word((unsigned)idx, new_val);
		  }
	    }
      }

      // Call post_randomize() callback if defined
      call_randomize_callback(thr, cobj, obj, "post_randomize");

      // Push result to vec4 stack: 1 for success, 0 for failure
      vvp_vector4_t res (32, BIT4_0);
      if (success) {
	    res.set_bit(0, BIT4_1);
      }
      // Clear inline constraints after use
      thr->clear_inline_constraints();

      thr->push_vec4(res);

      return true;
}

/*
 * %rand_mode/get <property_idx>
 *
 * Pop object from stack, get rand_mode for property, push result (0 or 1).
 */
bool of_RAND_MODE_GET(vthread_t thr, vvp_code_t cp)
{
      unsigned prop_idx = cp->number;

      vvp_object_t obj;
      thr->pop_object(obj);
      vvp_cobject* cobj = obj.peek<vvp_cobject>();

      int mode = 1;  // Default: enabled
      if (cobj != nullptr) {
	    mode = cobj->get_rand_mode(prop_idx);
      }

      // Push result as vec4
      vvp_vector4_t res(32, BIT4_0);
      if (mode)
	    res.set_bit(0, BIT4_1);
      thr->push_vec4(res);

      return true;
}

/*
 * %rand_mode/set <property_idx>, <mode>
 *
 * Pop object from stack, set rand_mode for property.
 * mode: 0 = disabled, 1 = enabled
 */
bool of_RAND_MODE_SET(vthread_t thr, vvp_code_t cp)
{
      unsigned prop_idx = cp->number;
      int mode = cp->bit_idx[0];

      vvp_object_t obj;
      thr->pop_object(obj);
      vvp_cobject* cobj = obj.peek<vvp_cobject>();

      if (cobj != nullptr) {
	    cobj->set_rand_mode(prop_idx, mode);
      }

      return true;
}

/*
 * %constraint_mode/get "<constraint_name>"
 *
 * Pop object from stack, get constraint_mode for named constraint, push result (0 or 1).
 */
bool of_CONSTRAINT_MODE_GET(vthread_t thr, vvp_code_t cp)
{
      const char* constraint_name = cp->text ? cp->text : "";

      vvp_object_t obj;
      thr->pop_object(obj);
      vvp_cobject* cobj = obj.peek<vvp_cobject>();

      int mode = 1;  // Default: enabled
      if (cobj != nullptr) {
	    mode = cobj->get_constraint_mode(constraint_name);
      }

      // Push result as vec4
      vvp_vector4_t res(32, BIT4_0);
      if (mode)
	    res.set_bit(0, BIT4_1);
      thr->push_vec4(res);

      return true;
}

/*
 * %constraint_mode/set "<constraint_name>", <mode>
 *
 * Pop object from stack, set constraint_mode for named constraint.
 * mode: 0 = disabled, 1 = enabled
 */
bool of_CONSTRAINT_MODE_SET(vthread_t thr, vvp_code_t cp)
{
      const char* constraint_name = cp->text ? cp->text : "";
      int mode = cp->bit_idx[0];

      vvp_object_t obj;
      thr->pop_object(obj);
      vvp_cobject* cobj = obj.peek<vvp_cobject>();

      if (cobj != nullptr) {
	    cobj->set_constraint_mode(constraint_name, mode);
      }

      return true;
}

/*
 * Semaphore support
 *
 * A semaphore is a synchronization primitive with an internal key count.
 * - new(count): creates a semaphore with initial count
 * - get(n): decrements count by n, blocks if count < n
 * - put(n): increments count by n, wakes waiting threads
 * - try_get(n): returns 1 if count >= n and decrements, else returns 0
 *
 * Blocking is implemented by adding waiting threads to a list in the semaphore.
 * When put() increases the count, waiting threads are woken in FIFO order.
 */

// Track a waiting thread and how many keys it needs
struct semaphore_waiter_s {
      vthread_t thread;
      int keys_needed;
      semaphore_waiter_s* next;
};

// Semaphore object class - derives from vvp_object for garbage collection
class vvp_semaphore : public vvp_object {
    public:
      explicit vvp_semaphore(int initial_count = 0)
	    : count_(initial_count), waiters_(nullptr), waiters_tail_(&waiters_) {}

      ~vvp_semaphore() {
	    // Clean up any remaining waiters (shouldn't happen normally)
	    while (waiters_) {
		  semaphore_waiter_s* next = waiters_->next;
		  delete waiters_;
		  waiters_ = next;
	    }
      }

      int get_count() const { return count_; }

      // Put keys back and wake waiting threads
      void put(int n) {
	    count_ += n;
	    wake_waiters();
      }

      bool try_get(int n) {
	    if (count_ >= n) {
		  count_ -= n;
		  return true;
	    }
	    return false;
      }

      // Add a thread to wait for keys
      void add_waiter(vthread_t thr, int n) {
	    semaphore_waiter_s* waiter = new semaphore_waiter_s;
	    waiter->thread = thr;
	    waiter->keys_needed = n;
	    waiter->next = nullptr;
	    *waiters_tail_ = waiter;
	    waiters_tail_ = &waiter->next;
      }

      // Check if we can satisfy the request immediately
      bool can_get(int n) const { return count_ >= n; }

      // Do the get (call only after can_get returns true)
      void do_get(int n) { count_ -= n; }

      // Required by vvp_object base class
      void shallow_copy(const vvp_object*) override { }
      vvp_object* duplicate(void) const override { return new vvp_semaphore(count_); }

    private:
      void wake_waiters() {
	    // Wake threads in FIFO order as long as we have enough keys
	    while (waiters_ && count_ >= waiters_->keys_needed) {
		  semaphore_waiter_s* waiter = waiters_;
		  waiters_ = waiter->next;
		  if (waiters_ == nullptr) {
			waiters_tail_ = &waiters_;
		  }

		  // Decrement count by keys needed
		  count_ -= waiter->keys_needed;

		  // Wake the thread
		  vthread_t thr = waiter->thread;
		  thr->waiting_for_event = 0;
		  schedule_vthread(thr, 0);

		  delete waiter;
	    }
      }

      int count_;
      semaphore_waiter_s* waiters_;
      semaphore_waiter_s** waiters_tail_;
};

/*
 * %semaphore/new <reg>
 *
 * Create a new semaphore with initial count from integer register <reg>.
 * Push the semaphore object to the object stack.
 */
bool of_SEMAPHORE_NEW(vthread_t thr, vvp_code_t cp)
{
      int count = thr->words[cp->bit_idx[0]].w_int;

      // Create a real semaphore object with the initial count
      vvp_semaphore* sem = new vvp_semaphore(count);
      vvp_object_t obj(sem);
      thr->push_object(obj);

      return true;
}

/*
 * %semaphore/get <reg>
 *
 * Pop semaphore from stack, decrement count by value in integer register <reg>.
 * If count < n, block until put() increases count sufficiently.
 */
bool of_SEMAPHORE_GET(vthread_t thr, vvp_code_t cp)
{
      assert(! thr->i_am_in_function);

      int n = thr->words[cp->bit_idx[0]].w_int;

      // Peek the semaphore from stack (code generator emits %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_semaphore* sem = obj.peek<vvp_semaphore>();
      if (sem == nullptr) {
	    return true;  // Null semaphore - just continue
      }

      // If we have enough keys, decrement and continue
      if (sem->can_get(n)) {
	    sem->do_get(n);
	    return true;
      }

      // Not enough keys - block until put() provides them
      // Mark thread as waiting for event
      assert(! thr->waiting_for_event);
      thr->waiting_for_event = 1;

      // Add thread to semaphore's waiting list
      sem->add_waiter(thr, n);

      // Return false to suspend this thread
      return false;
}

/*
 * %semaphore/put <reg>
 *
 * Pop semaphore from stack, increment count by value in integer register <reg>.
 */
bool of_SEMAPHORE_PUT(vthread_t thr, vvp_code_t cp)
{
      int n = thr->words[cp->bit_idx[0]].w_int;

      // Peek the semaphore from stack (code generator emits %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_semaphore* sem = obj.peek<vvp_semaphore>();
      if (sem) {
	    // Increment count
	    sem->put(n);
      }

      return true;
}

/*
 * %semaphore/try_get <reg>
 *
 * Pop semaphore from stack. If count >= n, decrement and push 1.
 * Otherwise push 0.
 */
bool of_SEMAPHORE_TRY_GET(vthread_t thr, vvp_code_t cp)
{
      int n = thr->words[cp->bit_idx[0]].w_int;

      // Peek the semaphore from stack (code generator emits %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_semaphore* sem = obj.peek<vvp_semaphore>();

      vvp_vector4_t res(32, BIT4_0);
      if (sem && sem->try_get(n)) {
	    // Successfully got the keys
	    res.set_bit(0, BIT4_1);  // Return 1 (success)
      }
      // Otherwise return 0 (failed - not enough keys)
      thr->push_vec4(res);

      return true;
}

/*
 * Mailbox support
 *
 * A mailbox is a message queue for inter-process communication.
 * Messages are stored as 32-bit integers (vec4 values).
 * Bounded mailboxes have a maximum capacity.
 *
 * Blocking is implemented by adding waiting threads to a list in the mailbox.
 * When put() adds a message, waiting get threads are woken in FIFO order.
 * When get() removes a message from a full bounded mailbox, waiting put threads are woken.
 */

// Track a waiting thread for mailbox get/put
struct mailbox_waiter_s {
      vthread_t thread;
      int32_t message;       // For put waiters: the message they want to put
      mailbox_waiter_s* next;
};

// Mailbox object class - derives from vvp_object for garbage collection
class vvp_mailbox : public vvp_object {
    public:
      explicit vvp_mailbox(int bound = 0)
	    : bound_(bound),
	      get_waiters_(nullptr), get_waiters_tail_(&get_waiters_),
	      put_waiters_(nullptr), put_waiters_tail_(&put_waiters_) {}

      ~vvp_mailbox() {
	    // Clean up any remaining waiters
	    while (get_waiters_) {
		  mailbox_waiter_s* next = get_waiters_->next;
		  delete get_waiters_;
		  get_waiters_ = next;
	    }
	    while (put_waiters_) {
		  mailbox_waiter_s* next = put_waiters_->next;
		  delete put_waiters_;
		  put_waiters_ = next;
	    }
      }

      int get_bound() const { return bound_; }
      int num() const { return (int)messages_.size(); }

      // Check if mailbox is full (bounded) or can accept more messages
      bool is_full() const {
	    if (bound_ <= 0) return false;  // Unbounded
	    return (int)messages_.size() >= bound_;
      }

      // Check if mailbox is empty
      bool is_empty() const { return messages_.empty(); }

      // Put a message into the mailbox and wake any waiting get threads
      // Returns true if successful, false if bounded mailbox is full
      bool put(int32_t msg) {
	    if (is_full()) return false;
	    messages_.push_back(msg);
	    wake_get_waiters();
	    return true;
      }

      // Try to get a message from the mailbox
      // Returns true and sets msg if message available, false otherwise
      bool try_get(int32_t &msg) {
	    if (messages_.empty()) return false;
	    msg = messages_.front();
	    messages_.erase(messages_.begin());
	    wake_put_waiters();  // Wake threads waiting to put
	    return true;
      }

      // Try to peek at the front message without removing it
      bool try_peek(int32_t &msg) const {
	    if (messages_.empty()) return false;
	    msg = messages_.front();
	    return true;
      }

      // Add a thread waiting for get
      void add_get_waiter(vthread_t thr) {
	    mailbox_waiter_s* waiter = new mailbox_waiter_s;
	    waiter->thread = thr;
	    waiter->message = 0;
	    waiter->next = nullptr;
	    *get_waiters_tail_ = waiter;
	    get_waiters_tail_ = &waiter->next;
      }

      // Add a thread waiting for put
      void add_put_waiter(vthread_t thr, int32_t msg) {
	    mailbox_waiter_s* waiter = new mailbox_waiter_s;
	    waiter->thread = thr;
	    waiter->message = msg;
	    waiter->next = nullptr;
	    *put_waiters_tail_ = waiter;
	    put_waiters_tail_ = &waiter->next;
      }

      // Check if there are threads waiting for get
      bool has_get_waiters() const { return get_waiters_ != nullptr; }

      // Check if there are threads waiting for put
      bool has_put_waiters() const { return put_waiters_ != nullptr; }

      // Required by vvp_object base class
      void shallow_copy(const vvp_object*) override { }
      vvp_object* duplicate(void) const override {
	    vvp_mailbox* dup = new vvp_mailbox(bound_);
	    dup->messages_ = messages_;
	    return dup;
      }

    private:
      void wake_get_waiters() {
	    // Wake threads in FIFO order as long as we have messages
	    while (get_waiters_ && !messages_.empty()) {
		  mailbox_waiter_s* waiter = get_waiters_;
		  get_waiters_ = waiter->next;
		  if (get_waiters_ == nullptr) {
			get_waiters_tail_ = &get_waiters_;
		  }

		  // Get the message for this waiter
		  int32_t msg = messages_.front();
		  messages_.erase(messages_.begin());

		  // Push the message to the thread's vec4 stack before waking.
		  // When the thread resumes, it will continue from the next opcode
		  // (e.g., %pop/obj, %store/vec4) which expects the value on the stack.
		  vthread_t thr = waiter->thread;
		  vvp_vector4_t res(32);
		  for (int i = 0; i < 32; i++) {
			res.set_bit(i, (msg >> i) & 1 ? BIT4_1 : BIT4_0);
		  }
		  thr->push_vec4(res);

		  // Wake the thread
		  thr->waiting_for_event = 0;
		  schedule_vthread(thr, 0, false);

		  delete waiter;
	    }
      }

      void wake_put_waiters() {
	    // Wake threads in FIFO order as long as we have space
	    while (put_waiters_ && !is_full()) {
		  mailbox_waiter_s* waiter = put_waiters_;
		  put_waiters_ = waiter->next;
		  if (put_waiters_ == nullptr) {
			put_waiters_tail_ = &put_waiters_;
		  }

		  // Put the message this waiter was trying to put
		  messages_.push_back(waiter->message);

		  // Wake the thread - it will resume at the next opcode
		  vthread_t thr = waiter->thread;
		  thr->waiting_for_event = 0;
		  schedule_vthread(thr, 0, false);

		  delete waiter;
	    }
      }

      int bound_;  // Max capacity (0 = unbounded)
      std::vector<int32_t> messages_;
      mailbox_waiter_s* get_waiters_;
      mailbox_waiter_s** get_waiters_tail_;
      mailbox_waiter_s* put_waiters_;
      mailbox_waiter_s** put_waiters_tail_;
};

/*
 * %mailbox/new <reg>
 *
 * Create a new mailbox with bound from integer register <reg>.
 * If bound <= 0, mailbox is unbounded. Otherwise it holds at most bound messages.
 * Push the mailbox object to the object stack.
 */
bool of_MAILBOX_NEW(vthread_t thr, vvp_code_t cp)
{
      int bound = thr->words[cp->bit_idx[0]].w_int;

      // Create a real mailbox object with the specified bound
      vvp_mailbox* mbx = new vvp_mailbox(bound);
      vvp_object_t obj(mbx);
      thr->push_object(obj);

      return true;
}

/*
 * %mailbox/put
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Put the message (from vec4 stack) into the mailbox.
 * Blocking put - blocks if bounded mailbox is full until space is available.
 *
 * When blocking, the thread is added to the mailbox's wait list and suspended.
 * When a get() removes a message from a full mailbox, wake_put_waiters() will:
 *   1. Put the waiting message into the mailbox
 *   2. Wake the thread
 * The thread then resumes at the NEXT opcode (not this one).
 */
bool of_MAILBOX_PUT(vthread_t thr, vvp_code_t)
{
      // Pop the message from vec4 stack
      vvp_vector4_t msg_vec = thr->pop_vec4();
      int64_t msg64 = 0;
      vector4_to_value(msg_vec, msg64, true, true);
      int32_t msg = (int32_t)msg64;

      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      if (mbx == nullptr) {
	    // Null mailbox - just continue
	    return true;
      }

      // Check if mailbox has space
      if (mbx->is_full()) {
	    // No space available - block until get() makes room
	    assert(! thr->waiting_for_event);
	    thr->waiting_for_event = 1;
	    mbx->add_put_waiter(thr, msg);
	    return false;  // Suspend thread
      }

      // Put message and wake any waiting get threads
      mbx->put(msg);

      return true;
}

/*
 * %mailbox/get
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Get a message and push it to the vec4 stack.
 * Blocking get - blocks if mailbox is empty until a message is available.
 *
 * When blocking, the thread is added to the mailbox's wait list and suspended.
 * When a put() adds a message, wake_get_waiters() will:
 *   1. Get the message from the mailbox
 *   2. Push the message to the waiting thread's vec4 stack
 *   3. Wake the thread
 * The thread then resumes at the NEXT opcode (not this one).
 */
bool of_MAILBOX_GET(vthread_t thr, vvp_code_t)
{
      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      if (mbx == nullptr) {
	    // Null mailbox - push 0 and continue
	    vvp_vector4_t res(32, BIT4_0);
	    thr->push_vec4(res);
	    return true;
      }

      // Check if mailbox has a message
      if (mbx->is_empty()) {
	    // No message available - block until one arrives
	    assert(! thr->waiting_for_event);
	    thr->waiting_for_event = 1;
	    mbx->add_get_waiter(thr);
	    return false;  // Suspend thread
      }

      // Get message and push to stack
      int32_t msg = 0;
      mbx->try_get(msg);

      vvp_vector4_t res(32);
      for (int i = 0; i < 32; i++) {
	    res.set_bit(i, (msg >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(res);

      return true;
}

/*
 * %mailbox/try_put
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Pop message from vec4 stack and try to put it.
 * If bounded mailbox is full, push 0; otherwise put message and push 1.
 */
bool of_MAILBOX_TRY_PUT(vthread_t thr, vvp_code_t)
{
      // Pop the message from vec4 stack
      vvp_vector4_t msg_vec = thr->pop_vec4();
      int64_t msg64 = 0;
      vector4_to_value(msg_vec, msg64, true, true);
      int32_t msg = (int32_t)msg64;

      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      vvp_vector4_t res(32, BIT4_0);
      if (mbx && mbx->put(msg)) {
	    res.set_bit(0, BIT4_1);  // Return 1 (success)
      }
      // Otherwise return 0 (failed - mailbox full)
      thr->push_vec4(res);

      return true;
}

/*
 * %mailbox/try_get
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Try to get a message. Push message to vec4 stack, then push return value.
 * If message available, return 1; otherwise return 0 and push 0 for message.
 */
bool of_MAILBOX_TRY_GET(vthread_t thr, vvp_code_t)
{
      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      int32_t msg = 0;
      bool success = false;
      if (mbx) {
	    success = mbx->try_get(msg);
      }

      // Push return value FIRST (1 = success, 0 = empty)
      vvp_vector4_t ret(32, BIT4_0);
      if (success) ret.set_bit(0, BIT4_1);
      thr->push_vec4(ret);

      // Push message value to vec4 stack (now on top)
      // Code generator will store this to output arg, leaving return value on stack
      vvp_vector4_t msg_res(32);
      for (int i = 0; i < 32; i++) {
	    msg_res.set_bit(i, (msg >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(msg_res);

      return true;
}

/*
 * %mailbox/peek
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Peek at front message without removing it, push to vec4 stack.
 * Blocking peek - for now, just peeks without blocking (returns 0 if empty).
 */
bool of_MAILBOX_PEEK(vthread_t thr, vvp_code_t)
{
      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      int32_t msg = 0;
      if (mbx) {
	    mbx->try_peek(msg);
      }

      // Push the message to vec4 stack
      vvp_vector4_t res(32);
      for (int i = 0; i < 32; i++) {
	    res.set_bit(i, (msg >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(res);

      return true;
}

/*
 * %mailbox/try_peek
 *
 * Peek mailbox from object stack (code generator emits %pop/obj to clean up).
 * Try to peek at front message. Push return value FIRST, then message on top.
 * If message available, return 1; otherwise return 0 and push 0 for message.
 */
bool of_MAILBOX_TRY_PEEK(vthread_t thr, vvp_code_t)
{
      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      int32_t msg = 0;
      bool success = false;
      if (mbx) {
	    success = mbx->try_peek(msg);
      }

      // Push return value FIRST (1 = success, 0 = empty)
      vvp_vector4_t ret(32, BIT4_0);
      if (success) ret.set_bit(0, BIT4_1);
      thr->push_vec4(ret);

      // Push message value to vec4 stack (now on top)
      // Code generator will store this to output arg, leaving return value on stack
      vvp_vector4_t msg_res(32);
      for (int i = 0; i < 32; i++) {
	    msg_res.set_bit(i, (msg >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(msg_res);

      return true;
}

/*
 * %mailbox/num
 *
 * Peek mailbox from stack. Push number of messages currently in mailbox.
 */
bool of_MAILBOX_NUM(vthread_t thr, vvp_code_t)
{
      // Peek the mailbox (code generator emits separate %pop/obj)
      vvp_object_t &obj = thr->peek_object();
      vvp_mailbox* mbx = obj.peek<vvp_mailbox>();

      int32_t count = 0;
      if (mbx) {
	    count = mbx->num();
      }

      // Push the count to vec4 stack
      vvp_vector4_t res(32);
      for (int i = 0; i < 32; i++) {
	    res.set_bit(i, (count >> i) & 1 ? BIT4_1 : BIT4_0);
      }
      thr->push_vec4(res);

      return true;
}

/*
 * %push_rand_bound <prop_idx>, <op_encoded>, <bound_value>
 *
 * Push an inline constraint bound for the next randomize() call.
 * op_encoded: bits 0-2 = operator (0='>', 1='<', 2='G' (>=), 3='L' (<=), 4='=', 5='!')
 *             bit 3 = soft flag (8 = soft constraint)
 */
bool of_PUSH_RAND_BOUND(vthread_t thr, vvp_code_t cp)
{
      class_type::simple_bound_t bound;
      bound.property_idx = cp->number;
      unsigned encoded_op = cp->bit_idx[0];

      // Decode from encoded_op bits:
      //   bits 0-3: op_code (4-bit operator, 0-15)
      //   bit 4: soft flag
      //   bits 5-14: weight (up to 1023)
      //   bit 15: has_element_idx flag
      //   bits 16-30: element_idx (up to 32767)
      //   bit 31: weight_per_value flag
      bound.weight = (encoded_op >> 5) & 0x3FF;  // 10 bits
      bound.weight_per_value = (encoded_op & (1u << 31)) != 0;
      if (bound.weight == 0) bound.weight = 1;  // Default weight if not specified

      // Decode element index information
      bound.has_element_idx = (encoded_op & (1u << 15)) != 0;
      bound.element_idx = (encoded_op >> 16) & 0x7FFF;  // 15 bits

      int op_code = encoded_op & 0xF;  // 4-bit operator
      // Extract soft flag from bit 4
      bool is_soft = (encoded_op & 0x10) != 0;
      switch (op_code) {
	    case 0: bound.op = '>'; break;
	    case 1: bound.op = '<'; break;
	    case 2: bound.op = 'G'; break;  // >=
	    case 3: bound.op = 'L'; break;  // <=
	    case 4: bound.op = '='; break;
	    case 5: bound.op = '!'; break;
	    case 6: bound.op = 'S'; break;  // Size constraint (exact)
	    case 7: bound.op = 's'; break;  // Size constraint (property-based)
	    case 8: bound.op = 'M'; break;  // Size >= (minimum)
	    case 9: bound.op = 'X'; break;  // Size <= (maximum)
	    case 10: bound.op = 'm'; break; // Size > (strict min)
	    case 11: bound.op = 'x'; break; // Size < (strict max)
	    case 13: bound.op = 'I'; break; // Inside array
	    case 14: bound.op = 'R'; break; // Excluded range
	    default: bound.op = '='; break;
      }
      bound.is_soft = is_soft;

      // For op_code 13 (inside array), store the array property index
      if (op_code == 13) {
	    bound.has_const_bound = false;  // Not a constant, it's an array reference
	    bound.is_inside_array = true;
	    bound.inside_array_prop_idx = cp->bit_idx[1];  // Array property index
	    bound.const_bound = 0;
	    bound.bound_prop_idx = 0;
	    bound.is_excluded_range = false;
	    bound.excluded_range_low = 0;
	    bound.excluded_range_high = 0;
      }
      // For op_code 14 (excluded range), unpack the low and high bounds:
      //   - lower 32 bits = low bound
      //   - upper 32 bits = high bound
      else if (op_code == 14) {
	    uint64_t packed = cp->bit_idx[1];
	    int32_t low = (int32_t)(packed & 0xFFFFFFFF);
	    int32_t high = (int32_t)(packed >> 32);
	    bound.has_const_bound = false;  // Not a simple constant bound
	    bound.is_excluded_range = true;
	    bound.excluded_range_low = low;
	    bound.excluded_range_high = high;
	    bound.const_bound = 0;
	    bound.bound_prop_idx = 0;
	    bound.is_inside_array = false;
	    bound.inside_array_prop_idx = 0;
      }
      // For op_code 7 (property-based size), unpack the source_prop_idx and offset:
      //   - upper 16 bits = source property index
      //   - lower 16 bits = signed offset (negative indicates division by abs(offset))
      else if (op_code == 7) {
	    int64_t packed = cp->bit_idx[1];
	    bound.has_const_bound = false;  // Property-based, not constant
	    bound.bound_prop_idx = (packed >> 16) & 0xFFFF;  // Source property index
	    // Sign-extend the 16-bit offset
	    int16_t value_raw = (int16_t)(packed & 0xFFFF);
	    bound.const_bound = (int64_t)value_raw;  // Offset (or negated divisor if negative)
	    bound.is_inside_array = false;
	    bound.inside_array_prop_idx = 0;
	    bound.is_excluded_range = false;
	    bound.excluded_range_low = 0;
	    bound.excluded_range_high = 0;
      } else {
	    bound.has_const_bound = true;
	    bound.const_bound = (int64_t)(int32_t)cp->bit_idx[1];  // Sign-extend
	    bound.bound_prop_idx = 0;
	    bound.is_inside_array = false;
	    bound.inside_array_prop_idx = 0;
	    bound.is_excluded_range = false;
	    bound.excluded_range_low = 0;
	    bound.excluded_range_high = 0;
      }

      // Initialize is_foreach to false for inline constraints
      bound.is_foreach = false;

      thr->push_inline_constraint(bound);
      return true;
}

/*
 * %push_rand_bound/stack <prop_idx>, <encoded_op>
 *
 * Push an inline constraint bound where the value is on the stack.
 * This is used for runtime-evaluated constraint expressions.
 * Pops the value from the vec4 stack.
 */
bool of_PUSH_RAND_BOUND_STACK(vthread_t thr, vvp_code_t cp)
{
      class_type::simple_bound_t bound;
      bound.property_idx = cp->number;
      unsigned encoded_op = cp->bit_idx[0];

      // Decode from encoded_op bits:
      //   bits 0-3: op_code (4-bit operator, 0-15)
      //   bit 4: soft flag
      //   bits 5-14: weight (up to 1023)
      //   bit 15: has_element_idx flag
      //   bits 16-30: element_idx (up to 32767)
      //   bit 31: weight_per_value flag
      bound.weight = (encoded_op >> 5) & 0x3FF;  // 10 bits
      bound.weight_per_value = (encoded_op & (1u << 31)) != 0;
      if (bound.weight == 0) bound.weight = 1;

      // Decode element index information
      bound.has_element_idx = (encoded_op & (1u << 15)) != 0;
      bound.element_idx = (encoded_op >> 16) & 0x7FFF;  // 15 bits

      int op_code = encoded_op & 0xF;
      bool is_soft = (encoded_op & 0x10) != 0;
      switch (op_code) {
	    case 0: bound.op = '>'; break;
	    case 1: bound.op = '<'; break;
	    case 2: bound.op = 'G'; break;  // >=
	    case 3: bound.op = 'L'; break;  // <=
	    case 4: bound.op = '='; break;
	    case 5: bound.op = '!'; break;
	    case 6: bound.op = 'S'; break;  // Size constraint (exact)
	    case 7: bound.op = 's'; break;  // Size constraint (property-based)
	    case 8: bound.op = 'M'; break;  // Size >= (minimum)
	    case 9: bound.op = 'X'; break;  // Size <= (maximum)
	    case 10: bound.op = 'm'; break; // Size > (strict min)
	    case 11: bound.op = 'x'; break; // Size < (strict max)
	    default: bound.op = '='; break;
      }
      bound.is_soft = is_soft;

      // Pop the value from the stack
      vvp_vector4_t val = thr->pop_vec4();
      int64_t const_val = 0;
      if (val.has_xz()) {
	    // X/Z value - treat as 0
	    const_val = 0;
      } else if (val.size() <= 64) {
	    // Extract value as unsigned - no sign extension
	    // This matches how property values are extracted in check_constraints
	    uint64_t uval = 0;
	    for (unsigned i = 0; i < val.size() && i < 64; i++) {
		  if (val.value(i) == BIT4_1)
			uval |= (1ULL << i);
	    }
	    const_val = (int64_t)uval;
      }

      bound.has_const_bound = true;
      bound.const_bound = const_val;
      bound.bound_prop_idx = 0;

      thr->push_inline_constraint(bound);
      return true;
}

/*
 * %push_rand_array_copy <prop_idx>
 *
 * Push an array copy constraint for the next randomize() call.
 * The source array is on the object stack.
 * This implements foreach element equality: foreach(src[i]) { dest[i] == src[i]; }
 */
bool of_PUSH_RAND_ARRAY_COPY(vthread_t thr, vvp_code_t cp)
{
      unsigned prop_idx = cp->number;

      // Pop the source array from the object stack
      vvp_object_t src_obj;
      thr->pop_object(src_obj);

      // Store the array copy constraint
      // Use op 'C' for copy, and store the source object in the thread
      class_type::simple_bound_t bound;
      bound.property_idx = prop_idx;
      bound.op = 'C';  // Copy operator
      bound.is_soft = false;
      bound.has_const_bound = false;
      bound.const_bound = 0;
      bound.bound_prop_idx = 0;
      bound.weight = 1;
      bound.weight_per_value = true;

      // Store the source array in the array_copy_sources map
      thr->push_array_copy_source(prop_idx, src_obj);
      thr->push_inline_constraint(bound);
      return true;
}

/*
 * %clear_rand_bounds
 *
 * Clear all inline constraint bounds. Called after randomize() if needed.
 */
bool of_CLEAR_RAND_BOUNDS(vthread_t thr, vvp_code_t)
{
      thr->clear_inline_constraints();
      return true;
}

/*
 * %std_randomize <sig>, <wid>, <prop_idx>
 * Randomize a standalone signal (for std::randomize function).
 * Uses inline constraints from the constraint stack filtered by prop_idx.
 * Does NOT push any result - that's handled by the code generator.
 * Does NOT clear bounds - caller should emit %clear_rand_bounds when done.
 */
bool of_STD_RANDOMIZE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned wid = cp->bit_idx[0];
      unsigned prop_idx = cp->bit_idx[1];

      if (net == 0) {
	    return true;
      }

      // Get the inline constraints if any
      const std::vector<class_type::simple_bound_t>& bounds = thr->get_inline_constraints();

      // Collect bounds matching our prop_idx
      int64_t min_val = INT64_MIN;
      int64_t max_val = INT64_MAX;
      // Collect discrete values with weights for == constraints (from dist)
      std::vector<std::pair<int64_t, int64_t>> discrete_values;  // (value, weight)
      // Collect >= and <= bounds for building ranges (from dist with ranges)
      std::vector<class_type::simple_bound_t> ge_bounds;  // >= bounds
      std::vector<class_type::simple_bound_t> le_bounds;  // <= bounds

      for (const auto& b : bounds) {
	    if (b.property_idx != prop_idx) continue;
	    switch (b.op) {
		  case '>':  // value > const - tightens minimum
			if (b.const_bound + 1 > min_val) min_val = b.const_bound + 1;
			break;
		  case 'G':  // value >= const - collect for range building
			ge_bounds.push_back(b);
			break;
		  case '<':  // value < const - tightens maximum
			if (b.const_bound - 1 < max_val) max_val = b.const_bound - 1;
			break;
		  case 'L':  // value <= const - collect for range building
			le_bounds.push_back(b);
			break;
		  case '=':  // value == const - collect for weighted selection
			discrete_values.push_back({b.const_bound, b.weight});
			break;
	    }
      }

      // Build range list from paired >= and <= bounds (for dist with ranges)
      struct weighted_range_t {
	    int64_t low, high, weight;
	    bool weight_per_value;
      };
      std::vector<weighted_range_t> ranges;
      if (!ge_bounds.empty() || !le_bounds.empty()) {
	    // Pair up bounds in order (from dist items)
	    size_t ge_idx = 0, le_idx = 0;
	    while (ge_idx < ge_bounds.size() || le_idx < le_bounds.size()) {
		  int64_t low = min_val, high = max_val;
		  int64_t weight = 1;
		  bool weight_per_value = true;
		  if (ge_idx < ge_bounds.size()) {
			low = ge_bounds[ge_idx].const_bound;
			weight = ge_bounds[ge_idx].weight;
			weight_per_value = ge_bounds[ge_idx].weight_per_value;
			ge_idx++;
		  }
		  if (le_idx < le_bounds.size()) {
			high = le_bounds[le_idx++].const_bound;
		  }
		  if (low <= high) {
			ranges.push_back({low, high, weight, weight_per_value});
		  }
	    }
      }

      int64_t generated_val;
      if (!discrete_values.empty()) {
	    // Priority 1: Weighted random selection from discrete values
	    int64_t total_weight = 0;
	    for (const auto& dv : discrete_values) {
		  total_weight += dv.second;
	    }
	    int64_t pick = rand() % total_weight;
	    int64_t cumulative = 0;
	    size_t selected = 0;
	    for (size_t j = 0; j < discrete_values.size(); j++) {
		  cumulative += discrete_values[j].second;
		  if (pick < cumulative) {
			selected = j;
			break;
		  }
	    }
	    generated_val = discrete_values[selected].first;
      } else if (!ranges.empty()) {
	    // Priority 2: Multiple disjoint ranges (from dist {[a:b], [c:d], ...})
	    // Calculate total weight (considering weight_per_value)
	    int64_t total_weight = 0;
	    for (const auto& r : ranges) {
		  if (r.weight_per_value) {
			// := means weight per value, so multiply by range size
			int64_t range_size = r.high - r.low + 1;
			total_weight += r.weight * range_size;
		  } else {
			// :/ means weight divided across range
			total_weight += r.weight;
		  }
	    }
	    // Weighted random selection of range
	    int64_t pick = rand() % total_weight;
	    int64_t cumulative = 0;
	    size_t range_idx = 0;
	    for (size_t j = 0; j < ranges.size(); j++) {
		  int64_t range_weight;
		  if (ranges[j].weight_per_value) {
			int64_t range_size = ranges[j].high - ranges[j].low + 1;
			range_weight = ranges[j].weight * range_size;
		  } else {
			range_weight = ranges[j].weight;
		  }
		  cumulative += range_weight;
		  if (pick < cumulative) {
			range_idx = j;
			break;
		  }
	    }
	    // Generate random value within selected range
	    int64_t low = ranges[range_idx].low;
	    int64_t high = ranges[range_idx].high;
	    int64_t range_size = high - low + 1;
	    generated_val = low + (rand() % range_size);
      } else if (max_val >= min_val) {
	    // Priority 3: Generate value in simple range [min_val, max_val]
	    int64_t range = max_val - min_val + 1;
	    if (range > 0) {
		  // Generate random value in range
		  generated_val = min_val + (int64_t)((unsigned long long)rand() * rand() % (unsigned long long)range);
	    } else {
		  // Overflow - just generate random
		  generated_val = rand();
	    }
      } else {
	    // No valid range - generate random bits
	    vvp_vector4_t val(wid);
	    for (unsigned b = 0; b < wid; b++) {
		  val.set_bit(b, (rand() & 1) ? BIT4_1 : BIT4_0);
	    }
	    vvp_net_ptr_t ptr(net, 0);
	    vvp_send_vec4(ptr, val, 0);
	    return true;
      }

      // Convert integer to vvp_vector4_t and store
      vvp_vector4_t val(wid);
      for (unsigned b = 0; b < wid && b < 64; b++) {
	    val.set_bit(b, ((generated_val >> b) & 1) ? BIT4_1 : BIT4_0);
      }
      // Sign-extend if needed for wider signals
      vvp_bit4_t sign_bit = ((generated_val >> (wid < 64 ? wid-1 : 63)) & 1) ? BIT4_1 : BIT4_0;
      for (unsigned b = 64; b < wid; b++) {
	    val.set_bit(b, sign_bit);
      }

      // Store the constrained random value to the signal
      vvp_net_ptr_t ptr(net, 0);
      vvp_send_vec4(ptr, val, 0);

      return true;
}

bool of_RELEASE_NET(vthread_t, vvp_code_t cp)
{
      return do_release_vec(cp, true);
}


bool of_RELEASE_REG(vthread_t, vvp_code_t cp)
{
      return do_release_vec(cp, false);
}

/* The type is 1 for registers and 0 for everything else. */
bool of_RELEASE_WR(vthread_t, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      unsigned type  = cp->bit_idx[0];

      assert(net->fil);
      net->fil->force_unlink();

	// Send a command to this signal to unforce itself.
      vvp_net_ptr_t ptr (net, 0);
      net->fil->release(ptr, type==0);
      return true;
}

bool of_REPLICATE(vthread_t thr, vvp_code_t cp)
{
      int rept = cp->number;
      vvp_vector4_t val = thr->pop_vec4();
      vvp_vector4_t res (val.size() * rept, BIT4_X);

      for (int idx = 0 ; idx < rept ; idx += 1) {
	    res.set_vec(idx * val.size(), val);
      }

      thr->push_vec4(res);

      return true;
}

static void poke_val(vthread_t fun_thr, unsigned depth, double val)
{
      fun_thr->parent->poke_real(depth, val);
}

static void poke_val(vthread_t fun_thr, unsigned depth, const string&val)
{
      fun_thr->parent->poke_str(depth, val);
}

static size_t get_max(vthread_t fun_thr, double&)
{
      return fun_thr->args_real.size();
}

static size_t get_max(vthread_t fun_thr, string&)
{
      return fun_thr->args_str.size();
}

static size_t get_max(vthread_t fun_thr, vvp_vector4_t&)
{
      return fun_thr->args_vec4.size();
}

static unsigned get_depth(vthread_t fun_thr, size_t index, double&)
{
      return fun_thr->args_real[index];
}

static unsigned get_depth(vthread_t fun_thr, size_t index, string&)
{
      return fun_thr->args_str[index];
}

static unsigned get_depth(vthread_t fun_thr, size_t index, vvp_vector4_t&)
{
      return fun_thr->args_vec4[index];
}

static vthread_t get_func(vthread_t thr)
{
      vthread_t fun_thr = thr;

      while (fun_thr->parent_scope->get_type_code() != vpiFunction) {
	    assert(fun_thr->parent);
	    fun_thr = fun_thr->parent;
      }

      return fun_thr;
}

template <typename ELEM>
static bool ret(vthread_t thr, vvp_code_t cp)
{
      size_t index = cp->number;
      ELEM val;
      pop_value(thr, val, 0);

      vthread_t fun_thr = get_func(thr);
      assert(index < get_max(fun_thr, val));

      unsigned depth = get_depth(fun_thr, index, val);
	// Use the depth to put the value into the stack of
	// the parent thread.
      poke_val(fun_thr, depth, val);
      return true;
}

/*
 * %ret/real <index>
 */
bool of_RET_REAL(vthread_t thr, vvp_code_t cp)
{
      return ret<double>(thr, cp);
}

/*
 * %ret/str <index>
 */
bool of_RET_STR(vthread_t thr, vvp_code_t cp)
{
      return ret<string>(thr, cp);
}

/*
 * %ret/vec4 <index>, <offset>, <wid>
 */
bool of_RET_VEC4(vthread_t thr, vvp_code_t cp)
{
      size_t index = cp->number;
      unsigned off_index = cp->bit_idx[0];
      unsigned int wid = cp->bit_idx[1];
      vvp_vector4_t&val = thr->peek_vec4();

      vthread_t fun_thr = get_func(thr);
      assert(index < get_max(fun_thr, val));
      assert(val.size() == wid);
      unsigned depth = get_depth(fun_thr, index, val);

      int64_t off = off_index ? thr->words[off_index].w_int : 0;
      unsigned int sig_value_size = fun_thr->parent->peek_vec4(depth).size();

      if (off_index!=0 && thr->flags[4] == BIT4_1) {
	    thr->pop_vec4(1);
	    return true;
      }

      if (!resize_rval_vec(val, off, sig_value_size)) {
	    thr->pop_vec4(1);
	    return true;
      }

      if (off == 0 && val.size() == sig_value_size) {
	    fun_thr->parent->poke_vec4(depth, val);
      } else {
	    vvp_vector4_t tmp_dst = fun_thr->parent->peek_vec4(depth);
	    tmp_dst.set_vec(off, val);
	    fun_thr->parent->poke_vec4(depth, tmp_dst);
      }

      thr->pop_vec4(1);
      return true;
}

static void push_from_parent(vthread_t thr, vthread_t fun_thr, unsigned depth, double&)
{
      thr->push_real(fun_thr->parent->peek_real(depth));
}

static void push_from_parent(vthread_t thr, vthread_t fun_thr, unsigned depth, string&)
{
      thr->push_str(fun_thr->parent->peek_str(depth));
}

static void push_from_parent(vthread_t thr, vthread_t fun_thr, unsigned depth, vvp_vector4_t&)
{
      thr->push_vec4(fun_thr->parent->peek_vec4(depth));
}

template <typename ELEM>
static bool retload(vthread_t thr, vvp_code_t cp)
{
      size_t index = cp->number;
      ELEM type;

      vthread_t fun_thr = get_func(thr);
      assert(index < get_max(fun_thr, type));

      unsigned depth = get_depth(fun_thr, index, type);
	// Use the depth to extract the values from the stack
	// of the parent thread.
      push_from_parent(thr, fun_thr, depth, type);
      return true;
}

/*
 * %retload/real <index>
 */
bool of_RETLOAD_REAL(vthread_t thr, vvp_code_t cp)
{
      return retload<double>(thr, cp);
}

/*
 * %retload/str <index>
 */
bool of_RETLOAD_STR(vthread_t thr, vvp_code_t cp)
{
      return retload<string>(thr, cp);
}

/*
 * %retload/vec4 <index>
 */
bool of_RETLOAD_VEC4(vthread_t thr, vvp_code_t cp)
{
      return retload<vvp_vector4_t>(thr, cp);
}

/*
 * %scopy
 *
 * Pop the top item from the object stack, and shallow_copy() that item into
 * the new top of the object stack. This will copy at many items as needed
 * from the source object to fill the target object. If the target object is
 * larger then the source object, then some items will be left unchanged.
 *
 * The object may be any kind of object that supports shallow_copy(),
 * including dynamic arrays and class objects.
 */
bool of_SCOPY(vthread_t thr, vvp_code_t)
{
      vvp_object_t tmp;
      thr->pop_object(tmp);

      vvp_object_t&dest = thr->peek_object();
        // If it is null there is nothing to copy
      if (!tmp.test_nil())
	    dest.shallow_copy(tmp);

      return true;
}

template <typename ELEM>
static bool set_dar_obj(vthread_t thr, vvp_code_t cp)
{
      unsigned adr = thr->words[cp->number].w_int;

      ELEM value;
      dar_pop_value(thr, value);

      vvp_object_t&top = thr->peek_object();
      vvp_darray*darray = top.peek<vvp_darray>();

      // Handle null or non-darray objects gracefully
      if (darray && (thr->flags[4] == BIT4_0)) {
	    darray->set_word(adr, value);
      }
      return true;
}

/*
 * %set/dar/obj/real <index>
 */
bool of_SET_DAR_OBJ_REAL(vthread_t thr, vvp_code_t cp)
{
      return set_dar_obj<double>(thr, cp);
}

/*
 * %set/dar/obj/str <index>
 */
bool of_SET_DAR_OBJ_STR(vthread_t thr, vvp_code_t cp)
{
      return set_dar_obj<string>(thr, cp);
}

/*
 * %set/dar/obj/vec4 <index>
 */
bool of_SET_DAR_OBJ_VEC4(vthread_t thr, vvp_code_t cp)
{
      return set_dar_obj<vvp_vector4_t>(thr, cp);
}

/*
 * %set/dar/obj/pv <idx_reg>, <off_reg>, <wid>
 *
 * Set a partial value into a darray/queue element with part-select.
 * This is used for assignments like arr[i][base -: width] = value.
 * The idx_reg contains the array index, off_reg contains the bit offset,
 * and wid is the width of the part-select.
 * Pop vec4 value from stack, do read-modify-write on darray element.
 */
bool of_SET_DAR_OBJ_PV(vthread_t thr, vvp_code_t cp)
{
      unsigned idx_reg = cp->number;
      unsigned off_reg = cp->bit_idx[0];
      unsigned wid = cp->bit_idx[1];

      int64_t adr = thr->words[idx_reg].w_int;
      int64_t off = off_reg ? thr->words[off_reg].w_int : 0;

      // Pop the value to store
      vvp_vector4_t val = thr->pop_vec4();
      if (val.size() > wid)
	    val.resize(wid);

      vvp_object_t&top = thr->peek_object();
      vvp_darray*darray = top.peek<vvp_darray>();

      if (darray && (adr >= 0) && (thr->flags[4] == BIT4_0)) {
	    // Get the current element value
	    vvp_vector4_t cur_val;
	    darray->get_word(adr, cur_val);

	    // Resize if needed to accommodate the part select
	    if (cur_val.size() < (size_t)(off + wid)) {
		  cur_val.resize(off + wid, BIT4_0);
	    }

	    // Insert the new value at the offset
	    for (unsigned i = 0; i < wid && i < val.size(); i++) {
		  cur_val.set_bit(off + i, val.value(i));
	    }

	    // Store the modified value back
	    darray->set_word(adr, cur_val);
      }
      return true;
}

/*
 * %get/dar/obj/o <index_reg>
 *
 * Get an object from the darray on top of the object stack at the index
 * specified by the word register. Pop the darray and push the element.
 * This is used for accessing elements of darray class properties.
 */
bool of_GET_DAR_OBJ_O(vthread_t thr, vvp_code_t cp)
{
      unsigned idx_reg = cp->number;
      int64_t adr = thr->words[idx_reg].w_int;

      vvp_object_t dar_obj;
      thr->pop_object(dar_obj);
      vvp_darray*darray = dar_obj.peek<vvp_darray>();

      vvp_object_t elem;
      if (darray && (adr >= 0) && (thr->flags[4] == BIT4_0)) {
	    darray->get_word(adr, elem);
      }
      // else elem remains nil

      thr->push_object(elem);
      return true;
}

/*
 * %get/dar/obj/vec4 <index_reg>
 *
 * Get a vec4 from the darray on top of the object stack at the index
 * specified by the word register. Pop the darray and push the element
 * to the vec4 stack. This is used for reading elements of int[] class
 * properties in expressions like $display(arr[i]).
 */
bool of_GET_DAR_OBJ_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned idx_reg = cp->number;
      int64_t adr = thr->words[idx_reg].w_int;

      vvp_object_t dar_obj;
      thr->pop_object(dar_obj);
      vvp_darray*darray = dar_obj.peek<vvp_darray>();

      vvp_vector4_t elem(32, BIT4_X);  // Default to 32-bit X
      if (darray && (adr >= 0) && (thr->flags[4] == BIT4_0)) {
	    darray->get_word(adr, elem);
      }

      thr->push_vec4(elem);
      return true;
}

/*
 * %set/dar/obj/o <index_reg>
 *
 * Set an object into the darray on the object stack at the index
 * specified by the word register. Pop the value from object stack,
 * then store into darray (which is next on stack).
 * Stack layout: [... darray value] -> [... darray] after store
 */
bool of_SET_DAR_OBJ_O(vthread_t thr, vvp_code_t cp)
{
      unsigned idx_reg = cp->number;
      int64_t adr = thr->words[idx_reg].w_int;

      // Pop the value to store
      vvp_object_t value;
      thr->pop_object(value);

      // Peek the darray (it stays on the stack)
      vvp_object_t&dar_obj = thr->peek_object();
      vvp_darray*darray = dar_obj.peek<vvp_darray>();

      if (darray && (adr >= 0) && (thr->flags[4] == BIT4_0)) {
	    darray->set_word(adr, value);
      }

      return true;
}

/*
 * %shiftl <idx>
 *
 * Pop the operand, then push the result.
 */
bool of_SHIFTL(vthread_t thr, vvp_code_t cp)
{
      int use_index = cp->number;
      uint64_t shift = thr->words[use_index].w_uint;

      vvp_vector4_t&val = thr->peek_vec4();
      unsigned wid  = val.size();

      if (thr->flags[4] == BIT4_1) {
	      // The result is 'bx if the shift amount is undefined
	    val = vvp_vector4_t(wid, BIT4_X);

      } else if (thr->flags[4] == BIT4_X || shift >= wid) {
	      // Shift is so big that all value is shifted out. Write
	      // a constant 0 result.
	    val = vvp_vector4_t(wid, BIT4_0);

      } else if (shift > 0) {
	    vvp_vector4_t blk = val.subvalue(0, wid-shift);
	    vvp_vector4_t tmp (shift, BIT4_0);
	    val.set_vec(0, tmp);
	    val.set_vec(shift, blk);
      }

      return true;
}

/*
 * %shiftr <idx>
 * This is an unsigned right shift. The <idx> is a number that selects
 * the index register with the amount of the shift. This instruction
 * checks flag bit 4, which will be true if the shift is invalid.
 */
bool of_SHIFTR(vthread_t thr, vvp_code_t cp)
{
      int use_index = cp->number;
      uint64_t shift = thr->words[use_index].w_uint;

      vvp_vector4_t val = thr->pop_vec4();
      unsigned wid  = val.size();

      if (thr->flags[4] == BIT4_1) {
	    val = vvp_vector4_t(wid, BIT4_X);

      } else if (thr->flags[4] == BIT4_X || shift > wid) {
	    val = vvp_vector4_t(wid, BIT4_0);

      } else if (shift > 0) {
	    vvp_vector4_t blk = val.subvalue(shift, wid-shift);
	    vvp_vector4_t tmp (shift, BIT4_0);
	    val.set_vec(0, blk);
	    val.set_vec(wid-shift, tmp);
      }

      thr->push_vec4(val);
      return true;
}

/*
 *  %shiftr/s <wid>
 */
bool of_SHIFTR_S(vthread_t thr, vvp_code_t cp)
{
      int use_index = cp->number;
      uint64_t shift = thr->words[use_index].w_uint;

      vvp_vector4_t val = thr->pop_vec4();
      unsigned wid  = val.size();

      vvp_bit4_t sign_bit = val.value(val.size()-1);

      if (thr->flags[4] == BIT4_1) {
	    val = vvp_vector4_t(wid, BIT4_X);

      } else if (thr->flags[4] == BIT4_X || shift > wid) {
	    val = vvp_vector4_t(wid, sign_bit);

      } else if (shift > 0) {
	    vvp_vector4_t blk = val.subvalue(shift, wid-shift);
	    vvp_vector4_t tmp (shift, sign_bit);
	    val.set_vec(0, blk);
	    val.set_vec(wid-shift, tmp);
      }

      thr->push_vec4(val);
      return true;
}

/*
 * %split/vec4 <wid>
 *   Pop 1 value,
 *   Take <wid> bits from the lsb,
 *   Push the remaining msb,
 *   Push the lsb.
 */
bool of_SPLIT_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned lsb_wid = cp->number;

      vvp_vector4_t&val = thr->peek_vec4();
      assert(lsb_wid < val.size());

      vvp_vector4_t lsb = val.subvalue(0, lsb_wid);
      val = val.subvalue(lsb_wid, val.size()-lsb_wid);

      thr->push_vec4(lsb);
      return true;
}

/*
 * The following are used to allow the darray templates to print correctly.
 */
inline static string get_darray_type(double&)
{
      return "darray<real>";
}

inline static string get_darray_type(string&)
{
      return "darray<string>";
}

inline static string get_darray_type(const vvp_vector4_t&value)
{
      ostringstream buf;
      buf << "darray<vector[" << value.size() << "]>";
      string res = buf.str();
      return res;
}

inline static string get_darray_type(const vvp_object_t&)
{
      return "darray<object>";
}

/*
 * The following are used to allow a common template to be written for
 * darray real/string/vec4 operations
 */
inline static void dar_pop_value(vthread_t thr, double&value)
{
      value = thr->pop_real();
}

inline static void dar_pop_value(vthread_t thr, string&value)
{
      value = thr->pop_str();
}

inline static void dar_pop_value(vthread_t thr, vvp_vector4_t&value)
{
      value = thr->pop_vec4();
}

inline static void dar_pop_value(vthread_t thr, vvp_object_t&value)
{
      thr->pop_object(value);
}

template <typename ELEM>
static bool store_dar(vthread_t thr, vvp_code_t cp)
{
      int64_t adr = thr->words[3].w_int;
      ELEM value;
	// FIXME: Can we get the size of the underlying array element
	//        and then use the normal pop_value?
      dar_pop_value(thr, value);

      vvp_net_t*net = cp->net;
      assert(net);

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_darray*darray = obj->get_object().peek<vvp_darray>();

      if (adr < 0)
	    cerr << thr->get_fileline()
	         << "Warning: cannot write to a negative " << get_darray_type(value)
	         << " index (" << adr << ")." << endl;
      else if (thr->flags[4] != BIT4_0)
	    cerr << thr->get_fileline()
	         << "Warning: cannot write to an undefined " << get_darray_type(value)
	         << " index." << endl;
      else if (darray)
	    darray->set_word(adr, value);
      else
	    cerr << thr->get_fileline()
	         << "Warning: cannot write to an undefined " << get_darray_type(value)
	         << "." << endl;

      return true;
}

/*
 * %store/dar/real <var>
 */
bool of_STORE_DAR_R(vthread_t thr, vvp_code_t cp)
{
      return store_dar<double>(thr, cp);
}

/*
 * %store/dar/str <var>
 */
bool of_STORE_DAR_STR(vthread_t thr, vvp_code_t cp)
{
      return store_dar<string>(thr, cp);
}

/*
 * %store/dar/vec4 <var>
 */
bool of_STORE_DAR_VEC4(vthread_t thr, vvp_code_t cp)
{
      return store_dar<vvp_vector4_t>(thr, cp);
}

/*
 * %store/dar/o <var>
 * Store object to dynamic array of objects at index in register 3.
 */
bool of_STORE_DAR_O(vthread_t thr, vvp_code_t cp)
{
      return store_dar<vvp_object_t>(thr, cp);
}

/*
 * %load/assoc/vec4 <array-label>
 * Load a vec4 value from an associative array.
 * The string key is popped from the string stack.
 */
bool of_LOAD_ASSOC_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      vvp_vector4_t value;
      if (assoc)
	    assoc->get_word(key, value);
      else
	    value = vvp_vector4_t(32, BIT4_0); // Default 32-bit zero

      thr->push_vec4(value);
      return true;
}

/*
 * %store/assoc/vec4 <array-label>
 * Store a vec4 value to an associative array.
 * The string key is popped from the string stack.
 * The vec4 value is popped from the vec4 stack.
 */
bool of_STORE_ASSOC_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();
      vvp_vector4_t value = thr->pop_vec4();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();
      if (assoc == 0) {
	      // Create a new associative array if it doesn't exist
	    assoc = new vvp_assoc_vec4(value.size());
	    vvp_object_t tmp(assoc);
	    vvp_net_ptr_t ptr(net, 0);
	    vvp_send_object(ptr, tmp, thr->wt_context);
	      // Re-get the assoc after sending to ensure we have the stored version
	    assoc = obj->get_object().peek<vvp_assoc>();
      }

      if (assoc) {
	    assoc->set_word(key, value);
      }

      return true;
}

/*
 * %store/assoc/r <array-label>
 */
bool of_STORE_ASSOC_R(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();
      double value = thr->pop_real();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();
      if (assoc == 0) {
	    assoc = new vvp_assoc_real();
	    vvp_object_t tmp(assoc);
	    vvp_net_ptr_t ptr(net, 0);
	    vvp_send_object(ptr, tmp, thr->wt_context);
	    assoc = obj->get_object().peek<vvp_assoc>();
      }

      if (assoc)
	    assoc->set_word(key, value);

      return true;
}

/*
 * %store/assoc/str <array-label>
 */
bool of_STORE_ASSOC_STR(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();
      string value = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();
      if (assoc == 0) {
	    assoc = new vvp_assoc_string();
	    vvp_object_t tmp(assoc);
	    vvp_net_ptr_t ptr(net, 0);
	    vvp_send_object(ptr, tmp, thr->wt_context);
	    assoc = obj->get_object().peek<vvp_assoc>();
      }

      if (assoc)
	    assoc->set_word(key, value);

      return true;
}

/*
 * %assoc/exists <array-label>
 * Check if key exists in associative array. Key is on string stack.
 * Pushes 1 if key exists, 0 otherwise onto vec4 stack.
 */
bool of_ASSOC_EXISTS(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      bool exists = false;
      if (assoc) {
	    exists = assoc->exists(key);
      }

	// Return integer 1 (0x00000001) or 0 (0x00000000), not 0xFFFFFFFF
      vvp_vector4_t result(32, BIT4_0);
      if (exists) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %assoc/delete <array-label>
 * Delete key from associative array. Key is on string stack.
 * Pushes 1 if key was present and deleted, 0 otherwise.
 */
bool of_ASSOC_DELETE(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

        // delete() is a void method - no return value
      if (assoc)
	    assoc->delete_word(key);

      return true;
}

/*
 * %assoc/first <array-label>
 * Get first key in associative array.
 * Pops current key from string stack, pushes first key back.
 * Pushes 1 if key found, 0 if array empty onto vec4 stack.
 */
bool of_ASSOC_FIRST(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();  // Pop current key (may be unused)

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      bool found = false;
      if (assoc)
	    found = assoc->first(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %assoc/last <array-label>
 * Get last key in associative array.
 * Pops current key from string stack, pushes last key back.
 * Pushes 1 if key found, 0 if array empty onto vec4 stack.
 */
bool of_ASSOC_LAST(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      bool found = false;
      if (assoc)
	    found = assoc->last(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %assoc/next <array-label>
 * Get next key after current key in associative array.
 * Pops current key from string stack, pushes next key back.
 * Pushes 1 if next key found, 0 if no more keys onto vec4 stack.
 */
bool of_ASSOC_NEXT(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      bool found = false;
      if (assoc)
	    found = assoc->next(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %assoc/prev <array-label>
 * Get previous key before current key in associative array.
 * Pops current key from string stack, pushes prev key back.
 * Pushes 1 if prev key found, 0 if no more keys onto vec4 stack.
 */
bool of_ASSOC_PREV(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      string key = thr->pop_str();

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      bool found = false;
      if (assoc)
	    found = assoc->prev(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %assoc/num <array-label>
 * Get number of elements in associative array.
 * Pushes size onto vec4 stack.
 */
bool of_ASSOC_NUM(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;
      assert(net);

      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      vvp_assoc*assoc = obj->get_object().peek<vvp_assoc>();

      size_t size = 0;
      if (assoc)
	    size = assoc->get_size();

      vvp_vector4_t result(32, BIT4_0);
      for (unsigned i = 0; i < 32 && i < sizeof(size)*8; i++) {
	    if (size & (1UL << i))
		  result.set_bit(i, BIT4_1);
      }
      thr->push_vec4(result);
      return true;
}

bool of_STORE_OBJ(vthread_t thr, vvp_code_t cp)
{
	/* set the value into port 0 of the destination. */
      vvp_net_ptr_t ptr (cp->net, 0);

      vvp_object_t val;
      thr->pop_object(val);

      vvp_send_object(ptr, val, thr->wt_context);

      return true;
}

/*
 * %store/obja <array-label> <index>
 */
bool of_STORE_OBJA(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      unsigned adr = thr->words[idx].w_int;

      vvp_object_t val;
      thr->pop_object(val);

      cp->array->set_word(adr, val);

      return true;
}


/*
 * %store/prop/obj <pid>, <idx>
 *
 * Pop an object value from the object stack, and store the value into
 * the property of the object references by the top of the stack. Do NOT
 * pop the object stack.
 */
bool of_STORE_PROP_OBJ(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      unsigned idx = cp->bit_idx[0];

      if (idx != 0) {
	    assert(idx < vthread_s::WORDS_COUNT);
	    idx = thr->words[idx].w_uint;
      }

      vvp_object_t val;
      thr->pop_object(val);

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_STORE_PROP_OBJ: thr=%p cobj null at pid=%lu scope=%s obj.nil=%d val.nil=%d wt=%p rd=%p\n",
	            (void*)thr, (unsigned long)pid, scope ? scope->scope_name() : "(null)",
	            obj.test_nil(), val.test_nil(), thr->wt_context, thr->rd_context);
	    // Can't store to null object - this is likely a UVM library issue
	    // For now, skip the store rather than crashing
	    return true;
      }

      cobj->set_object(pid, val, idx);

      return true;
}

static void pop_prop_val(vthread_t thr, double&val, unsigned)
{
      val = thr->pop_real();
}

static void pop_prop_val(vthread_t thr, string&val, unsigned)
{
      val = thr->pop_str();
}

static void pop_prop_val(vthread_t thr, vvp_vector4_t&val, unsigned wid)
{
      val = thr->pop_vec4();
      assert(val.size() >= wid);
      val.resize(wid);
}

static void set_val(vvp_cobject*cobj, size_t pid, const double&val)
{
      cobj->set_real(pid, val);
}

static void set_val(vvp_cobject*cobj, size_t pid, const string&val)
{
      cobj->set_string(pid, val);
}

static void set_val(vvp_cobject*cobj, size_t pid, const vvp_vector4_t&val)
{
      cobj->set_vec4(pid, val);
}

template <typename ELEM>
static bool store_prop(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      size_t pid = cp->number;
      ELEM val;
      pop_prop_val(thr, val, wid); // Pop the value to store.

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR store_prop<>: cobj null at pid=%lu scope=%s obj.nil=%d\n",
	            (unsigned long)pid, scope ? scope->scope_name() : "(null)", obj.test_nil());
	    // Can't store to null object - skip
	    return true;
      }

      set_val(cobj, pid, val);

      return true;
}

/*
 * %store/prop/r <id>
 *
 * Pop a real value from the real stack, and store the value into the
 * property of the object references by the top of the stack. Do NOT
 * pop the object stack.
 */
bool of_STORE_PROP_R(vthread_t thr, vvp_code_t cp)
{
      return store_prop<double>(thr, cp);
}

/*
 * %store/prop/str <id>
 *
 * Pop a string value from the string stack, and store the value into
 * the property of the object references by the top of the stack. Do NOT
 * pop the object stack.
 */
bool of_STORE_PROP_STR(vthread_t thr, vvp_code_t cp)
{
      return store_prop<string>(thr, cp);
}

/*
 * %store/prop/v <pid>, <wid>
 *
 * Store vector value into property <id> of cobject in the top of the
 * stack. Do NOT pop the object stack.
 */
bool of_STORE_PROP_V(vthread_t thr, vvp_code_t cp)
{
      return store_prop<vvp_vector4_t>(thr, cp, cp->bit_idx[0]);
}

/*
 * %store/prop/va <pid>, <wid>
 *
 * Store vector value into property array element. The array index is
 * popped from the vec4 stack first, then the value to store.
 * The cobject remains on top of the object stack.
 */
bool of_STORE_PROP_VA(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      unsigned wid = cp->bit_idx[0];

      // Stack order: value pushed first, then index pushed second
      // Pop in reverse order (LIFO): index first, then value

      // Pop the array index (pushed last)
      vvp_vector4_t idx_vec = thr->pop_vec4();
      int64_t idx_val;
      bool ok = vector4_to_value(idx_vec, idx_val, true, false);
      assert(ok);
      uint64_t idx = idx_val;

      // Pop the value to store (pushed first)
      vvp_vector4_t val = thr->pop_vec4();
      assert(val.size() >= wid);
      val.resize(wid);

      // Get the object and store the value at the indexed position
      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_STORE_PROP_VA: cobj null at pid=%lu idx=%lu scope=%s\n",
	            (unsigned long)pid, (unsigned long)idx, scope ? scope->scope_name() : "(null)");
	    return true;
      }

      cobj->set_vec4(pid, val, idx);

      return true;
}

/*
 * %store/prop/v/s <pid>, <off_idx>, <wid>
 *
 * Store vector value with part-select into property <pid> of cobject on the
 * top of the object stack. This is used for packed struct member writes.
 * The offset is taken from the word register specified by <off_idx>.
 * Do NOT pop the object stack.
 */
bool of_STORE_PROP_VS(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      unsigned off_idx = cp->bit_idx[0];
      unsigned wid = cp->bit_idx[1];

      // Get the offset from the word register
      int64_t off = off_idx ? thr->words[off_idx].w_int : 0;

      // Pop the value to store
      vvp_vector4_t val = thr->pop_vec4();
      assert(val.size() >= wid);
      val.resize(wid);

      // Get the object and its current property value
      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_STORE_PROP_VS: cobj null at pid=%lu scope=%s\n",
	            (unsigned long)pid, scope ? scope->scope_name() : "(null)");
	    return true;
      }

      // Get the current property value
      vvp_vector4_t prop_val;
      cobj->get_vec4(pid, prop_val, 0);

      // Resize if needed to accommodate the part select
      if (prop_val.size() < (size_t)(off + wid)) {
	    prop_val.resize(off + wid, BIT4_X);
      }

      // Insert the new value at the offset
      for (unsigned i = 0; i < wid; i++) {
	    prop_val.set_bit(off + i, val.value(i));
      }

      // Store the modified value back
      cobj->set_vec4(pid, prop_val, 0);

      return true;
}

/*
 * %store/prop/assoc/vec4 <pid>, <wid>
 *
 * Store a vec4 value to an associative array property.
 * The string key is popped from the string stack.
 * The vec4 value is popped from the vec4 stack.
 * The cobject remains on top of the object stack.
 */
bool of_STORE_PROP_ASSOC_VEC4(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      unsigned wid = cp->bit_idx[0];

      // Pop the string key (pushed last)
      string key = thr->pop_str();

      // Pop the value to store (pushed first)
      vvp_vector4_t val = thr->pop_vec4();
      assert(val.size() >= wid);
      val.resize(wid);

      // Get the class object from the object stack
      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_STORE_PROP_ASSOC_VEC4: cobj null at pid=%lu scope=%s\n",
	            (unsigned long)pid, scope ? scope->scope_name() : "(null)");
	    return true;
      }

      // Get the associative array property object
      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      // Try to get the associative array
      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      if (assoc == 0) {
	    // Create a new associative array if it doesn't exist
	    assoc = new vvp_assoc_vec4(wid);
	    vvp_object_t new_obj(assoc);
	    cobj->set_object(pid, new_obj, 0);
	    // Re-fetch to get the correct pointer
	    cobj->get_object(pid, prop_obj, 0);
	    assoc = prop_obj.peek<vvp_assoc>();
      }

      if (assoc)
	    assoc->set_word(key, val);

      return true;
}

/*
 * %prop/assoc/vec4 <pid>
 *
 * Load a vec4 value from an associative array property.
 * The string key is popped from the string stack.
 * The vec4 value is pushed to the vec4 stack.
 * The cobject remains on top of the object stack.
 */
bool of_PROP_ASSOC_VEC4(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;

      // Pop the string key
      string key = thr->pop_str();

      // Get the class object from the object stack
      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_PROP_ASSOC_VEC4: cobj null at pid=%lu scope=%s\n",
	            (unsigned long)pid, scope ? scope->scope_name() : "(null)");
	    // Push a default value
	    vvp_vector4_t val(32, BIT4_X);
	    thr->push_vec4(val);
	    return true;
      }

      // Get the associative array property object
      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      // Get the associative array
      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      if (assoc == 0) {
	    // Array doesn't exist, return default value
	    vvp_vector4_t val(32, BIT4_X);
	    thr->push_vec4(val);
	    return true;
      }

      // Get the value from the associative array
      vvp_vector4_t val;
      assoc->get_word(key, val);
      thr->push_vec4(val);

      return true;
}

/*
 * %prop/assoc/exists <pid>
 * Check if key exists in associative array property. Key is on string stack.
 * Pushes 1 if key exists, 0 otherwise onto vec4 stack.
 */
bool of_PROP_ASSOC_EXISTS(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool exists = false;
      if (assoc)
	    exists = assoc->exists(key);

	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (exists) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/delete <pid>
 * Delete key from associative array property. Key is on string stack.
 * Pushes 1 if key was deleted, 0 otherwise.
 */
bool of_PROP_ASSOC_DELETE(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool deleted = false;
      if (assoc)
	    deleted = assoc->delete_word(key);

	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (deleted) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/first <pid>
 * Get first key in associative array property.
 * Pops current key from string stack, pushes first key back.
 * Pushes 1 if found, 0 if array empty onto vec4 stack.
 */
bool of_PROP_ASSOC_FIRST(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_str("");
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool found = false;
      if (assoc)
	    found = assoc->first(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/last <pid>
 * Get last key in associative array property.
 */
bool of_PROP_ASSOC_LAST(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_str("");
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool found = false;
      if (assoc)
	    found = assoc->last(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/next <pid>
 * Get next key after current key in associative array property.
 */
bool of_PROP_ASSOC_NEXT(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_str("");
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool found = false;
      if (assoc)
	    found = assoc->next(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/prev <pid>
 * Get previous key before current key in associative array property.
 */
bool of_PROP_ASSOC_PREV(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;
      string key = thr->pop_str();

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_str("");
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      bool found = false;
      if (assoc)
	    found = assoc->prev(key);

      thr->push_str(key);
	// Return integer 1 or 0
      vvp_vector4_t result(32, BIT4_0);
      if (found) result.set_bit(0, BIT4_1);
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/assoc/num <pid>
 * Get number of elements in associative array property.
 * Pushes size onto vec4 stack.
 */
bool of_PROP_ASSOC_NUM(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    thr->push_vec4(vvp_vector4_t(32, BIT4_0));
	    return true;
      }

      vvp_object_t prop_obj;
      cobj->get_object(pid, prop_obj, 0);

      vvp_assoc*assoc = prop_obj.peek<vvp_assoc>();
      size_t size = 0;
      if (assoc)
	    size = assoc->get_size();

      vvp_vector4_t result(32, BIT4_0);
      for (unsigned i = 0; i < 32 && i < sizeof(size)*8; i++) {
	    if (size & (1UL << i))
		  result.set_bit(i, BIT4_1);
      }
      thr->push_vec4(result);
      return true;
}

/*
 * %prop/va <pid>
 *
 * Load vector value from property array element. The array index is
 * popped from the vec4 stack. The loaded value is pushed to vec4 stack.
 * The cobject remains on the object stack.
 */
bool of_PROP_VA(vthread_t thr, vvp_code_t cp)
{
      size_t pid = cp->number;

      // Pop the array index
      vvp_vector4_t idx_vec = thr->pop_vec4();
      int64_t idx_val;
      bool ok = vector4_to_value(idx_vec, idx_val, true, false);
      assert(ok);
      uint64_t idx = idx_val;

      // Get the object (keep on stack)
      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj = obj.peek<vvp_cobject>();
      if (!cobj) {
	    __vpiScope*scope = vthread_scope(thr);
	    fprintf(stderr, "ERROR of_PROP_VA: cobj null at pid=%lu idx=%lu scope=%s\n",
	            (unsigned long)pid, (unsigned long)idx, scope ? scope->scope_name() : "(null)");
	    // Push a default value
	    vvp_vector4_t val(32, BIT4_X);
	    thr->push_vec4(val);
	    return true;
      }

      // Load the value from the indexed position
      vvp_vector4_t val;
      cobj->get_vec4(pid, val, idx);

      // Push the value
      thr->push_vec4(val);

      return true;
}

/*
 * Helper function to find a signal by name in a scope.
 * Returns the vvp_net_t* for the signal, or nullptr if not found.
 */
static vvp_net_t* find_signal_in_scope(__vpiScope* scope, const char* name)
{
      if (!scope) return nullptr;

      // Iterate through the scope's internal items looking for signals
      for (size_t i = 0; i < scope->intern.size(); ++i) {
            __vpiHandle* handle = scope->intern[i];
            if (!handle) continue;

            // Check if this is a signal type using get_type_code()
            int type = handle->get_type_code();
            if (type == vpiNet || type == vpiReg || type == vpiIntegerVar ||
                type == vpiByteVar || type == vpiBitVar || type == vpiShortIntVar ||
                type == vpiIntVar || type == vpiLongIntVar) {
                  __vpiSignal* sig = static_cast<__vpiSignal*>(handle);
                  // Check if the name matches
                  if (sig->id.name && strcmp(sig->id.name, name) == 0) {
                        return sig->node;
                  }
            } else if (type == vpiClassVar) {
                  // Handle class-typed variables (e.g., class objects in interfaces)
                  __vpiCobjectVar* cvar = dynamic_cast<__vpiCobjectVar*>(handle);
                  if (cvar && cvar->get_name() && strcmp(cvar->get_name(), name) == 0) {
                        return cvar->get_net();
                  }
            }
      }
      return nullptr;
}

/*
 * %vif/load/v "member_name", <wid>
 *
 * Load a vector value from a virtual interface member signal.
 * The virtual interface (scope pointer) is on the top of the object stack.
 */
bool of_VIF_LOAD_V(vthread_t thr, vvp_code_t cp)
{
      const char*member_name = cp->text;
      unsigned wid = cp->bit_idx[0];

      // Peek at the VIF scope reference from the object stack
      vvp_object_t& vif_obj = thr->peek_object();
      vvp_scope_ref* scope_ref = vif_obj.peek<vvp_scope_ref>();

      if (!scope_ref) {
            // Push undefined value if VIF is null
            vvp_vector4_t val(wid, BIT4_X);
            thr->push_vec4(val);
            fprintf(stderr, "RUNTIME ERROR: Virtual interface is null when reading '%s'\n", member_name);
            return true;
      }

      __vpiScope* vif_scope = scope_ref->get_scope();
      if (!vif_scope) {
            vvp_vector4_t val(wid, BIT4_X);
            thr->push_vec4(val);
            fprintf(stderr, "RUNTIME ERROR: Virtual interface scope is null when reading '%s'\n", member_name);
            return true;
      }

      // Find the signal by name in the VIF scope
      vvp_net_t* net = find_signal_in_scope(vif_scope, member_name);
      if (!net) {
            vvp_vector4_t val(wid, BIT4_X);
            thr->push_vec4(val);
            fprintf(stderr, "RUNTIME ERROR: Signal '%s' not found in virtual interface scope\n", member_name);
            return true;
      }

      // Read the value from the signal
      vvp_signal_value* sig = dynamic_cast<vvp_signal_value*>(net->fil);
      if (!sig) {
            vvp_vector4_t val(wid, BIT4_X);
            thr->push_vec4(val);
            fprintf(stderr, "RUNTIME ERROR: Signal '%s' has no value filter\n", member_name);
            return true;
      }

      // Get the vec4 value and push onto stack
      vvp_vector4_t val;
      sig->vec4_value(val);

      // Resize if necessary to match requested width
      if (val.size() != wid) {
            val.resize(wid);
      }

      thr->push_vec4(val);
      return true;
}

/*
 * %vif/load/obj "member_name"
 *
 * Load a class object from a virtual interface member.
 * The virtual interface (scope pointer) is on the top of the object stack.
 * The loaded object is pushed onto the object stack.
 */
bool of_VIF_LOAD_OBJ(vthread_t thr, vvp_code_t cp)
{
      const char*member_name = cp->text;

      // Peek at the VIF scope reference from the object stack
      vvp_object_t& vif_obj = thr->peek_object();
      vvp_scope_ref* scope_ref = vif_obj.peek<vvp_scope_ref>();

      if (!scope_ref) {
            // Push null if VIF is null
            vvp_object_t null_obj;
            thr->push_object(null_obj);
            return true;
      }

      __vpiScope* vif_scope = scope_ref->get_scope();
      if (!vif_scope) {
            vvp_object_t null_obj;
            thr->push_object(null_obj);
            return true;
      }

      // Find the signal by name in the VIF scope
      vvp_net_t* net = find_signal_in_scope(vif_scope, member_name);
      if (!net) {
            vvp_object_t null_obj;
            thr->push_object(null_obj);
            fprintf(stderr, "RUNTIME ERROR: Signal '%s' not found in virtual interface scope\n", member_name);
            return true;
      }

      // Read the object value from the signal's fun
      vvp_fun_signal_object* sig = dynamic_cast<vvp_fun_signal_object*>(net->fun);
      if (!sig) {
            vvp_object_t null_obj;
            thr->push_object(null_obj);
            return true;
      }

      // Get the object value and push onto stack
      vvp_object_t val = sig->get_object();
      thr->push_object(val);
      return true;
}

/*
 * %vif/store/obj "member_name"
 *
 * Store an object value to a class-typed variable inside a virtual interface.
 * The virtual interface (scope pointer) is on the object stack.
 * The object to store is also on the object stack (above the VIF).
 */
bool of_VIF_STORE_OBJ(vthread_t thr, vvp_code_t cp)
{
      const char*member_name = cp->text;

      // Pop the object value to store from the object stack
      vvp_object_t val;
      thr->pop_object(val);

      // Peek at the VIF scope reference from the object stack
      vvp_object_t& vif_obj = thr->peek_object();
      vvp_scope_ref* scope_ref = vif_obj.peek<vvp_scope_ref>();

      if (!scope_ref) {
            fprintf(stderr, "RUNTIME ERROR: Virtual interface is null\n");
            return true;
      }

      __vpiScope* vif_scope = scope_ref->get_scope();
      if (!vif_scope) {
            fprintf(stderr, "RUNTIME ERROR: Virtual interface scope is null\n");
            return true;
      }

      // Find the signal by name in the VIF scope
      vvp_net_t* net = find_signal_in_scope(vif_scope, member_name);
      if (!net) {
            fprintf(stderr, "RUNTIME ERROR: Signal '%s' not found in virtual interface scope\n", member_name);
            return true;
      }

      // Store the object to the signal
      vvp_net_ptr_t ptr(net, 0);
      vvp_send_object(ptr, val, thr->wt_context);

      return true;
}

/*
 * %vif/store/v "member_name", <wid>
 *
 * Store a vector value to a virtual interface member signal.
 * The virtual interface (scope pointer) is on the top of the object stack.
 */
bool of_VIF_STORE_V(vthread_t thr, vvp_code_t cp)
{
      const char*member_name = cp->text;
      unsigned wid = cp->bit_idx[0];

      // Pop the value from the vec4 stack
      vvp_vector4_t val = thr->pop_vec4();

      // Peek at the VIF scope reference from the object stack
      vvp_object_t& vif_obj = thr->peek_object();
      vvp_scope_ref* scope_ref = vif_obj.peek<vvp_scope_ref>();

      if (!scope_ref) {
            fprintf(stderr, "RUNTIME ERROR: Virtual interface is null\n");
            return true;
      }

      __vpiScope* vif_scope = scope_ref->get_scope();
      if (!vif_scope) {
            fprintf(stderr, "RUNTIME ERROR: Virtual interface scope is null\n");
            return true;
      }

      // Find the signal by name in the VIF scope
      vvp_net_t* net = find_signal_in_scope(vif_scope, member_name);
      if (!net) {
            fprintf(stderr, "RUNTIME ERROR: Signal '%s' not found in virtual interface scope\n", member_name);
            return true;
      }

      // Resize value if necessary to match the signal width
      if (val.size() != wid) {
            val.resize(wid);
      }

      // Store the value to the signal
      vvp_send_vec4(vvp_net_ptr_t(net, 0), val, thr->wt_context);

      return true;
}

template <typename ELEM, class QTYPE>
static bool store_qb(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      ELEM value;
      vvp_net_t*net = cp->net;
      unsigned max_size = thr->words[cp->bit_idx[0]].w_int;
      pop_value(thr, value, wid); // Pop the value to store.

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);
      queue->push_back(value, max_size);
      return true;
}

/*
 * %store/qb/r <var-label>, <max-idx>
 */
bool of_STORE_QB_R(vthread_t thr, vvp_code_t cp)
{
      return store_qb<double, vvp_queue_real>(thr, cp);
}

/*
 * %store/qb/str <var-label>, <max-idx>
 */
bool of_STORE_QB_STR(vthread_t thr, vvp_code_t cp)
{
      return store_qb<string, vvp_queue_string>(thr, cp);
}

/*
 * %store/qb/v <var-label>, <max-idx>, <wid>
 */
bool of_STORE_QB_V(vthread_t thr, vvp_code_t cp)
{
      return store_qb<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[1]);
}

/*
 * %store/qb/o <var-label>, <max-idx>
 */
bool of_STORE_QB_O(vthread_t thr, vvp_code_t cp)
{
      return store_qb<vvp_object_t, vvp_queue_object>(thr, cp);
}

template <typename ELEM, class QTYPE>
static bool store_qdar(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      int64_t idx = thr->words[3].w_int;
      ELEM value;
      vvp_net_t*net = cp->net;
      pop_value(thr, value, wid); // Pop the value to store.

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);
      if (idx < 0) {
	    cerr << thr->get_fileline()
	         << "Warning: cannot assign to a negative "
	         << get_queue_type(value)
	         << " index (" << idx << "). ";
	    print_queue_value(value);
	    cerr << " was not added." << endl;
      } else if (thr->flags[4] != BIT4_0) {
	    cerr << thr->get_fileline()
	         << "Warning: cannot assign to an undefined "
	         << get_queue_type(value) << " index. ";
	    print_queue_value(value);
	    cerr << " was not added." << endl;
      } else {
	    unsigned max_size = thr->words[cp->bit_idx[0]].w_int;
	    queue->set_word_max(idx, value, max_size);
      }
      return true;
}

/*
 * %store/qdar/r <var>, idx
 */
bool of_STORE_QDAR_R(vthread_t thr, vvp_code_t cp)
{
      return store_qdar<double, vvp_queue_real>(thr, cp);
}

/*
 * %store/qdar/str <var>, idx
 */
bool of_STORE_QDAR_STR(vthread_t thr, vvp_code_t cp)
{
      return store_qdar<string, vvp_queue_string>(thr, cp);
}

/*
 * %store/qdar/v <var>, idx
 */
bool of_STORE_QDAR_V(vthread_t thr, vvp_code_t cp)
{
      return store_qdar<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[1]);
}

template <typename ELEM, class QTYPE>
static bool store_qf(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
      ELEM value;
      vvp_net_t*net = cp->net;
      unsigned max_size = thr->words[cp->bit_idx[0]].w_int;
      pop_value(thr, value, wid); // Pop the value to store.

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);
      queue->push_front(value, max_size);
      return true;
}
/*
 * %store/qf/r <var-label>, <max-idx>
 */
bool of_STORE_QF_R(vthread_t thr, vvp_code_t cp)
{
      return store_qf<double, vvp_queue_real>(thr, cp);
}

/*
 * %store/qf/str <var-label>, <max-idx>
 */
bool of_STORE_QF_STR(vthread_t thr, vvp_code_t cp)
{
      return store_qf<string, vvp_queue_string>(thr, cp);
}

/*
 * %store/qb/v <var-label>, <max-idx>, <wid>
 */
bool of_STORE_QF_V(vthread_t thr, vvp_code_t cp)
{
      return store_qf<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[1]);
}

/*
 * %store/qf/o <var-label>, <max-idx>
 */
bool of_STORE_QF_O(vthread_t thr, vvp_code_t cp)
{
      return store_qf<vvp_object_t, vvp_queue_object>(thr, cp);
}

template <typename ELEM, class QTYPE>
static bool store_qobj(vthread_t thr, vvp_code_t cp, unsigned wid=0)
{
// FIXME: Can we actually use wid here?
      (void)wid;
      vvp_net_t*net = cp->net;

      vvp_queue*queue = get_queue_object<QTYPE>(thr, net);
      assert(queue);

      vvp_object_t src;
      thr->pop_object(src);

        // If it is null just clear the queue
      if (src.test_nil())
	    queue->erase_tail(0);
      else {
	    unsigned max_size = thr->words[cp->bit_idx[0]].w_int;
	    queue->copy_elems(src, max_size);
      }

      return true;
}

bool of_STORE_QOBJ_R(vthread_t thr, vvp_code_t cp)
{
      return store_qobj<double, vvp_queue_real>(thr, cp);
}

bool of_STORE_QOBJ_STR(vthread_t thr, vvp_code_t cp)
{
      return store_qobj<string, vvp_queue_string>(thr, cp);
}

bool of_STORE_QOBJ_V(vthread_t thr, vvp_code_t cp)
{
      return store_qobj<vvp_vector4_t, vvp_queue_vec4>(thr, cp, cp->bit_idx[1]);
}

static void vvp_send(vthread_t thr, vvp_net_ptr_t ptr, const double&val)
{
      vvp_send_real(ptr, val, thr->wt_context);
}

static void vvp_send(vthread_t thr, vvp_net_ptr_t ptr, const string&val)
{
      vvp_send_string(ptr, val, thr->wt_context);
}

template <typename ELEM>
static bool store(vthread_t thr, vvp_code_t cp)
{
      ELEM val;
      pop_value(thr, val, 0);
	/* set the value into port 0 of the destination. */
      vvp_net_ptr_t ptr (cp->net, 0);
      vvp_send(thr, ptr, val);
      return true;
}

bool of_STORE_REAL(vthread_t thr, vvp_code_t cp)
{
      return store<double>(thr, cp);
}

template <typename ELEM>
static bool storea(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      ELEM val;
      pop_value(thr, val, 0);

      if (thr->flags[4] != BIT4_1) {
	    unsigned adr = thr->words[idx].w_int;
	    cp->array->set_word(adr, val);
      }

      return true;
}

/*
 * %store/reala <var-label> <index>
 */
bool of_STORE_REALA(vthread_t thr, vvp_code_t cp)
{
      return storea<double>(thr, cp);
}

bool of_STORE_STR(vthread_t thr, vvp_code_t cp)
{
      return store<string>(thr, cp);
}

/*
 * %store/stra <array-label> <index>
 */
bool of_STORE_STRA(vthread_t thr, vvp_code_t cp)
{
      return storea<string>(thr, cp);
}

/*
 * %store/vec4 <var-label>, <offset>, <wid>
 *
 * <offset> is the index register that contains the base offset into
 * the destination. If zero, the offset of 0 is used instead of index
 * register zero. The offset value is SIGNED, and can be negative.
 *
 * <wid> is the actual width, an unsigned number.
 *
 * This function tests flag bit 4. If that flag is set, and <offset>
 * is an actual index register (not zero) then this assumes that the
 * calculation of the <offset> contents failed, and the store is
 * aborted.
 *
 * NOTE: This instruction may loose the <wid> argument because it is
 * not consistent with the %store/vec4/<etc> instructions which have
 * no <wid>.
 */
bool of_STORE_VEC4(vthread_t thr, vvp_code_t cp)
{
      vvp_net_ptr_t ptr(cp->net, 0);
      vvp_signal_value*sig = dynamic_cast<vvp_signal_value*> (cp->net->fil);
      unsigned off_index = cp->bit_idx[0];
      unsigned int wid = cp->bit_idx[1];

      int64_t off = off_index ? thr->words[off_index].w_int : 0;
      unsigned int sig_value_size = sig->value_size();

      vvp_vector4_t&val = thr->peek_vec4();
      unsigned val_size = val.size();

      if (val_size < wid) {
	    cerr << thr->get_fileline()
	         << "XXXX Internal error: val.size()=" << val_size
		 << ", expecting >= " << wid << endl;
	    // Pad with X values to prevent crash
	    vvp_vector4_t padded(wid, BIT4_X);
	    for (unsigned i = 0; i < val_size; i++)
		  padded.set_bit(i, val.value(i));
	    val = padded;
	    val_size = wid;
      }
      if (val_size > wid) {
	    val.resize(wid);
      }

	// If there is a problem loading the index register, flags-4
	// will be set to 1, and we know here to skip the actual assignment.
      if (off_index!=0 && thr->flags[4] == BIT4_1) {
	    thr->pop_vec4(1);
	    return true;
      }

      if (!resize_rval_vec(val, off, sig_value_size)) {
	    thr->pop_vec4(1);
	    return true;
      }

      if (off == 0 && val.size() == sig_value_size)
	    vvp_send_vec4(ptr, val, thr->wt_context);
      else
	    vvp_send_vec4_pv(ptr, val, off, sig_value_size, thr->wt_context);

      thr->pop_vec4(1);
      return true;
}

/*
 * %store/vec4a <var-label>, <addr>, <offset>
 */
bool of_STORE_VEC4A(vthread_t thr, vvp_code_t cp)
{
      unsigned adr_index = cp->bit_idx[0];
      unsigned off_index = cp->bit_idx[1];

      long adr = adr_index? thr->words[adr_index].w_int : 0;
      int64_t off = off_index ? thr->words[off_index].w_int : 0;

	// Suppress action if flags-4 is true.
      if (thr->flags[4] == BIT4_1) {
	    thr->pop_vec4(1);
	    return true;
      }

      vvp_vector4_t &value = thr->peek_vec4();

      if (!resize_rval_vec(value, off, cp->array->get_word_size())) {
	    thr->pop_vec4(1);
	    return true;
      }

      cp->array->set_word(adr, off, value);

      thr->pop_vec4(1);
      return true;
}

/*
 * %sub
 *   pop r;
 *   pop l;
 *   push l-r;
 */
bool of_SUB(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t r = thr->pop_vec4();
      vvp_vector4_t&l = thr->peek_vec4();

      l.sub(r);
      return true;
}

/*
 * %subi <vala>, <valb>, <wid>
 *
 * Pop1 operand, get the other operand from the arguments, and push
 * the result.
 */
bool of_SUBI(vthread_t thr, vvp_code_t cp)
{
      unsigned wid = cp->number;

      vvp_vector4_t&l = thr->peek_vec4();

	// I expect that most of the bits of an immediate value are
	// going to be zero, so start the result vector with all zero
	// bits. Then we only need to replace the bits that are different.
      vvp_vector4_t r (wid, BIT4_0);
      get_immediate_rval (cp, r);

      l.sub(r);

      return true;

}

bool of_SUB_WR(vthread_t thr, vvp_code_t)
{
      double r = thr->pop_real();
      double l = thr->pop_real();
      thr->push_real(l - r);
      return true;
}

/*
 * %substr <first>, <last>
 * Pop a string, take the substring (SystemVerilog style), and return
 * the result to the stack. This opcode actually works by editing the
 * string in place.
 */
bool of_SUBSTR(vthread_t thr, vvp_code_t cp)
{
      int32_t first = thr->words[cp->bit_idx[0]].w_int;
      int32_t last = thr->words[cp->bit_idx[1]].w_int;
      string&val = thr->peek_str(0);

      if (first < 0 || last < first || last >= (int32_t)val.size()) {
	    val = string("");
	    return true;
      }

      val = val.substr(first, last-first+1);
      return true;
}

/*
 * %substr/vec4 <index>, <wid>
 */
bool of_SUBSTR_VEC4(vthread_t thr, vvp_code_t cp)
{
      unsigned sel_idx = cp->bit_idx[0];
      unsigned wid = cp->bit_idx[1];

      int32_t sel = thr->words[sel_idx].w_int;
      const string&val = thr->peek_str(0);

      assert(wid%8 == 0);

      if (sel < 0 || sel >= (int32_t)val.size()) {
	    vvp_vector4_t res (wid, BIT4_0);
	    thr->push_vec4(res);
	    return true;
      }

      vvp_vector4_t res (wid, BIT4_0);

      assert(wid==8);
      unsigned char tmp = val[sel];
      for (int idx = 0 ; idx < 8 ; idx += 1) {
	    if (tmp & (1<<idx))
		  res.set_bit(idx, BIT4_1);
      }

      thr->push_vec4(res);
      return true;
}

bool of_FILE_LINE(vthread_t thr, vvp_code_t cp)
{
      vpiHandle handle = cp->handle;

	/* When it is available, keep the file/line information in the
	   thread for error/warning messages. */
      thr->set_fileline(vpi_get_str(vpiFile, handle),
                        vpi_get(vpiLineNo, handle));

      if (show_file_line)
	    cerr << thr->get_fileline()
	         << vpi_get_str(_vpiDescription, handle) << endl;

      return true;
}

/*
 * %test_nul <var-label>;
 * Test if the object at the specified variable is nil. If so, write
 * "1" into flags[4], otherwise write "0" into flags[4].
 */
bool of_TEST_NUL(vthread_t thr, vvp_code_t cp)
{
      vvp_net_t*net = cp->net;

      assert(net);
      vvp_fun_signal_object*obj = dynamic_cast<vvp_fun_signal_object*> (net->fun);
      assert(obj);

      if (obj->get_object().test_nil())
	    thr->flags[4] = BIT4_1;
      else
	    thr->flags[4] = BIT4_0;

      return true;
}

bool of_TEST_NUL_A(vthread_t thr, vvp_code_t cp)
{
      unsigned idx = cp->bit_idx[0];
      unsigned adr = thr->words[idx].w_int;
      vvp_object_t word;

	/* If the address is undefined, return true. */
      if (thr->flags[4] == BIT4_1) {
	    return true;
      }

      cp->array->get_word_obj(adr, word);
      if (word.test_nil())
	    thr->flags[4] = BIT4_1;
      else
	    thr->flags[4] = BIT4_0;

      return true;
}

bool of_TEST_NUL_OBJ(vthread_t thr, vvp_code_t)
{
      if (thr->peek_object().test_nil())
	    thr->flags[4] = BIT4_1;
      else
	    thr->flags[4] = BIT4_0;
      return true;
}

/*
 * %test_nul/dar <idx_register>
 * Peek at the darray on the object stack.
 * Test if the element at the given index is null.
 * Set flag 4 to 1 if null, 0 if not null.
 */
bool of_TEST_NUL_DAR(vthread_t thr, vvp_code_t cp)
{
      unsigned idx_reg = cp->number;
      unsigned idx = thr->words[idx_reg].w_uint;

      vvp_object_t&obj = thr->peek_object();
      vvp_darray*darray = obj.peek<vvp_darray>();

      // If the darray is null, the element is also null
      if (!darray) {
	    thr->flags[4] = BIT4_1;
	    return true;
      }

      vvp_object_t val;
      darray->get_word(idx, val);

      if (val.test_nil())
	    thr->flags[4] = BIT4_1;
      else
	    thr->flags[4] = BIT4_0;

      return true;
}

/*
 * %test_nul/prop <pid>, <idx>
 */
bool of_TEST_NUL_PROP(vthread_t thr, vvp_code_t cp)
{
      unsigned pid = cp->number;
      unsigned idx = cp->bit_idx[0];

      if (idx != 0) {
	    assert(idx < vthread_s::WORDS_COUNT);
	    idx = thr->words[idx].w_uint;
      }

      vvp_object_t&obj = thr->peek_object();
      vvp_cobject*cobj  = obj.peek<vvp_cobject>();

      // If the object is null, the property is also null
      if (!cobj) {
	    thr->flags[4] = BIT4_1;
	    return true;
      }

      vvp_object_t val;
      cobj->get_object(pid, val, idx);

      if (val.test_nil())
	    thr->flags[4] = BIT4_1;
      else
	    thr->flags[4] = BIT4_0;

      return true;
}

bool of_VPI_CALL(vthread_t thr, vvp_code_t cp)
{
      vpip_execute_vpi_call(thr, cp->handle);

      if (schedule_stopped()) {
	    if (! schedule_finished())
		  schedule_vthread(thr, 0, false);

	    return false;
      }

      return schedule_finished()? false : true;
}

/* %wait <label>;
 * Implement the wait by locating the vvp_net_T for the event, and
 * adding this thread to the threads list for the event. The some
 * argument is the  reference to the functor to wait for. This must be
 * an event object of some sort.
 */
bool of_WAIT(vthread_t thr, vvp_code_t cp)
{
      assert(! thr->i_am_in_function);
      assert(! thr->waiting_for_event);
      thr->waiting_for_event = 1;

	/* Add this thread to the list in the event. */
      waitable_hooks_s*ep = dynamic_cast<waitable_hooks_s*> (cp->net->fun);
      assert(ep);
      thr->wait_next = ep->add_waiting_thread(thr);

	/* Return false to suspend this thread. */
      return false;
}

/*
 * Implement the %wait/fork (SystemVerilog) instruction by suspending
 * the current thread until all the detached children have finished.
 */
bool of_WAIT_FORK(vthread_t thr, vvp_code_t)
{
	/* If a %wait/fork is being executed then the parent thread
	 * cannot be waiting in a join or already waiting. */
      assert(! thr->i_am_in_function);
      assert(! thr->i_am_joining);
      assert(! thr->i_am_waiting);

	/* There should be no active children when waiting. */
      assert(thr->children.empty());

	/* If there are no detached children then there is nothing to
	 * wait for. */
      if (thr->detached_children.empty()) return true;

	/* Flag that this process is waiting for the detached children
	 * to finish and suspend it. */
      thr->i_am_waiting = 1;
      return false;
}

/*
 * %xnor
 */
bool of_XNOR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valr = thr->pop_vec4();
      vvp_vector4_t&vall = thr->peek_vec4();
      assert(vall.size() == valr.size());
      unsigned wid = vall.size();

      for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {

	    vvp_bit4_t lb = vall.value(idx);
	    vvp_bit4_t rb = valr.value(idx);
	    vall.set_bit(idx, ~(lb ^ rb));
      }

      return true;
}

/*
 * %xor
 */
bool of_XOR(vthread_t thr, vvp_code_t)
{
      vvp_vector4_t valr = thr->pop_vec4();
      vvp_vector4_t&vall = thr->peek_vec4();
      assert(vall.size() == valr.size());
      unsigned wid = vall.size();

      for (unsigned idx = 0 ;  idx < wid ;  idx += 1) {

	    vvp_bit4_t lb = vall.value(idx);
	    vvp_bit4_t rb = valr.value(idx);
	    vall.set_bit(idx, lb ^ rb);
      }

      return true;
}


bool of_ZOMBIE(vthread_t thr, vvp_code_t)
{
      thr->pc = codespace_null();
      if ((thr->parent == 0) && (thr->children.empty())) {
	    if (thr->delay_delete)
		  schedule_del_thr(thr);
	    else
		  vthread_delete(thr);
      }
      return false;
}

/*
 * This is a phantom opcode used to call user defined functions. It
 * is used in code generated by the .ufunc statement. It contains a
 * pointer to the executable code of the function and a pointer to
 * a ufunc_core object that has all the port information about the
 * function.
 */
static bool do_exec_ufunc(vthread_t thr, vvp_code_t cp, vthread_t child)
{
      __vpiScope*child_scope = cp->ufunc_core_ptr->func_scope();
      assert(child_scope);

      assert(child_scope->get_type_code() == vpiFunction);
      assert(thr->children.empty());


        /* We can take a number of shortcuts because we know that a
           continuous assignment can only occur in a static scope. */
      assert(thr->wt_context == 0);
      assert(thr->rd_context == 0);

        /* If an automatic function, allocate a context for this call. */
      vvp_context_t child_context = 0;
      if (child_scope->is_automatic()) {
            child_context = vthread_alloc_context(child_scope);
            thr->wt_context = child_context;
            thr->rd_context = child_context;
      }

      child->wt_context = child_context;
      child->rd_context = child_context;

      // Propagate fork_this from parent if parent has it set
      if (thr->fork_this_net_ != 0) {
	    child->fork_this_net_ = thr->fork_this_net_;
	    if (!thr->fork_this_obj_.test_nil()) {
		  child->fork_this_obj_ = thr->fork_this_obj_;
	    } else if (thr->wt_context) {
		  // Fallback: try to read @ from parent's wt_context
		  vvp_fun_signal_object_aa*fun_aa =
			dynamic_cast<vvp_fun_signal_object_aa*>(thr->fork_this_net_->fun);
		  if (fun_aa) {
			child->fork_this_obj_ = fun_aa->get_object_from_context(thr->wt_context);
		  }
	    }
      }

	/* Copy all the inputs to the ufunc object to the port
	   variables of the function. This copies all the values
	   atomically. */
      cp->ufunc_core_ptr->assign_bits_to_ports(child_context);
      child->delay_delete = 1;

      child->parent = thr;
      thr->children.insert(child);
	// This should be the only child
      assert(thr->children.size()==1);

      child->is_scheduled = 1;
      child->i_am_in_function = 1;
      vthread_run(child);
      running_thread = thr;

      if (child->i_have_ended) {
	    do_join(thr, child);
            return true;
      } else {
	    thr->i_am_joining = 1;
	    return false;
      }
}

bool of_EXEC_UFUNC_REAL(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*child_scope = cp->ufunc_core_ptr->func_scope();
      assert(child_scope);

	/* Create a temporary thread and run it immediately. */
      vthread_t child = vthread_new(cp->cptr, child_scope);
      thr->push_real(0.0);
      child->args_real.push_back(0);

      return do_exec_ufunc(thr, cp, child);
}

bool of_EXEC_UFUNC_VEC4(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*child_scope = cp->ufunc_core_ptr->func_scope();
      assert(child_scope);

      vpiScopeFunction*scope_func = dynamic_cast<vpiScopeFunction*>(child_scope);
      assert(scope_func);

	/* Create a temporary thread and run it immediately. */
      vthread_t child = vthread_new(cp->cptr, child_scope);
      thr->push_vec4(vvp_vector4_t(scope_func->get_func_width(), scope_func->get_func_init_val()));
      child->args_vec4.push_back(0);

      return do_exec_ufunc(thr, cp, child);
}

/*
 * This is a phantom opcode used to harvest the result of calling a user
 * defined function. It is used in code generated by the .ufunc statement.
 */
bool of_REAP_UFUNC(vthread_t thr, vvp_code_t cp)
{
      __vpiScope*child_scope = cp->ufunc_core_ptr->func_scope();
      assert(child_scope);

	/* Copy the output from the result variable to the output
	   ports of the .ufunc device. */
      cp->ufunc_core_ptr->finish_thread();

        /* If an automatic function, free the context for this call. */
      if (child_scope->is_automatic()) {
            vthread_free_context(thr->rd_context, child_scope);
            thr->wt_context = 0;
            thr->rd_context = 0;
      }

      return true;
}

/*
 * Queue property method operations.
 * These opcodes operate on queue properties of class objects.
 * The queue object is on the object stack (will be cleaned up by subsequent %pop/obj).
 * Values are on vec4/object stack.
 */

/*
 * Helper to get a queue from object stack, creating if needed.
 * Returns the queue pointer, or NULL if the object is not a queue.
 */
template <class QTYPE>
static vvp_queue* get_qprop_queue(vthread_t thr)
{
      vvp_object_t&obj = thr->peek_object();
      vvp_queue*queue = obj.peek<vvp_queue>();

      // If queue is nil, allocate it
      if (queue == 0) {
	    if (obj.test_nil()) {
		  queue = new QTYPE;
		  obj.reset(queue);
	    }
      }
      return queue;
}

/*
 * %qprop/qb/v <pidx> - push_back vec4 value to queue property
 * Stack: [class_obj, queue_obj] + vec4 stack top
 * The property index is used to store the queue back if it was newly created.
 */
bool of_QPROP_QB_V(vthread_t thr, vvp_code_t cp)
{
      size_t pidx = cp->number;

      // Pop the value to push
      vvp_vector4_t value = thr->pop_vec4();

      // Top of object stack is the queue, second is the class object
      vvp_object_t&queue_obj = thr->peek_object(0);
      vvp_object_t&class_obj = thr->peek_object(1);

      // Get or create the queue
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 && queue_obj.test_nil()) {
	    // Queue was nil - create new queue
	    queue = new vvp_queue_vec4;
	    queue_obj.reset(queue);

	    // Store the new queue back to the class property
	    vvp_cobject*cobj = class_obj.peek<vvp_cobject>();
	    if (cobj) {
		  cobj->set_object(pidx, queue_obj, 0);
	    }
      }

      if (queue) {
	    queue->push_back(value, 0); // 0 = unlimited size
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property push_back on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/qb/o <pidx> - push_back object value to queue property
 * Stack: [class_obj, queue_obj, value_obj]
 * Pushes a class/struct object onto the back of a queue property.
 */
bool of_QPROP_QB_O(vthread_t thr, vvp_code_t cp)
{
      size_t pidx = cp->number;

      // Pop the value object (top of stack)
      vvp_object_t value;
      thr->pop_object(value);

      // Top of object stack is the queue, second is the class object
      vvp_object_t&queue_obj = thr->peek_object(0);
      vvp_object_t&class_obj = thr->peek_object(1);

      // Get or create the queue
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 && queue_obj.test_nil()) {
	    queue = new vvp_queue_object;
	    queue_obj.reset(queue);
	    vvp_cobject*cobj = class_obj.peek<vvp_cobject>();
	    if (cobj) {
		  cobj->set_object(pidx, queue_obj, 0);
	    }
      }

      if (queue) {
	    queue->push_back(value, 0); // 0 = unlimited size
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property push_back on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/qf/v <pidx> - push_front vec4 value to queue property
 * Stack: [class_obj, queue_obj] + vec4 stack top
 */
bool of_QPROP_QF_V(vthread_t thr, vvp_code_t cp)
{
      size_t pidx = cp->number;

      // Pop the value to push
      vvp_vector4_t value = thr->pop_vec4();

      // Top of object stack is the queue, second is the class object
      vvp_object_t&queue_obj = thr->peek_object(0);
      vvp_object_t&class_obj = thr->peek_object(1);

      // Get or create the queue
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 && queue_obj.test_nil()) {
	    queue = new vvp_queue_vec4;
	    queue_obj.reset(queue);
	    vvp_cobject*cobj = class_obj.peek<vvp_cobject>();
	    if (cobj) {
		  cobj->set_object(pidx, queue_obj, 0);
	    }
      }

      if (queue) {
	    queue->push_front(value, 0); // 0 = unlimited size
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property push_front on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/qf/o <pidx> - push_front object value to queue property
 * Stack: [class_obj, queue_obj, value_obj]
 * Pushes a class/struct object onto the front of a queue property.
 */
bool of_QPROP_QF_O(vthread_t thr, vvp_code_t cp)
{
      size_t pidx = cp->number;

      // Pop the value object (top of stack)
      vvp_object_t value;
      thr->pop_object(value);

      // Top of object stack is the queue, second is the class object
      vvp_object_t&queue_obj = thr->peek_object(0);
      vvp_object_t&class_obj = thr->peek_object(1);

      // Get or create the queue
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 && queue_obj.test_nil()) {
	    queue = new vvp_queue_object;
	    queue_obj.reset(queue);
	    vvp_cobject*cobj = class_obj.peek<vvp_cobject>();
	    if (cobj) {
		  cobj->set_object(pidx, queue_obj, 0);
	    }
      }

      if (queue) {
	    queue->push_front(value, 0); // 0 = unlimited size
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property push_front on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/insert/v - insert vec4 value into queue property at index
 * Index is in word register 3.
 */
bool of_QPROP_INSERT_V(vthread_t thr, vvp_code_t)
{
      // Pop the value to insert
      vvp_vector4_t value = thr->pop_vec4();

      // Get index from word register 3
      int64_t idx = thr->words[3].w_int;

      // Get queue from object stack
      vvp_queue*queue = get_qprop_queue<vvp_queue_vec4>(thr);
      if (queue) {
	    if (idx < 0) {
		  cerr << thr->get_fileline()
		       << "Warning: cannot insert at negative index (" << idx << ")." << endl;
	    } else {
		  queue->insert(idx, value, 0);
	    }
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property insert on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/insert/o - insert object value into queue property at index
 * Inserts a class/struct object into a queue property at the specified index.
 * Index is in word register 3.
 */
bool of_QPROP_INSERT_O(vthread_t thr, vvp_code_t)
{
      // Pop the value object (top of stack)
      vvp_object_t value;
      thr->pop_object(value);

      // Get index from word register 3
      int64_t idx = thr->words[3].w_int;

      // Get queue from object stack
      vvp_queue*queue = get_qprop_queue<vvp_queue_object>(thr);
      if (queue) {
	    if (idx < 0) {
		  cerr << thr->get_fileline()
		       << "Warning: cannot insert at negative index (" << idx << ")." << endl;
	    } else {
		  queue->insert(idx, value, 0);
	    }
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property insert on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/set/v <pidx> - set element at index in queue property with vec4 value
 * Stack: [class_obj, queue_obj] + vec4 stack top, index in word reg 3
 * This opcode includes auto-vivification - creates queue if null.
 */
bool of_QPROP_SET_V(vthread_t thr, vvp_code_t cp)
{
      size_t pidx = cp->number;

      // Pop the value to set
      vvp_vector4_t value = thr->pop_vec4();

      // Get index from word register 3
      int64_t idx = thr->words[3].w_int;

      // Top of object stack is the queue, second is the class object
      vvp_object_t&queue_obj = thr->peek_object(0);
      vvp_object_t&class_obj = thr->peek_object(1);

      // Get or create the queue (auto-vivification)
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue == 0 && queue_obj.test_nil()) {
	    // Queue was nil - create new queue
	    queue = new vvp_queue_vec4;
	    queue_obj.reset(queue);

	    // Store the new queue back to the class property
	    vvp_cobject*cobj = class_obj.peek<vvp_cobject>();
	    if (cobj) {
		  cobj->set_object(pidx, queue_obj, 0);
	    }
      }

      if (queue) {
	    if (idx < 0) {
		  cerr << thr->get_fileline()
		       << "Warning: cannot set element at negative index (" << idx << ")." << endl;
	    } else {
		  // Use set_word_max to auto-extend queue if needed
		  queue->set_word_max(idx, value, 0);
	    }
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property set on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/delete - clear queue property (delete all elements)
 * This clears the queue contents in place, not just the local reference.
 */
bool of_QPROP_DELETE(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();

      // Get the actual queue object and clear its contents
      vvp_queue*queue = queue_obj.peek<vvp_queue>();
      if (queue) {
	    // Clear all elements from the queue
	    while (queue->get_size() > 0) {
		  queue->pop_back();
	    }
      }
      return true;
}

/*
 * %qprop/delete/elem - delete element from queue property at index
 * Index is in word register 3.
 */
bool of_QPROP_DELETE_ELEM(vthread_t thr, vvp_code_t)
{
      // Get index from word register 3
      int64_t idx = thr->words[3].w_int;

      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      if (queue) {
	    if (idx < 0 || (size_t)idx >= queue->get_size()) {
		  cerr << thr->get_fileline()
		       << "Warning: queue delete index (" << idx << ") out of range." << endl;
	    } else {
		  queue->erase(idx);
	    }
      } else {
	    cerr << thr->get_fileline()
	         << "Error: queue property delete element on non-queue object." << endl;
      }
      return true;
}

/*
 * %qprop/reverse - reverse a queue property in place
 * Queue object is on top of the object stack.
 */
bool of_QPROP_REVERSE(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      if (queue) {
	    queue->reverse();
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: reverse() on empty or nil queue property." << endl;
      }
      return true;
}

/*
 * %cvg/sample packed - sample a covergroup property with coverpoint values
 * packed = (bins_count << 8) | cp_count
 * Covergroup object is on top of the object stack.
 * Coverpoint values are in integer registers 0..cp_count-1.
 * Increments the sample counter and tracks unique values per coverpoint.
 */
bool of_CVG_SAMPLE(vthread_t thr, vvp_code_t cp)
{
      // Unpack the coverpoint count and bins count from opcode
      unsigned packed = cp->number;
      unsigned cp_count = packed & 0xFF;
      unsigned bins_count = packed >> 8;

      // Get covergroup object from stack
      vvp_object_t&cvg_obj = thr->peek_object();
      vvp_cobject*cobj = cvg_obj.peek<vvp_cobject>();

      if (cobj) {
	    // Increment m_sample_count property (index 3 in __ivl_covergroup)
	    // Properties are sorted alphabetically by Icarus:
	    // 0=m_bins_hit, 1=m_enabled, 2=m_inst_name, 3=m_sample_count, 4=m_target_bins
	    vvp_vector4_t cur_count;
	    cobj->get_vec4(3, cur_count);
	    uint64_t count = 0;
	    vector4_to_value(cur_count, count);
	    count++;
	    vvp_vector4_t new_count(32);
	    for (unsigned b = 0; b < 32; b++) {
		  new_count.set_bit(b, ((count >> b) & 1) ? BIT4_1 : BIT4_0);
	    }
	    cobj->set_vec4(3, new_count);

	    // Set m_target_bins (property 4) to bins_count
	    // This overrides the default value from the constructor
	    if (bins_count > 0) {
		  vvp_vector4_t target_bins(32);
		  for (unsigned b = 0; b < 32; b++) {
			target_bins.set_bit(b, ((bins_count >> b) & 1) ? BIT4_1 : BIT4_0);
		  }
		  cobj->set_vec4(4, target_bins);
	    }

	    // Track unique coverpoint values in m_bins_hit (property 0)
	    // m_bins_hit is an associative array with string keys
	    // Key format: "cp<idx>:<value>" to identify coverpoint and value

	    // Get or create m_bins_hit associative array
	    vvp_object_t bins_obj;
	    cobj->get_object(0, bins_obj, 0);
	    vvp_assoc*bins = bins_obj.peek<vvp_assoc>();

	    if (bins == 0) {
		  // Create a new associative array if it doesn't exist
		  vvp_assoc_vec4*new_bins = new vvp_assoc_vec4(32);
		  bins_obj.reset(new_bins);
		  cobj->set_object(0, bins_obj, 0);
		  bins = new_bins;
	    }

	    if (cp_count > 0) {
		  // For each coverpoint value, if this value hasn't been seen before,
		  // add it to the associative array with value 1
		  for (unsigned idx = 0; idx < cp_count; idx++) {
			// Read coverpoint value from integer register
			int64_t cp_value = thr->words[idx].w_int;

			// Create string key encoding coverpoint index and value
			char key_buf[64];
			snprintf(key_buf, sizeof(key_buf), "cp%u:%lld",
				 idx, (long long)cp_value);
			string key_str(key_buf);

			// Check if this value has been seen before
			if (!bins->exists(key_str)) {
			      // Not seen before, add it with value 1
			      vvp_vector4_t one(32);
			      one.set_bit(0, BIT4_1);
			      bins->set_word(key_str, one);
			}
		  }
	    } else {
		  // For parameterized covergroups (sample with arguments), cp_count is 0
		  // because coverpoint values aren't evaluated yet. Track each sample
		  // call as a bin hit to provide approximate coverage progress.
		  // Use sample count as key to count unique samples.
		  char key_buf[64];
		  snprintf(key_buf, sizeof(key_buf), "sample:%llu", (unsigned long long)count);
		  string key_str(key_buf);
		  if (!bins->exists(key_str)) {
			vvp_vector4_t one(32);
			one.set_bit(0, BIT4_1);
			bins->set_word(key_str, one);
		  }
	    }
      }
      return true;
}

/*
 * %qprop/shuffle - shuffle a queue property in place
 * Queue object is on top of the object stack.
 */
bool of_QPROP_SHUFFLE(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      if (queue) {
	    queue->shuffle();
      } else {
	    cerr << thr->get_fileline()
	         << "Warning: shuffle() on empty or nil queue property." << endl;
      }
      return true;
}

/*
 * %qprop/unique_index - return queue of indices of first unique occurrences
 * Queue object is on top of the object stack, result replaces it.
 */
bool of_QPROP_UNIQUE_INDEX(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack (peek to access, then pop and push result)
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      vvp_object_t result;
      if (queue && queue->get_size() > 0) {
	    result = queue->unique_index();
      }
      // Pop the original queue and push the result
      vvp_object_t discard;
      thr->pop_object(discard);
      thr->push_object(result);
      return true;
}

/*
 * %qprop/min_index - return queue of indices of minimum elements
 * Queue object is on top of the object stack, result replaces it.
 */
bool of_QPROP_MIN_INDEX(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      vvp_object_t result;
      if (queue && queue->get_size() > 0) {
	    result = queue->min_index();
      }
      // Pop the original queue and push the result
      vvp_object_t discard;
      thr->pop_object(discard);
      thr->push_object(result);
      return true;
}

/*
 * %qprop/max_index - return queue of indices of maximum elements
 * Queue object is on top of the object stack, result replaces it.
 */
bool of_QPROP_MAX_INDEX(vthread_t thr, vvp_code_t)
{
      // Get queue from object stack
      vvp_object_t&queue_obj = thr->peek_object();
      vvp_queue*queue = queue_obj.peek<vvp_queue>();

      vvp_object_t result;
      if (queue && queue->get_size() > 0) {
	    result = queue->max_index();
      }
      // Pop the original queue and push the result
      vvp_object_t discard;
      thr->pop_object(discard);
      thr->push_object(result);
      return true;
}
