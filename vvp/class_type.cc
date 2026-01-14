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

# include  "class_type.h"
# include  "compile.h"
# include  "factory_registry.h"
# include  "vpi_priv.h"
# include  "vvp_cobject.h"
# include  "vvp_darray.h"
# include  "config.h"
# include  <algorithm>
# include  <map>
# include  <vector>
#ifdef CHECK_WITH_VALGRIND
# include  "vvp_cleanup.h"
#endif
# include  <cassert>
# include  <cstdio>
# include  <type_traits>

using namespace std;

/*
 * Helper function to count the number of 1 bits in an int64_t.
 * Used for $countones constraint evaluation.
 */
static int count_ones(int64_t val)
{
      int count = 0;
      // Use unsigned to handle all 64 bits correctly
      uint64_t uval = static_cast<uint64_t>(val);
      while (uval) {
	    count += (uval & 1);
	    uval >>= 1;
      }
      return count;
}

/*
 * Helper function to compute ceiling log base 2.
 * Used for $clog2 constraint evaluation.
 */
static int clog2(int64_t val)
{
      if (val <= 0) return 0;
      if (val == 1) return 0;
      int result = 0;
      val--;  // For ceiling, we need (val-1) and then add 1
      while (val > 0) {
	    result++;
	    val >>= 1;
      }
      return result;
}

/*
 * This class_property_t class is an abstract base class for
 * representing a property of an instance. The definition keeps and
 * array (of pointers) of these in order to define the the class.
 */
class class_property_t {
    public:
      inline class_property_t() { }
      virtual ~class_property_t() =0;
	// How much space does an instance of this property require?
      virtual size_t instance_size() const =0;

      void set_offset(size_t off) { offset_ = off; }

    public:
      virtual void construct(char*buf) const;
      virtual void destruct(char*buf) const;

      virtual void set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx);
      virtual void get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx);
      virtual bool supports_vec4() const { return false; }
      virtual bool is_signed() const { return false; }
      virtual unsigned bit_width() const { return 0; }
      virtual uint64_t array_size() const { return 1; }

      virtual void set_real(char*buf, double val);
      virtual double get_real(char*buf);

      virtual void set_string(char*buf, const std::string&val);
      virtual string get_string(char*buf);

      virtual void set_object(char*buf, const vvp_object_t&val, uint64_t element);
      virtual void get_object(char*buf, vvp_object_t&val, uint64_t element);

	// Implement polymorphic shallow copy.
      virtual void copy(char*buf, char*src) = 0;

    protected:
      size_t offset_;
};

class_property_t::~class_property_t()
{
}

void class_property_t::construct(char*) const
{
}

void class_property_t::destruct(char*) const
{
}

void class_property_t::set_vec4(char*, const vvp_vector4_t&, uint64_t)
{
      assert(0);
}

void class_property_t::get_vec4(char*, vvp_vector4_t&, uint64_t)
{
      assert(0);
}

void class_property_t::set_real(char*, double)
{
      assert(0);
}

double class_property_t::get_real(char*)
{
      assert(0);
      return 0.0;
}

void class_property_t::set_string(char*, const string&)
{
      assert(0);
}

string class_property_t::get_string(char*)
{
      assert(0);
      return "";
}

void class_property_t::set_object(char*, const vvp_object_t&, uint64_t)
{
      // This property type doesn't support objects.
      // This can happen when config_db or similar code tries to store an object
      // to a property that is actually an enum/int. Gracefully ignore.
      // Only warn once to avoid noise.
      static bool warned = false;
      if (!warned) {
            warned = true;
            // Suppress warning - this is a known limitation with config_db
            // trying object operations on enum/int properties
      }
}

void class_property_t::get_object(char*, vvp_object_t& val, uint64_t)
{
      // This property type doesn't support objects.
      // Return nil object instead of crashing. Only warn once.
      static bool warned = false;
      if (!warned) {
            warned = true;
            // Suppress warning - this is a known limitation
      }
      val = vvp_object_t();
}

/*
 */
template <class T> class property_atom : public class_property_t {
    public:
      inline explicit property_atom(uint64_t as = 0) : array_size_(as == 0 ? 1 : as) { }
      ~property_atom() override { }

      size_t instance_size() const override { return array_size_ * sizeof(T); }

    public:
      void construct(char*buf) const override
      { T*tmp = reinterpret_cast<T*> (buf+offset_);
	for (uint64_t i = 0; i < array_size_; ++i)
	    tmp[i] = 0;
      }

      void set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx) override;
      void get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx) override;
      bool supports_vec4() const override { return true; }
      bool is_signed() const override { return std::is_signed<T>::value; }
      unsigned bit_width() const override { return sizeof(T) * 8; }
      uint64_t array_size() const override { return array_size_; }

      string get_string(char*buf) override
      { T*tmp = reinterpret_cast<T*> (buf+offset_);
	return std::to_string(tmp[0]);
      }

      void copy(char*dst, char*src) override;

    private:
      uint64_t array_size_;
};

class property_bit : public class_property_t {
    public:
      explicit inline property_bit(size_t wid, uint64_t as = 0)
	  : wid_(wid), array_size_(as == 0 ? 1 : as) { }
      ~property_bit() override { }

      size_t instance_size() const override { return array_size_ * sizeof(vvp_vector2_t); }

    public:
      void construct(char*buf) const override
      { for (uint64_t i = 0; i < array_size_; ++i)
	    new (buf+offset_ + i*sizeof(vvp_vector2_t)) vvp_vector2_t (0, wid_);
      }

      void destruct(char*buf) const override
      { vvp_vector2_t*tmp = reinterpret_cast<vvp_vector2_t*>(buf+offset_);
	for (uint64_t i = 0; i < array_size_; ++i)
	    (tmp+i)->~vvp_vector2_t();
      }

      void set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx) override;
      void get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx) override;
      bool supports_vec4() const override { return true; }
      unsigned bit_width() const override { return wid_; }
      uint64_t array_size() const override { return array_size_; }

      string get_string(char*buf) override;

      void copy(char*dst, char*src) override;

    private:
      size_t wid_;
      uint64_t array_size_;
};

class property_logic : public class_property_t {
    public:
      explicit inline property_logic(size_t wid, uint64_t as = 0)
	  : wid_(wid), array_size_(as == 0 ? 1 : as) { }
      ~property_logic() override { }

      size_t instance_size() const override { return array_size_ * sizeof(vvp_vector4_t); }

    public:
      void construct(char*buf) const override
      { for (uint64_t i = 0; i < array_size_; ++i)
	    new (buf+offset_ + i*sizeof(vvp_vector4_t)) vvp_vector4_t (wid_);
      }

      void destruct(char*buf) const override
      { vvp_vector4_t*tmp = reinterpret_cast<vvp_vector4_t*>(buf+offset_);
	for (uint64_t i = 0; i < array_size_; ++i)
	    (tmp+i)->~vvp_vector4_t();
      }

      void set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx) override;
      void get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx) override;
      bool supports_vec4() const override { return true; }
      unsigned bit_width() const override { return wid_; }
      uint64_t array_size() const override { return array_size_; }

      string get_string(char*buf) override;

      void copy(char*dst, char*src) override;

    private:
      size_t wid_;
      uint64_t array_size_;
};

template <class T> class property_real : public class_property_t {
    public:
      inline explicit property_real(void) { }
      ~property_real() override { }

      size_t instance_size() const override { return sizeof(T); }

    public:
      void construct(char*buf) const override
      { T*tmp = reinterpret_cast<T*> (buf+offset_);
	*tmp = 0.0;
      }

      void set_real(char*buf, double val) override;
      double get_real(char*buf) override;

      string get_string(char*buf) override
      { T*tmp = reinterpret_cast<T*> (buf+offset_);
	return std::to_string(*tmp);
      }

      void copy(char*dst, char*src) override;
};

class property_string : public class_property_t {
    public:
      inline explicit property_string(void) { }
      ~property_string() override { }

      size_t instance_size() const override { return sizeof(std::string); }

    public:
      void construct(char*buf) const override
      { /* string*tmp = */ new (buf+offset_) string; }

      void destruct(char*buf) const override
      { string*tmp = reinterpret_cast<string*> (buf+offset_);
	tmp->~string();
      }

      void set_string(char*buf, const string&) override;
      string get_string(char*buf) override;

      // Support for parameterized class specialization where the code was
      // generated for a base class method with T=int but actual type is string.
      // Convert vec4 to string by treating it as packed ASCII characters.
      void set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx) override;
      void get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx) override;

      void copy(char*dst, char*src) override;
};

class property_object : public class_property_t {
    public:
      inline explicit property_object(uint64_t as): array_size_(as==0? 1 : as) { }
      ~property_object() override { }

      size_t instance_size() const override { return array_size_ * sizeof(vvp_object_t); }

    public:
      void construct(char*buf) const override;

      void destruct(char*buf) const override;

      void set_object(char*buf, const vvp_object_t&, uint64_t) override;
      void get_object(char*buf, vvp_object_t&, uint64_t) override;

      string get_string(char*buf) override;

      void copy(char*dst, char*src) override;

    private:
      size_t array_size_;
};

template <class T> void property_atom<T>::set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      T*tmp = reinterpret_cast<T*> (buf+offset_);
      bool flag = vector4_to_value(val, tmp[idx], true, false);
      // If conversion fails (e.g., due to X/Z values), store 0 as default
      if (!flag) {
	    tmp[idx] = 0;
      }
}

template <class T> void property_atom<T>::get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      T*src = reinterpret_cast<T*> (buf+offset_);
      const size_t tmp_cnt = sizeof(T)<sizeof(unsigned long)
				       ? 1
				       : sizeof(T) / sizeof(unsigned long);
      unsigned long tmp[tmp_cnt];
      tmp[0] = src[idx];

      for (size_t i = 1 ; i < tmp_cnt ; i += 1)
	    tmp[i] = src[idx] >> i * 8 * sizeof(tmp[0]);

      val.resize(8*sizeof(T));
      val.setarray(0, val.size(), tmp);
}

template <class T> void property_atom<T>::copy(char*dst, char*src)
{
      T*dst_obj = reinterpret_cast<T*> (dst+offset_);
      T*src_obj = reinterpret_cast<T*> (src+offset_);
      for (uint64_t i = 0; i < array_size_; ++i)
	    dst_obj[i] = src_obj[i];
}

void property_bit::set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      vvp_vector2_t*obj = reinterpret_cast<vvp_vector2_t*> (buf+offset_);
      obj[idx] = val;
}

void property_bit::get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      const vvp_vector2_t*obj = reinterpret_cast<vvp_vector2_t*> (buf+offset_);
      val = vector2_to_vector4(obj[idx], obj[idx].size());
}

void property_bit::copy(char*dst, char*src)
{
      vvp_vector2_t*dst_obj = reinterpret_cast<vvp_vector2_t*> (dst+offset_);
      const vvp_vector2_t*src_obj = reinterpret_cast<vvp_vector2_t*> (src+offset_);
      for (uint64_t i = 0; i < array_size_; ++i)
	    dst_obj[i] = src_obj[i];
}

string property_bit::get_string(char*buf)
{
      const vvp_vector2_t*obj = reinterpret_cast<vvp_vector2_t*>(buf+offset_);
      vvp_vector4_t tmp = vector2_to_vector4(obj[0], obj[0].size());
      char str_buf[4096];
      tmp.as_string(str_buf, sizeof(str_buf));
      return string(str_buf);
}

void property_logic::set_vec4(char*buf, const vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      vvp_vector4_t*obj = reinterpret_cast<vvp_vector4_t*> (buf+offset_);
      obj[idx] = val;
}

void property_logic::get_vec4(char*buf, vvp_vector4_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      const vvp_vector4_t*obj = reinterpret_cast<vvp_vector4_t*> (buf+offset_);
      val = obj[idx];
}

void property_logic::copy(char*dst, char*src)
{
      vvp_vector4_t*dst_obj = reinterpret_cast<vvp_vector4_t*> (dst+offset_);
      const vvp_vector4_t*src_obj = reinterpret_cast<vvp_vector4_t*> (src+offset_);
      for (uint64_t i = 0; i < array_size_; ++i)
	    dst_obj[i] = src_obj[i];
}

string property_logic::get_string(char*buf)
{
      const vvp_vector4_t*obj = reinterpret_cast<vvp_vector4_t*>(buf+offset_);
      char str_buf[4096];
      obj[0].as_string(str_buf, sizeof(str_buf));
      return string(str_buf);
}

template <class T> void property_real<T>::set_real(char*buf, double val)
{
      T*tmp = reinterpret_cast<T*>(buf+offset_);
      *tmp = val;
}

template <class T> double property_real<T>::get_real(char*buf)
{
      T*tmp = reinterpret_cast<T*>(buf+offset_);
      return *tmp;
}

template <class T> void property_real<T>::copy(char*dst, char*src)
{
      T*dst_obj = reinterpret_cast<T*> (dst+offset_);
      T*src_obj = reinterpret_cast<T*> (src+offset_);
      *dst_obj = *src_obj;
}

void property_string::set_string(char*buf, const string&val)
{
      string*tmp = reinterpret_cast<string*>(buf+offset_);
      *tmp = val;
}

string property_string::get_string(char*buf)
{
      const string*tmp = reinterpret_cast<string*>(buf+offset_);
      return *tmp;
}

void property_string::copy(char*dst, char*src)
{
      string*dst_obj = reinterpret_cast<string*> (dst+offset_);
      const string*src_obj = reinterpret_cast<string*> (src+offset_);
      *dst_obj = *src_obj;
}

// Support for parameterized class specialization: convert vec4 to string.
// The vec4 value contains packed ASCII characters (MSB is first char).
void property_string::set_vec4(char*buf, const vvp_vector4_t&val, uint64_t)
{
      string*tmp = reinterpret_cast<string*>(buf+offset_);

      // Convert vec4 to string - extract ASCII bytes from packed value
      size_t nbytes = (val.size() + 7) / 8;
      string result;
      result.reserve(nbytes);

      for (size_t idx = 0; idx < nbytes; idx++) {
	    // Extract each byte from the vec4 (MSB first like SystemVerilog strings)
	    size_t bit_base = (nbytes - 1 - idx) * 8;
	    unsigned char ch = 0;
	    for (int bit = 7; bit >= 0 && (bit_base + bit) < val.size(); bit--) {
		  vvp_bit4_t b = val.value(bit_base + bit);
		  if (b == BIT4_1) ch |= (1 << bit);
	    }
	    if (ch != 0) result.push_back(ch);
      }

      *tmp = result;
}

// Convert string to vec4 (for when code expects vec4 but property is string)
void property_string::get_vec4(char*buf, vvp_vector4_t&val, uint64_t)
{
      const string*tmp = reinterpret_cast<string*>(buf+offset_);

      // Convert string to vec4 - pack ASCII bytes into vec4
      size_t nbytes = tmp->size();
      size_t nbits = nbytes * 8;
      val = vvp_vector4_t(nbits > 0 ? nbits : 8, BIT4_0);

      for (size_t idx = 0; idx < nbytes; idx++) {
	    unsigned char ch = (*tmp)[idx];
	    size_t bit_base = (nbytes - 1 - idx) * 8;
	    for (int bit = 7; bit >= 0; bit--) {
		  val.set_bit(bit_base + bit, (ch & (1 << bit)) ? BIT4_1 : BIT4_0);
	    }
      }
}

void property_object::construct(char*buf) const
{
      for (size_t idx = 0 ; idx < array_size_ ; idx += 1)
	    new (buf+offset_ + idx*sizeof(vvp_object_t)) vvp_object_t;
}

void property_object::destruct(char*buf) const
{
      vvp_object_t*tmp = reinterpret_cast<vvp_object_t*> (buf+offset_);
      for (size_t idx = 0 ; idx < array_size_ ; idx += 1)
	    (tmp+idx)->~vvp_object_t();
}

void property_object::set_object(char*buf, const vvp_object_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      vvp_object_t*tmp = reinterpret_cast<vvp_object_t*>(buf+offset_);
      tmp[idx] = val;
}

void property_object::get_object(char*buf, vvp_object_t&val, uint64_t idx)
{
      assert(idx < array_size_);
      const vvp_object_t*tmp = reinterpret_cast<vvp_object_t*>(buf+offset_);
      val = tmp[idx];
}

void property_object::copy(char*dst, char*src)
{
      vvp_object_t*dst_obj = reinterpret_cast<vvp_object_t*>(dst+offset_);
      const vvp_object_t*src_obj = reinterpret_cast<vvp_object_t*>(src+offset_);
      for (size_t idx = 0 ; idx < array_size_ ; idx += 1)
	    dst_obj[idx] = src_obj[idx];
}

string property_object::get_string(char*)
{
      // Return a placeholder string for object properties (queues, darrays, etc.)
      // since they can't be meaningfully converted to a single string value.
      return "<object>";
}

/* **** */

class_type::class_type(const string&nam, size_t nprop)
: class_name_(nam), parent_(0), properties_(nprop)
{
      instance_size_ = 0;
}

bool class_type::is_derived_from(const class_type*target_class) const
{
      // Walk up the inheritance hierarchy looking for target_class
      const class_type*cur = this;
      while (cur) {
	    if (cur == target_class)
		  return true;
	    cur = cur->parent_;
      }
      return false;
}

class_type::~class_type()
{
      for (size_t idx = 0 ; idx < properties_.size() ; idx += 1)
	    delete properties_[idx].type;
}

void class_type::set_property(size_t idx, const string&name, const string&type, uint64_t array_size, int rand_flag)
{
      assert(idx < properties_.size());
      properties_[idx].name = name;
      properties_[idx].rand_flag = rand_flag;

      if (type == "b8")
	    properties_[idx].type = new property_atom<uint8_t>(array_size);
      else if (type == "b16")
	    properties_[idx].type = new property_atom<uint16_t>(array_size);
      else if (type == "b32")
	    properties_[idx].type = new property_atom<uint32_t>(array_size);
      else if (type == "b64")
	    properties_[idx].type = new property_atom<uint64_t>(array_size);
      else if (type == "sb8")
	    properties_[idx].type = new property_atom<int8_t>(array_size);
      else if (type == "sb16")
	    properties_[idx].type = new property_atom<int16_t>(array_size);
      else if (type == "sb32")
	    properties_[idx].type = new property_atom<int32_t>(array_size);
      else if (type == "sb64")
	    properties_[idx].type = new property_atom<int64_t>(array_size);
      else if (type == "r")
	    properties_[idx].type = new property_real<double>;
      else if (type == "S")
	    properties_[idx].type = new property_string;
      else if (type == "o")
	    properties_[idx].type = new property_object(array_size);
      else if (type[0] == 'b') {
	    size_t wid = strtoul(type.c_str()+1, 0, 0);
	    properties_[idx].type = new property_bit(wid, array_size);
      } else if (type[0] == 'L') {
	    size_t wid = strtoul(type.c_str()+1,0,0);
	    properties_[idx].type = new property_logic(wid, array_size);
      } else if (type[0] == 's' && type[1] == 'L') {
	    size_t wid = strtoul(type.c_str()+2,0,0);
	    properties_[idx].type = new property_logic(wid, array_size);
      } else {
	    properties_[idx].type = 0;
      }
}

void class_type::finish_setup(void)
{
      map<size_t, vector<size_t> > size_map;
	// Add up all the sizes to get a total instance size. This
	// figures out how much memory a complete instance will need.
      size_t accum = 0;
      for (size_t idx = 0 ; idx < properties_.size() ; idx += 1) {
	    assert(properties_[idx].type);
	    size_t instance_size = properties_[idx].type->instance_size();
	    accum += instance_size;
	    size_map[instance_size].push_back(idx);
      }

      instance_size_ = accum;

	// Now allocate the properties to offsets within an instance
	// space. Allocate the properties largest objects first so
	// that they are assured better alignment.
      accum = 0;
      for (map<size_t, vector<size_t> >::reverse_iterator cur = size_map.rbegin()
		 ; cur != size_map.rend() ; ++ cur) {
	    for (size_t idx = 0 ; idx < cur->second.size() ; idx += 1) {
		  size_t pid = cur->second[idx];
		  class_property_t*ptype = properties_[pid].type;
		  assert(ptype->instance_size() == cur->first);
		  ptype->set_offset(accum);
		  accum += cur->first;
	    }
      }
}

class_type::inst_t class_type::instance_new() const
{
      char*buf = new char [instance_size_];

      for (size_t idx = 0 ; idx < properties_.size() ; idx += 1)
	    properties_[idx].type->construct(buf);

      return reinterpret_cast<inst_t> (buf);
}

void class_type::instance_delete(class_type::inst_t obj) const
{
      char*buf = reinterpret_cast<char*> (obj);

      for (size_t idx = 0 ; idx < properties_.size() ; idx += 1)
	    properties_[idx].type->destruct(buf);

      delete[]buf;
}

void class_type::set_vec4(class_type::inst_t obj, size_t pid,
			  const vvp_vector4_t&val, uint64_t idx) const
{
      char*buf = reinterpret_cast<char*> (obj);
      if (pid >= properties_.size()) {
            fprintf(stderr, "ERROR class_type::set_vec4: pid=%lu >= properties_.size()=%lu, class=%s\n",
                    (unsigned long)pid, (unsigned long)properties_.size(), class_name_.c_str());
            return;
      }
      properties_[pid].type->set_vec4(buf, val, idx);
}

void class_type::get_vec4(class_type::inst_t obj, size_t pid,
			  vvp_vector4_t&val, uint64_t idx) const
{
      char*buf = reinterpret_cast<char*> (obj);
      if (pid >= properties_.size()) {
            fprintf(stderr, "ERROR class_type::get_vec4: pid=%lu >= properties_.size()=%lu, class=%s\n",
                    (unsigned long)pid, (unsigned long)properties_.size(), class_name_.c_str());
            val = vvp_vector4_t(0);
            return;
      }
      properties_[pid].type->get_vec4(buf, val, idx);
}

bool class_type::property_supports_vec4(size_t pid) const
{
      if (pid >= properties_.size())
	    return false;
      return properties_[pid].type->supports_vec4();
}

uint64_t class_type::property_array_size(size_t pid) const
{
      if (pid >= properties_.size())
	    return 1;
      return properties_[pid].type->array_size();
}

bool class_type::property_is_rand(size_t pid) const
{
      if (pid >= properties_.size())
	    return false;
      return properties_[pid].rand_flag != 0;  // 1=rand, 2=randc
}

bool class_type::property_is_randc(size_t pid) const
{
      if (pid >= properties_.size())
	    return false;
      return properties_[pid].rand_flag == 2;  // specifically randc
}

void class_type::add_constraint_bound(const simple_bound_t& bound)
{
      constraint_bounds_.push_back(bound);
}

const class_type::simple_bound_t& class_type::get_constraint_bound(size_t idx) const
{
      assert(idx < constraint_bounds_.size());
      return constraint_bounds_[idx];
}

int class_type::constraint_idx_from_name(const std::string& name) const
{
      // Constraint names are stored in constraint_bounds_, so we need to
      // find a unique constraint index from the name. Since bounds can share
      // the same constraint name, we return the first matching bound index.
      // For constraint_mode, we track unique names.
      for (size_t i = 0; i < constraint_bounds_.size(); ++i) {
	    if (constraint_bounds_[i].constraint_name == name)
		  return (int)i;
      }
      // Check parent class
      if (parent_) {
	    return parent_->constraint_idx_from_name(name);
      }
      return -1;
}

/*
 * Generate a constrained random value for a property.
 * Computes the valid range from all constraint bounds and generates
 * a random value within that range.
 */
int64_t class_type::generate_constrained_random(inst_t inst, size_t prop_idx, unsigned wid, const vvp_cobject* cobj, const std::vector<simple_bound_t>& inline_constraints) const
{
      // Check if this property has enum bounds - if so, pick from valid enum values
      const std::vector<int64_t>* enum_vals = get_enum_values(prop_idx);
      if (enum_vals != nullptr && !enum_vals->empty()) {
	    // Pick a random valid enum value
	    size_t idx = rand() % enum_vals->size();
	    return (*enum_vals)[idx];
      }

      // Check for "inside array" constraint - pick value from array property
      // This handles patterns like: x inside {arr} where arr is a dynamic array property
      for (const auto& bound : inline_constraints) {
	    if (bound.property_idx == prop_idx && bound.is_inside_array) {
		  // Get the array from the inside_array_prop_idx property
		  size_t arr_prop_idx = bound.inside_array_prop_idx;
		  if (arr_prop_idx < properties_.size()) {
			// Try to get the property as an object and see if it's a dynamic array
			vvp_object_t obj;
			get_object(inst, arr_prop_idx, obj, 0);
			vvp_darray* darray_ptr = obj.peek<vvp_darray>();
			if (darray_ptr && darray_ptr->get_size() > 0) {
			      // Pick a random element from the array
			      size_t arr_size = darray_ptr->get_size();
			      size_t idx = rand() % arr_size;
			      vvp_vector4_t elem_val;
			      darray_ptr->get_word(idx, elem_val);
			      // Convert to int64_t
			      int64_t result = 0;
			      for (unsigned i = 0; i < elem_val.size() && i < 64; i++) {
				    if (elem_val.value(i) == BIT4_1)
					  result |= (int64_t(1) << i);
			      }
			      return result;
			}
		  }
	    }
      }

      // Compute the type-based min/max based on width and signedness
      int64_t type_min = 0;
      int64_t type_max = (1LL << wid) - 1;

      // Check if property is signed using the type info
      bool is_signed_type = false;
      if (prop_idx < properties_.size() && properties_[prop_idx].type) {
	    is_signed_type = properties_[prop_idx].type->is_signed();
      }

      if (is_signed_type) {
	    // For signed types, min is negative
	    if (wid < 64) {
		  type_min = -(1LL << (wid - 1));
		  type_max = (1LL << (wid - 1)) - 1;
	    } else {
		  type_min = INT64_MIN;
		  type_max = INT64_MAX;
	    }
      } else {
	    // For unsigned types
	    if (wid > 63) type_max = INT64_MAX;
      }

      // Start with full range
      int64_t min_val = type_min;
      int64_t max_val = type_max;

      // Check for system function constraints on this property that we need
      // to handle specially (e.g., $countones(x) == 1 requires one-hot value)
      bool need_onehot = false;  // Generate one-hot value (exactly one bit set)
      bool need_onehot0 = false; // Generate zero or one-hot value
      int required_ones = -1;    // For $countones(x) == N

      for (const auto& bound : constraint_bounds_) {
	    // Skip disabled constraints (via constraint_mode)
	    if (cobj != nullptr && !bound.constraint_name.empty() &&
	        !cobj->is_constraint_enabled(bound.constraint_name))
		  continue;
	    // Only care about sysfunc constraints on this property
	    if (bound.sysfunc_type == SYSFUNC_NONE)
		  continue;
	    if (bound.sysfunc_arg_idx != prop_idx)
		  continue;
	    if (bound.is_soft)
		  continue;  // Skip soft constraints for value generation

	    // Check if this is a conditional constraint
	    if (bound.has_condition) {
		  // Evaluate the condition to see if this constraint applies
		  if (bound.cond_prop_idx >= properties_.size())
			continue;
		  if (!properties_[bound.cond_prop_idx].type->supports_vec4())
			continue;

		  // First check if inline constraints set the condition property to a specific value
		  // This handles cases like: randomize() with { burst == BURST4; }
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
			get_vec4(inst, bound.cond_prop_idx, cond_prop_val);

			if (cond_prop_val.size() <= 64) {
			      for (unsigned i = 0; i < cond_prop_val.size(); i++) {
				    if (cond_prop_val.value(i) == BIT4_1)
					  cond_val |= (int64_t(1) << i);
			      }
			}
		  }

		  // Get the condition bound value
		  int64_t cond_bound_val = 0;
		  if (bound.cond_has_const) {
			cond_bound_val = bound.cond_const;
		  } else if (bound.cond_prop2_idx < properties_.size() &&
		             properties_[bound.cond_prop2_idx].type->supports_vec4()) {
			vvp_vector4_t cond_prop2_val;
			get_vec4(inst, bound.cond_prop2_idx, cond_prop2_val);
			if (cond_prop2_val.size() <= 64) {
			      for (unsigned i = 0; i < cond_prop2_val.size(); i++) {
				    if (cond_prop2_val.value(i) == BIT4_1)
					  cond_bound_val |= (int64_t(1) << i);
			      }
			}
		  }

		  // Evaluate the condition
		  bool cond_satisfied = false;
		  switch (bound.cond_op) {
			case '>': cond_satisfied = (cond_val > cond_bound_val); break;
			case '<': cond_satisfied = (cond_val < cond_bound_val); break;
			case 'G': cond_satisfied = (cond_val >= cond_bound_val); break;
			case 'L': cond_satisfied = (cond_val <= cond_bound_val); break;
			case '=': cond_satisfied = (cond_val == cond_bound_val); break;
			case '!': cond_satisfied = (cond_val != cond_bound_val); break;
			default: cond_satisfied = true; break;
		  }

		  // If condition is false, skip this constraint
		  if (!cond_satisfied)
			continue;
	    }

	    // Handle system function constraints
	    if (bound.sysfunc_type == SYSFUNC_COUNTONES && bound.op == '=' &&
		bound.has_const_bound) {
		  required_ones = static_cast<int>(bound.const_bound);
		  if (required_ones == 1) need_onehot = true;
	    } else if (bound.sysfunc_type == SYSFUNC_ONEHOT && bound.op == '=' &&
		       bound.has_const_bound && bound.const_bound == 1) {
		  need_onehot = true;
	    } else if (bound.sysfunc_type == SYSFUNC_ONEHOT0 && bound.op == '=' &&
		       bound.has_const_bound && bound.const_bound == 1) {
		  need_onehot0 = true;
	    }
      }

      // First, check for weighted discrete values and ranges (from dist constraints)
      // Collect discrete values with weights, and range bounds with weights
      struct weighted_value_t {
	    int64_t value;
	    int64_t weight;
      };
      struct weighted_range_t {
	    int64_t low;
	    int64_t high;
	    int64_t weight;
	    bool weight_per_value;  // := means weight per value, :/ means weight per range
      };
      std::vector<weighted_value_t> weighted_values;
      std::vector<weighted_range_t> weighted_ranges;
      int64_t total_weight = 0;

      // First pass: collect >= bounds with weights (lower bounds of ranges)
      std::map<int64_t, std::pair<int64_t, bool>> lower_bounds;  // weight -> (value, weight_per_value)
      std::map<int64_t, std::pair<int64_t, bool>> upper_bounds;  // weight -> (value, weight_per_value)

      for (const auto& bound : constraint_bounds_) {
	    // Skip disabled constraints (via constraint_mode)
	    if (cobj != nullptr && !bound.constraint_name.empty() &&
	        !cobj->is_constraint_enabled(bound.constraint_name))
		  continue;
	    if (bound.property_idx != prop_idx)
		  continue;
	    if (bound.sysfunc_type != SYSFUNC_NONE)
		  continue;
	    if (bound.is_soft)
		  continue;
	    if (!bound.has_const_bound)
		  continue;
	    if (bound.weight <= 0)
		  continue;

	    // Skip conditional constraints for now in dist handling
	    if (bound.has_condition)
		  continue;

	    if (bound.op == '=') {
		  // Discrete value
		  weighted_value_t wv;
		  wv.value = bound.const_bound;
		  wv.weight = bound.weight;
		  weighted_values.push_back(wv);
	    } else if (bound.op == 'G') {
		  // >= bound (lower bound of range)
		  lower_bounds[bound.weight] = std::make_pair(bound.const_bound, bound.weight_per_value);
	    } else if (bound.op == 'L') {
		  // <= bound (upper bound of range)
		  upper_bounds[bound.weight] = std::make_pair(bound.const_bound, bound.weight_per_value);
	    }
      }

      // Pair up lower and upper bounds with matching weights to form ranges
      for (const auto& lb : lower_bounds) {
	    int64_t weight = lb.first;
	    auto ub_it = upper_bounds.find(weight);
	    if (ub_it != upper_bounds.end()) {
		  weighted_range_t wr;
		  wr.low = lb.second.first;
		  wr.high = ub_it->second.first;
		  wr.weight = weight;
		  wr.weight_per_value = lb.second.second;
		  if (wr.low <= wr.high) {  // Valid range
			weighted_ranges.push_back(wr);
		  }
	    }
      }

      // Calculate total weight from discrete values and ranges
      for (const auto& wv : weighted_values) {
	    total_weight += wv.weight;
      }
      for (const auto& wr : weighted_ranges) {
	    if (wr.weight_per_value) {
		  // := means weight per value, so total weight = weight * range_size
		  total_weight += wr.weight * (wr.high - wr.low + 1);
	    } else {
		  // :/ means weight per range
		  total_weight += wr.weight;
	    }
      }

      // If we have weighted values or ranges, do weighted random selection
      size_t total_items = weighted_values.size() + weighted_ranges.size();
      if (total_items > 1 && total_weight > 0) {
	    int64_t r = rand() % total_weight;
	    int64_t cumulative = 0;

	    // Check discrete values first
	    for (const auto& wv : weighted_values) {
		  cumulative += wv.weight;
		  if (r < cumulative)
			return wv.value;
	    }

	    // Then check ranges
	    for (const auto& wr : weighted_ranges) {
		  int64_t range_weight;
		  if (wr.weight_per_value) {
			range_weight = wr.weight * (wr.high - wr.low + 1);
		  } else {
			range_weight = wr.weight;
		  }
		  cumulative += range_weight;
		  if (r < cumulative) {
			// Generate random value within this range
			int64_t range_size = wr.high - wr.low + 1;
			return wr.low + (rand() % range_size);
		  }
	    }

	    // Fallback to last item
	    if (!weighted_ranges.empty()) {
		  const auto& wr = weighted_ranges.back();
		  int64_t range_size = wr.high - wr.low + 1;
		  return wr.low + (rand() % range_size);
	    }
	    return weighted_values.back().value;
      }

      // Handle single value or single range with weight
      if (weighted_values.size() == 1 && weighted_ranges.empty()) {
	    return weighted_values[0].value;
      }
      if (weighted_ranges.size() == 1 && weighted_values.empty()) {
	    const auto& wr = weighted_ranges[0];
	    int64_t range_size = wr.high - wr.low + 1;
	    return wr.low + (rand() % range_size);
      }

      // Now collect range constraints for this property
      // Apply all constraint bounds for this property
      for (const auto& bound : constraint_bounds_) {
	    // Skip disabled constraints (via constraint_mode)
	    if (cobj != nullptr && !bound.constraint_name.empty() &&
	        !cobj->is_constraint_enabled(bound.constraint_name))
		  continue;
	    if (bound.property_idx != prop_idx)
		  continue;
	    // Skip system function constraints (handled above)
	    if (bound.sysfunc_type != SYSFUNC_NONE)
		  continue;
	    // Skip weighted constraints (already handled above)
	    if (bound.weight > 1 || (bound.op == '=' && bound.weight > 0))
		  continue;

	    // For implication constraints, check the condition first
	    // If condition is false, skip this bound
	    if (bound.has_condition) {
		  if (bound.cond_prop_idx >= properties_.size())
			continue;
		  if (!properties_[bound.cond_prop_idx].type->supports_vec4())
			continue;

		  vvp_vector4_t cond_prop_val;
		  get_vec4(inst, bound.cond_prop_idx, cond_prop_val);

		  int64_t cond_val = 0;
		  if (cond_prop_val.size() <= 64) {
			for (unsigned i = 0; i < cond_prop_val.size(); i++) {
			      if (cond_prop_val.value(i) == BIT4_1)
				    cond_val |= (int64_t(1) << i);
			}
		  }

		  int64_t cond_bound_val = bound.cond_has_const ? bound.cond_const : 0;
		  if (!bound.cond_has_const && bound.cond_prop2_idx < properties_.size() &&
		      properties_[bound.cond_prop2_idx].type->supports_vec4()) {
			vvp_vector4_t cond_prop2_val;
			get_vec4(inst, bound.cond_prop2_idx, cond_prop2_val);
			if (cond_prop2_val.size() <= 64) {
			      for (unsigned i = 0; i < cond_prop2_val.size(); i++) {
				    if (cond_prop2_val.value(i) == BIT4_1)
					  cond_bound_val |= (int64_t(1) << i);
			      }
			}
		  }

		  // Evaluate the condition
		  bool cond_satisfied = false;
		  switch (bound.cond_op) {
			case '>': cond_satisfied = (cond_val > cond_bound_val); break;
			case '<': cond_satisfied = (cond_val < cond_bound_val); break;
			case 'G': cond_satisfied = (cond_val >= cond_bound_val); break;
			case 'L': cond_satisfied = (cond_val <= cond_bound_val); break;
			case '=': cond_satisfied = (cond_val == cond_bound_val); break;
			case '!': cond_satisfied = (cond_val != cond_bound_val); break;
			default: cond_satisfied = true; break;
		  }

		  if (!cond_satisfied)
			continue;
	    }

	    // Get the bound value
	    int64_t bval = 0;
	    if (bound.has_prop_offset && bound.bound_prop_idx < properties_.size()) {
		  // Property + offset bound (e.g., y <= x + 10)
		  // bound.bound_prop_idx references another property, const_bound is the offset
		  if (!properties_[bound.bound_prop_idx].type->supports_vec4())
			continue;
		  vvp_vector4_t prop_val;
		  get_vec4(inst, bound.bound_prop_idx, prop_val);
		  if (prop_val.size() <= 64) {
			for (unsigned i = 0; i < prop_val.size(); i++) {
			      if (prop_val.value(i) == BIT4_1)
				    bval |= (int64_t(1) << i);
			}
			// Handle signed values - ONLY sign-extend if property is signed
			bool is_signed_prop = properties_[bound.bound_prop_idx].type->is_signed();
			if (is_signed_prop && prop_val.size() < 64 && prop_val.size() > 0 &&
			    prop_val.value(prop_val.size()-1) == BIT4_1) {
			      for (unsigned i = prop_val.size(); i < 64; i++)
				    bval |= (int64_t(1) << i);
			}
		  }
		  // Add the constant offset
		  bval += bound.const_bound;
	    } else if (bound.has_const_bound) {
		  bval = bound.const_bound;
	    } else if (bound.bound_prop_idx < properties_.size()) {
		  // Get value from another property (no offset)
		  if (!properties_[bound.bound_prop_idx].type->supports_vec4())
			continue;
		  vvp_vector4_t prop_val;
		  get_vec4(inst, bound.bound_prop_idx, prop_val);
		  if (prop_val.size() <= 64) {
			for (unsigned i = 0; i < prop_val.size(); i++) {
			      if (prop_val.value(i) == BIT4_1)
				    bval |= (int64_t(1) << i);
			}
			// Handle signed values - ONLY sign-extend if property is signed
			bool is_signed_prop = properties_[bound.bound_prop_idx].type->is_signed();
			if (is_signed_prop && prop_val.size() < 64 && prop_val.size() > 0 &&
			    prop_val.value(prop_val.size()-1) == BIT4_1) {
			      for (unsigned i = prop_val.size(); i < 64; i++)
				    bval |= (int64_t(1) << i);
			}
		  }
	    } else {
		  continue;
	    }

	    // Apply bound based on operator
	    switch (bound.op) {
		  case '>':  // val > bval => min = bval + 1
		      if (bval + 1 > min_val) min_val = bval + 1;
		      break;
		  case 'G':  // val >= bval => min = bval
		      if (bval > min_val) min_val = bval;
		      break;
		  case '<':  // val < bval => max = bval - 1
		      if (bval - 1 < max_val) max_val = bval - 1;
		      break;
		  case 'L':  // val <= bval => max = bval
		      if (bval < max_val) max_val = bval;
		      break;
		  case '=':  // val == bval => both min and max = bval
		      min_val = max_val = bval;
		      break;
		  // '!' (!=) can't be easily range-bounded, skip for now
	    }
      }

      // Collect excluded ranges for this property (from !(x inside {[lo:hi]}))
      std::vector<std::pair<int64_t, int64_t>> excluded_ranges;
      for (const auto& bound : constraint_bounds_) {
	    // Skip disabled constraints
	    if (cobj != nullptr && !bound.constraint_name.empty() &&
	        !cobj->is_constraint_enabled(bound.constraint_name))
		  continue;
	    if (bound.property_idx != prop_idx)
		  continue;
	    if (!bound.is_excluded_range)
		  continue;
	    if (bound.is_soft)
		  continue;
	    excluded_ranges.push_back(std::make_pair(bound.excluded_range_low,
						     bound.excluded_range_high));
      }

      // Also check inline constraints for excluded ranges
      for (const auto& bound : inline_constraints) {
	    if (bound.property_idx != prop_idx)
		  continue;
	    if (!bound.is_excluded_range)
		  continue;
	    if (bound.is_soft)
		  continue;
	    excluded_ranges.push_back(std::make_pair(bound.excluded_range_low,
						     bound.excluded_range_high));
      }

      // Helper lambda to check if a value is in any excluded range
      auto is_in_excluded_range = [&](int64_t val) -> bool {
	    for (const auto& range : excluded_ranges) {
		  if (val >= range.first && val <= range.second)
			return true;
	    }
	    return false;
      };

      // Now handle special value generation (like one-hot) WITH range constraints
      if (need_onehot) {
	    // Generate a random power of 2 (exactly one bit set)
	    // But respect the range constraints [min_val, max_val]
	    // Find which bit positions produce values in range
	    std::vector<unsigned> valid_positions;
	    for (unsigned i = 0; i < wid; i++) {
		  int64_t val = int64_t(1) << i;
		  if (val >= min_val && val <= max_val)
			valid_positions.push_back(i);
	    }
	    if (!valid_positions.empty()) {
		  unsigned idx = rand() % valid_positions.size();
		  return int64_t(1) << valid_positions[idx];
	    }
	    // No valid one-hot value in range - fall through to normal generation
      }

      if (need_onehot0) {
	    // Generate 0 or a random power of 2, respecting range
	    std::vector<int64_t> valid_values;
	    if (0 >= min_val && 0 <= max_val)
		  valid_values.push_back(0);
	    for (unsigned i = 0; i < wid; i++) {
		  int64_t val = int64_t(1) << i;
		  if (val >= min_val && val <= max_val)
			valid_values.push_back(val);
	    }
	    if (!valid_values.empty()) {
		  unsigned idx = rand() % valid_values.size();
		  return valid_values[idx];
	    }
	    // No valid value in range - fall through
      }

      if (required_ones >= 0 && required_ones <= (int)wid) {
	    // Generate a value with exactly required_ones bits set
	    // This is harder to combine with range constraints
	    // For now, generate and retry up to 100 times
	    for (int attempt = 0; attempt < 100; attempt++) {
		  int64_t result = 0;
		  std::vector<unsigned> positions;
		  for (unsigned i = 0; i < wid; i++)
			positions.push_back(i);
		  // Shuffle positions
		  for (unsigned i = wid - 1; i > 0; i--) {
			unsigned j = rand() % (i + 1);
			std::swap(positions[i], positions[j]);
		  }
		  // Set required_ones bits
		  for (int i = 0; i < required_ones && i < (int)positions.size(); i++) {
			result |= (int64_t(1) << positions[i]);
		  }
		  // Check if result is in range
		  if (result >= min_val && result <= max_val)
			return result;
	    }
	    // Couldn't find valid value - fall through to normal generation
      }

      // Generate random value in [min_val, max_val]
      if (min_val > max_val) {
	    // Impossible constraint - return a random value and let check fail
	    int64_t r = 0;
	    for (unsigned i = 0; i < wid && i < 64; i++) {
		  if (rand() & 1) r |= (int64_t(1) << i);
	    }
	    return r;
      }

      // Generate random value in range, avoiding excluded ranges
      int64_t range = max_val - min_val + 1;
      if (range <= 0) {
	    // Overflow or single value
	    return min_val;
      }

      // If we have excluded ranges, we need to retry to find a valid value
      int max_attempts = excluded_ranges.empty() ? 1 : 1000;
      for (int attempt = 0; attempt < max_attempts; attempt++) {
	    // Use modulo for range (not perfectly uniform but good enough)
	    int64_t r = 0;
	    for (unsigned i = 0; i < 64; i++) {
		  if (rand() & 1) r |= (int64_t(1) << i);
	    }
	    // Make sure r is non-negative for modulo
	    if (r < 0) r = -r;

	    int64_t result = min_val + (r % range);

	    // Check if result is in an excluded range
	    if (!is_in_excluded_range(result))
		  return result;
      }

      // Fallback: couldn't find a value outside excluded ranges
      // Return a value that's at least in the valid range
      return min_val + (rand() % range);
}

bool class_type::has_any_constraints() const
{
      // Check if this class or any parent has constraints
      if (!constraint_bounds_.empty())
	    return true;
      if (parent_ != nullptr)
	    return parent_->has_any_constraints();
      return false;
}

bool class_type::check_constraints(inst_t inst, const vvp_cobject* cobj) const
{
      // Collect all constraint bounds from this class and all parent classes
      // We collect them and check using THIS class's property accessors
      // because property indices match between parent and derived classes
      // (derived copies parent properties at the same indices)
      std::vector<simple_bound_t> all_bounds;
      const class_type* cls = this;
      while (cls != nullptr) {
	    for (const auto& bound : cls->constraint_bounds_) {
		  // Skip disabled constraints (via constraint_mode)
		  if (cobj != nullptr && !bound.constraint_name.empty() &&
		      !cobj->is_constraint_enabled(bound.constraint_name))
			continue;
		  all_bounds.push_back(bound);
	    }
	    cls = cls->parent_;
      }

      if (all_bounds.empty())
	    return true;

      // First, handle weighted constraints (from dist)
      // Group discrete values and ranges by property index, check with OR logic

      // Structure to hold ranges (paired >= and <= bounds)
      struct range_t { int64_t low; int64_t high; };

      // Collect discrete values and ranges for each property
      std::map<size_t, std::vector<int64_t>> weighted_eq_values;
      std::map<size_t, std::map<int64_t, int64_t>> lower_bounds_by_prop;  // prop -> weight -> low
      std::map<size_t, std::map<int64_t, int64_t>> upper_bounds_by_prop;  // prop -> weight -> high
      std::map<size_t, std::vector<range_t>> weighted_ranges;

      for (const auto& bound : all_bounds) {
	    if (!bound.has_const_bound || bound.weight <= 0 || bound.is_soft ||
		bound.sysfunc_type != SYSFUNC_NONE)
		  continue;

	    if (bound.op == '=') {
		  weighted_eq_values[bound.property_idx].push_back(bound.const_bound);
	    } else if (bound.op == 'G') {
		  lower_bounds_by_prop[bound.property_idx][bound.weight] = bound.const_bound;
	    } else if (bound.op == 'L') {
		  upper_bounds_by_prop[bound.property_idx][bound.weight] = bound.const_bound;
	    }
      }

      // Pair up lower and upper bounds to form ranges
      for (const auto& lb_entry : lower_bounds_by_prop) {
	    size_t prop_idx = lb_entry.first;
	    auto ub_it = upper_bounds_by_prop.find(prop_idx);
	    if (ub_it == upper_bounds_by_prop.end()) continue;

	    for (const auto& lb : lb_entry.second) {
		  int64_t weight = lb.first;
		  auto ub = ub_it->second.find(weight);
		  if (ub != ub_it->second.end()) {
			range_t r;
			r.low = lb.second;
			r.high = ub->second;
			if (r.low <= r.high)
			      weighted_ranges[prop_idx].push_back(r);
		  }
	    }
      }

      // Check properties with weighted constraints (discrete values or ranges)
      for (const auto& entry : weighted_eq_values) {
	    size_t prop_idx = entry.first;
	    auto ranges_it = weighted_ranges.find(prop_idx);
	    bool has_ranges = (ranges_it != weighted_ranges.end() && !ranges_it->second.empty());

	    // If only one value and no ranges, skip (handled normally)
	    if (entry.second.size() <= 1 && !has_ranges)
		  continue;

	    if (prop_idx >= properties_.size())
		  continue;
	    if (!properties_[prop_idx].type->supports_vec4())
		  continue;

	    vvp_vector4_t prop_val;
	    get_vec4(inst, prop_idx, prop_val);

	    int64_t val = 0;
	    if (prop_val.size() <= 64) {
		  for (unsigned i = 0; i < prop_val.size(); i++) {
			if (prop_val.value(i) == BIT4_1)
			      val |= (int64_t(1) << i);
		  }
	    }

	    // Check if value matches ANY discrete value or is in ANY range
	    bool matches_any = false;
	    for (int64_t allowed : entry.second) {
		  if (val == allowed) {
			matches_any = true;
			break;
		  }
	    }
	    if (!matches_any && has_ranges) {
		  for (const auto& r : ranges_it->second) {
			if (val >= r.low && val <= r.high) {
			      matches_any = true;
			      break;
			}
		  }
	    }

	    if (!matches_any) {
		  return false;
	    }
      }

      // Also check properties that have ranges but no discrete values
      for (const auto& entry : weighted_ranges) {
	    size_t prop_idx = entry.first;
	    if (weighted_eq_values.find(prop_idx) != weighted_eq_values.end())
		  continue;  // Already handled above
	    if (entry.second.size() <= 1)
		  continue;  // Single range, handled normally

	    if (prop_idx >= properties_.size())
		  continue;
	    if (!properties_[prop_idx].type->supports_vec4())
		  continue;

	    vvp_vector4_t prop_val;
	    get_vec4(inst, prop_idx, prop_val);

	    int64_t val = 0;
	    if (prop_val.size() <= 64) {
		  for (unsigned i = 0; i < prop_val.size(); i++) {
			if (prop_val.value(i) == BIT4_1)
			      val |= (int64_t(1) << i);
		  }
	    }

	    bool matches_any = false;
	    for (const auto& r : entry.second) {
		  if (val >= r.low && val <= r.high) {
			matches_any = true;
			break;
		  }
	    }

	    if (!matches_any) {
		  return false;
	    }
      }

      for (const auto& bound : all_bounds) {
	    // Skip weighted equality constraints we already handled above
	    // We need to skip if either:
	    // 1. There are multiple discrete values for this property, OR
	    // 2. There are ranges for this property (discrete value + range uses OR logic)
	    if (bound.op == '=' && bound.has_const_bound && bound.weight > 0 &&
		!bound.is_soft && bound.sysfunc_type == SYSFUNC_NONE) {
		  auto it = weighted_eq_values.find(bound.property_idx);
		  auto range_it = weighted_ranges.find(bound.property_idx);
		  bool has_multiple_values = (it != weighted_eq_values.end() && it->second.size() > 1);
		  bool has_ranges = (range_it != weighted_ranges.end() && !range_it->second.empty());
		  if (has_multiple_values || has_ranges)
			continue;  // Already checked with OR logic
	    }
	    // Skip weighted range bounds we already handled above
	    if ((bound.op == 'G' || bound.op == 'L') && bound.has_const_bound &&
		bound.weight > 0 && !bound.is_soft && bound.sysfunc_type == SYSFUNC_NONE) {
		  auto it = weighted_ranges.find(bound.property_idx);
		  if (it != weighted_ranges.end() && it->second.size() > 0)
			continue;  // Part of a weighted range, already checked
	    }
	    // Get the value of the constrained property
	    // Use THIS class's property accessors (not parent's)
	    if (bound.property_idx >= properties_.size())
		  continue;

	    if (!properties_[bound.property_idx].type->supports_vec4())
		  continue;

	    // For implication constraints, check the condition first
	    // If condition is false, skip this bound (it doesn't apply)
	    if (bound.has_condition) {
		  if (bound.cond_prop_idx >= properties_.size())
			continue;
		  if (!properties_[bound.cond_prop_idx].type->supports_vec4())
			continue;

		  vvp_vector4_t cond_prop_val;
		  get_vec4(inst, bound.cond_prop_idx, cond_prop_val);

		  int64_t cond_val = 0;
		  if (cond_prop_val.size() <= 64) {
			for (unsigned i = 0; i < cond_prop_val.size(); i++) {
			      if (cond_prop_val.value(i) == BIT4_1)
				    cond_val |= (int64_t(1) << i);
			}
		  }

		  // Get the condition bound value
		  int64_t cond_bound_val = 0;
		  if (bound.cond_has_const) {
			cond_bound_val = bound.cond_const;
		  } else if (bound.cond_prop2_idx < properties_.size() &&
		             properties_[bound.cond_prop2_idx].type->supports_vec4()) {
			vvp_vector4_t cond_prop2_val;
			get_vec4(inst, bound.cond_prop2_idx, cond_prop2_val);
			if (cond_prop2_val.size() <= 64) {
			      for (unsigned i = 0; i < cond_prop2_val.size(); i++) {
				    if (cond_prop2_val.value(i) == BIT4_1)
					  cond_bound_val |= (int64_t(1) << i);
			      }
			}
		  }

		  // Evaluate the condition
		  bool cond_satisfied = false;
		  switch (bound.cond_op) {
			case '>': cond_satisfied = (cond_val > cond_bound_val); break;
			case '<': cond_satisfied = (cond_val < cond_bound_val); break;
			case 'G': cond_satisfied = (cond_val >= cond_bound_val); break;
			case 'L': cond_satisfied = (cond_val <= cond_bound_val); break;
			case '=': cond_satisfied = (cond_val == cond_bound_val); break;
			case '!': cond_satisfied = (cond_val != cond_bound_val); break;
			default: cond_satisfied = true; break;
		  }

		  // If condition is false, skip this bound
		  if (!cond_satisfied)
			continue;
	    }

	    vvp_vector4_t prop_val;
	    get_vec4(inst, bound.property_idx, prop_val);

	    // Convert to int64_t for comparison
	    // Note: X/Z bits are treated as 0 for constraint checking
	    int64_t val = 0;
	    if (prop_val.size() <= 64) {
		  for (unsigned i = 0; i < prop_val.size(); i++) {
			if (prop_val.value(i) == BIT4_1)
			      val |= (int64_t(1) << i);
		  }
		  // Handle signed values - ONLY sign-extend if property is signed
		  bool is_signed_prop = properties_[bound.property_idx].type->is_signed();
		  if (is_signed_prop && prop_val.size() < 64 && prop_val.size() > 0 &&
		      prop_val.value(prop_val.size()-1) == BIT4_1) {
			// Sign extend
			for (unsigned i = prop_val.size(); i < 64; i++)
			      val |= (int64_t(1) << i);
		  }
	    }

	    // Get the bound value (constant, property, or property + offset)
	    int64_t bound_val = 0;
	    if (bound.has_prop_offset && bound.bound_prop_idx < properties_.size()) {
		  // Property + offset bound (e.g., y <= x + 10)
		  // bound.bound_prop_idx references another property, const_bound is the offset
		  if (!properties_[bound.bound_prop_idx].type->supports_vec4())
			continue;
		  vvp_vector4_t bound_prop_val;
		  get_vec4(inst, bound.bound_prop_idx, bound_prop_val);
		  if (bound_prop_val.size() <= 64) {
			for (unsigned i = 0; i < bound_prop_val.size(); i++) {
			      if (bound_prop_val.value(i) == BIT4_1)
				    bound_val |= (int64_t(1) << i);
			}
			// Handle signed values - ONLY sign-extend if property is signed
			bool is_signed_bound = properties_[bound.bound_prop_idx].type->is_signed();
			if (is_signed_bound && bound_prop_val.size() < 64 && bound_prop_val.size() > 0 &&
			    bound_prop_val.value(bound_prop_val.size()-1) == BIT4_1) {
			      for (unsigned i = bound_prop_val.size(); i < 64; i++)
				    bound_val |= (int64_t(1) << i);
			}
		  }
		  // Add the constant offset
		  bound_val += bound.const_bound;
	    } else if (bound.has_const_bound) {
		  bound_val = bound.const_bound;
	    } else if (bound.bound_prop_idx < properties_.size()) {
		  // Property reference only (no offset)
		  if (!properties_[bound.bound_prop_idx].type->supports_vec4())
			continue;
		  vvp_vector4_t bound_prop_val;
		  get_vec4(inst, bound.bound_prop_idx, bound_prop_val);
		  if (bound_prop_val.size() <= 64) {
			for (unsigned i = 0; i < bound_prop_val.size(); i++) {
			      if (bound_prop_val.value(i) == BIT4_1)
				    bound_val |= (int64_t(1) << i);
			}
			// Handle signed values - ONLY sign-extend if property is signed
			bool is_signed_bound = properties_[bound.bound_prop_idx].type->is_signed();
			if (is_signed_bound && bound_prop_val.size() < 64 && bound_prop_val.size() > 0 &&
			    bound_prop_val.value(bound_prop_val.size()-1) == BIT4_1) {
			      for (unsigned i = bound_prop_val.size(); i < 64; i++)
				    bound_val |= (int64_t(1) << i);
			}
		  }
	    } else {
		  continue;
	    }

	    // For system function constraints, we need to evaluate the function
	    // on the argument property and compare the result to bound_val.
	    // For non-sysfunc constraints, val is the property value to compare.
	    int64_t compare_val = val;
	    if (bound.sysfunc_type != SYSFUNC_NONE) {
		  // Get the value of the system function argument property
		  if (bound.sysfunc_arg_idx >= properties_.size())
			continue;
		  if (!properties_[bound.sysfunc_arg_idx].type->supports_vec4())
			continue;

		  vvp_vector4_t arg_val;
		  get_vec4(inst, bound.sysfunc_arg_idx, arg_val);

		  int64_t arg = 0;
		  bool has_xz = false;
		  if (arg_val.size() <= 64) {
			for (unsigned i = 0; i < arg_val.size(); i++) {
			      vvp_bit4_t bit = arg_val.value(i);
			      if (bit == BIT4_1)
				    arg |= (int64_t(1) << i);
			      else if (bit == BIT4_X || bit == BIT4_Z)
				    has_xz = true;
			}
		  }

		  // Evaluate the system function
		  switch (bound.sysfunc_type) {
			case SYSFUNC_COUNTONES:
			      compare_val = count_ones(arg);
			      break;
			case SYSFUNC_ONEHOT:
			      // $onehot: exactly one bit set and no X/Z
			      compare_val = (!has_xz && count_ones(arg) == 1) ? 1 : 0;
			      break;
			case SYSFUNC_ONEHOT0:
			      // $onehot0: at most one bit set and no X/Z
			      compare_val = (!has_xz && count_ones(arg) <= 1) ? 1 : 0;
			      break;
			case SYSFUNC_ISUNKNOWN:
			      // $isunknown: true if any X/Z bits
			      compare_val = has_xz ? 1 : 0;
			      break;
			case SYSFUNC_CLOG2:
			      compare_val = clog2(arg);
			      break;
			default:
			      continue;  // Unknown sysfunc, skip
		  }
	    }

	    // Check the constraint based on operator
	    bool satisfied = false;
	    switch (bound.op) {
		  case '>': satisfied = (compare_val > bound_val); break;
		  case '<': satisfied = (compare_val < bound_val); break;
		  case 'G': satisfied = (compare_val >= bound_val); break;  // >=
		  case 'L': satisfied = (compare_val <= bound_val); break;  // <=
		  case '=': satisfied = (compare_val == bound_val); break;  // ==
		  case '!': satisfied = (compare_val != bound_val); break;  // !=
		  default: satisfied = true; break;
	    }

	    if (!satisfied && !bound.is_soft) {
		  // Hard constraint violated
		  return false;
	    }

	    // Check excluded ranges (from !(x inside {[lo:hi]}))
	    if (bound.is_excluded_range && !bound.is_soft) {
		  // Value must NOT be in the excluded range
		  if (val >= bound.excluded_range_low && val <= bound.excluded_range_high) {
			return false;
		  }
	    }
      }

      return true;
}

void class_type::set_real(class_type::inst_t obj, size_t pid,
			  double val) const
{
      char*buf = reinterpret_cast<char*> (obj);
      assert(pid < properties_.size());
      properties_[pid].type->set_real(buf, val);
}

double class_type::get_real(class_type::inst_t obj, size_t pid) const
{
      char*buf = reinterpret_cast<char*> (obj);
      assert(pid < properties_.size());
      return properties_[pid].type->get_real(buf);
}

void class_type::set_string(class_type::inst_t obj, size_t pid,
			    const string&val) const
{
      char*buf = reinterpret_cast<char*> (obj);
      assert(pid < properties_.size());
      properties_[pid].type->set_string(buf, val);
}

string class_type::get_string(class_type::inst_t obj, size_t pid) const
{
      char*buf = reinterpret_cast<char*> (obj);
      if (pid >= properties_.size()) {
	    fprintf(stderr, "ERROR: get_string pid=%zu >= properties_.size()=%zu class=%s\n",
		    pid, properties_.size(), class_name_.c_str());
	    // Print all property names
	    for (size_t i = 0; i < properties_.size(); ++i) {
		  fprintf(stderr, "  property[%zu] = %s\n", i, properties_[i].name.c_str());
	    }
      }
      assert(pid < properties_.size());
      return properties_[pid].type->get_string(buf);
}

void class_type::set_object(class_type::inst_t obj, size_t pid,
			    const vvp_object_t&val, size_t idx) const
{
      char*buf = reinterpret_cast<char*> (obj);
      assert(pid < properties_.size());
      // Debug: print class and property info for troubleshooting
      // fprintf(stderr, "DEBUG: set_object on class '%s' property[%zu] '%s'\n",
      //         class_name_.c_str(), pid, properties_[pid].name.c_str());
      properties_[pid].type->set_object(buf, val, idx);
}

void class_type::get_object(class_type::inst_t obj, size_t pid,
			    vvp_object_t&val, size_t idx) const
{
      char*buf = reinterpret_cast<char*> (obj);
      assert(pid < properties_.size());
      // Debug: print class and property info for troubleshooting
      // fprintf(stderr, "DEBUG: get_object on class '%s' property[%zu] '%s'\n",
      //         class_name_.c_str(), pid, properties_[pid].name.c_str());
      properties_[pid].type->get_object(buf, val, idx);
}

void class_type::copy_property(class_type::inst_t dst, size_t pid, class_type::inst_t src) const
{
      char*dst_buf = reinterpret_cast<char*> (dst);
      char*src_buf = reinterpret_cast<char*> (src);

      assert(pid < properties_.size());

      properties_[pid].type->copy(dst_buf, src_buf);
}

int class_type::get_type_code(void) const
{
      return vpiClassDefn;
}

void class_type::register_method(const string& name, __vpiScope* scope, struct vvp_code_s* entry)
{
      method_info info;
      info.scope = scope;
      info.entry = entry;
      methods_[name] = info;
}

void class_type::set_method_entry(const string& name, struct vvp_code_s* entry)
{
      auto it = methods_.find(name);
      if (it != methods_.end())
	    it->second.entry = entry;
}

const class_type::method_info* class_type::get_method(const string& name) const
{
      // First check this class's methods
      auto it = methods_.find(name);
      if (it != methods_.end())
	    return &it->second;

      // If not found and we have a parent, check the parent class (inheritance)
      if (parent_)
	    return parent_->get_method(name);

      return 0;
}

static class_type*compile_class = 0;

// Deferred parent resolution for forward-declared classes
static std::vector<std::pair<class_type*, std::string>> deferred_parents;

void compile_class_start(char*lab, char*nam, unsigned ntype, char*parent_lab)
{
      assert(compile_class == 0);
      compile_class = new class_type(nam, ntype);

      // If parent_lab is specified, try to look up the parent class
      if (parent_lab) {
	    vpiHandle parent_h = vvp_lookup_handle(parent_lab);
	    if (parent_h) {
		  class_type*parent = dynamic_cast<class_type*>(parent_h);
		  if (parent)
			compile_class->set_parent(parent);
	    } else {
		  // Parent not found yet - store for deferred resolution
		  deferred_parents.push_back(std::make_pair(compile_class, std::string(parent_lab)));
	    }
	    free(parent_lab);
      }

      compile_vpi_symbol(lab, compile_class);
      free(lab);
      delete[]nam;
}

void compile_class_resolve_parents(void)
{
      // Resolve all deferred parent links now that all classes are defined
      for (auto& dp : deferred_parents) {
	    class_type* child = dp.first;
	    const std::string& parent_lab = dp.second;
	    vpiHandle parent_h = vvp_lookup_handle(parent_lab.c_str());
	    if (parent_h) {
		  class_type* parent = dynamic_cast<class_type*>(parent_h);
		  if (parent) {
			child->set_parent(parent);
		  }
	    }
      }
      deferred_parents.clear();
}

void compile_class_property(unsigned idx, char*nam, char*typ, uint64_t array_size, int rand_flag)
{
      assert(compile_class);
      compile_class->set_property(idx, nam, typ, array_size, rand_flag);
      delete[]nam;
      delete[]typ;
}

void compile_class_done(void)
{
      __vpiScope*scope = vpip_peek_current_scope();
      assert(scope);
      assert(compile_class);
      compile_class->finish_setup();
      scope->classes[compile_class->class_name()] = compile_class;
      compile_class = 0;
}

/*
 * Factory registration: .factory "type_name", class_label ;
 * This registers a class with the UVM factory under the given type name.
 */
void compile_factory(char*type_name, char*class_label)
{
      // Look up the class definition from the label
      vpiHandle class_h = vvp_lookup_handle(class_label);
      if (!class_h) {
	    fprintf(stderr, "ERROR: .factory: class label '%s' not found\n",
		    class_label);
	    delete[]type_name;
	    free(class_label);
	    return;
      }

      class_type*class_def = dynamic_cast<class_type*>(class_h);
      if (!class_def) {
	    fprintf(stderr, "ERROR: .factory: '%s' is not a class\n",
		    class_label);
	    delete[]type_name;
	    free(class_label);
	    return;
      }

      // Register with the factory
      vvp_factory_registry::instance().register_class(type_name, class_def);

      delete[]type_name;
      free(class_label);
}

/*
 * Constraint bound: .constraint_bound class_label, "constraint_name", prop_idx, "op", soft, has_const, value, sysfunc_type, sysfunc_arg, weight, weight_per_value, has_cond, cond_prop, "cond_op", cond_has_const, cond_value ;
 * This registers a simple constraint bound for the randomize() constraint solver.
 * sysfunc_type: 0=NONE, 1=COUNTONES, 2=ONEHOT, 3=ONEHOT0, 4=ISUNKNOWN, 5=CLOG2
 * weight: weight for weighted dist constraints (default 1)
 * weight_per_value: 1 for := (per value), 0 for :/ (per range)
 * has_cond: 1 if this bound has a guard condition (implication constraint)
 * cond_prop: property index for condition expression
 * cond_op: condition comparison operator
 * cond_has_const: 1 if condition compares to constant
 * cond_value: constant value or property index for condition
 */
void compile_constraint_bound(char*class_label, char*constraint_name, unsigned prop_idx,
                              char op, int soft, int has_const, int64_t value,
                              unsigned sysfunc_type, unsigned sysfunc_arg,
                              int64_t weight, int weight_per_value,
                              int has_cond, unsigned cond_prop, char cond_op,
                              int cond_has_const, int64_t cond_value,
                              int has_element_idx, int64_t element_idx)
{
      // Look up the class definition from the label
      vpiHandle class_h = vvp_lookup_handle(class_label);
      if (!class_h) {
	    fprintf(stderr, "ERROR: .constraint_bound: class label '%s' not found\n",
		    class_label);
	    free(class_label);
	    free(constraint_name);
	    return;
      }

      class_type*class_def = dynamic_cast<class_type*>(class_h);
      if (!class_def) {
	    fprintf(stderr, "ERROR: .constraint_bound: '%s' is not a class\n",
		    class_label);
	    free(class_label);
	    free(constraint_name);
	    return;
      }

      // Create and add the constraint bound
      class_type::simple_bound_t bound;
      bound.constraint_name = constraint_name ? constraint_name : "";
      bound.property_idx = prop_idx;
      bound.is_soft = (soft != 0);
      bound.has_prop_offset = false;  // Default

      // Check for property+offset operators (lowercase variants)
      // These indicate the value is packed: upper 32 bits = prop_idx, lower 32 bits = signed offset
      char effective_op = op;
      bool is_prop_offset = false;
      switch (op) {
	    case 'g': effective_op = 'G'; is_prop_offset = true; break;  // >= with offset
	    case 'l': effective_op = 'L'; is_prop_offset = true; break;  // <= with offset
	    case 'h': effective_op = '>'; is_prop_offset = true; break;  // > with offset
	    case 'j': effective_op = '<'; is_prop_offset = true; break;  // < with offset
	    case 'e': effective_op = '='; is_prop_offset = true; break;  // == with offset
	    case 'n': effective_op = '!'; is_prop_offset = true; break;  // != with offset
	    default: break;
      }
      bound.op = effective_op;

      // For excluded range constraint (op 'R'), value contains packed bounds:
      //   - lower 32 bits = low bound
      //   - upper 32 bits = high bound
      if (op == 'R') {
	    bound.is_excluded_range = true;
	    // Sign-extend both 32-bit bounds
	    int32_t low_raw = (int32_t)(value & 0xFFFFFFFF);
	    int32_t high_raw = (int32_t)((value >> 32) & 0xFFFFFFFF);
	    bound.excluded_range_low = (int64_t)low_raw;
	    bound.excluded_range_high = (int64_t)high_raw;
	    bound.has_const_bound = false;
	    bound.const_bound = 0;
	    bound.bound_prop_idx = 0;
      }
      // For property-based size constraint (op 's') or property+offset constraints,
      // value contains packed data:
      //   - upper 32 bits = source property index
      //   - lower 32 bits = signed offset
      else if (op == 's' || is_prop_offset) {
	    bound.has_const_bound = true;  // There's an offset
	    bound.has_prop_offset = true;  // Bound references property + offset
	    bound.bound_prop_idx = (value >> 32) & 0xFFFFFFFF;  // Source property index
	    // Sign-extend the 32-bit offset
	    int32_t offset_raw = (int32_t)(value & 0xFFFFFFFF);
	    bound.const_bound = (int64_t)offset_raw;  // Offset to add
      } else if (has_const) {
	    bound.has_const_bound = true;
	    bound.const_bound = value;
	    bound.bound_prop_idx = 0;
      } else {
	    bound.has_const_bound = false;
	    bound.const_bound = 0;
	    bound.bound_prop_idx = static_cast<size_t>(value);
      }
      bound.sysfunc_type = static_cast<class_type::sysfunc_type_t>(sysfunc_type);
      bound.sysfunc_arg_idx = sysfunc_arg;
      bound.weight = weight;
      bound.weight_per_value = (weight_per_value != 0);
      // Condition fields for implication constraints
      bound.has_condition = (has_cond != 0);
      bound.cond_prop_idx = cond_prop;
      bound.cond_op = cond_op;
      bound.cond_has_const = (cond_has_const != 0);
      if (cond_has_const) {
	    bound.cond_const = cond_value;
	    bound.cond_prop2_idx = 0;
      } else {
	    bound.cond_const = 0;
	    bound.cond_prop2_idx = static_cast<size_t>(cond_value);
      }
      // Indexed array element constraints - for conditional foreach patterns
      // e.g., foreach(arr[i]) if (i == 0) arr[i] == 0;
      bound.has_element_idx = (has_element_idx != 0);
      bound.element_idx = element_idx;
      // Foreach constraint flag (applies to dynamic arrays)
      bound.is_foreach = false;
      // Inside array constraint (not set from .constraint_bound directive)
      bound.is_inside_array = false;
      bound.inside_array_prop_idx = 0;
      // Excluded range: already set above if op == 'R', otherwise initialize to false
      if (op != 'R') {
	    bound.is_excluded_range = false;
	    bound.excluded_range_low = 0;
	    bound.excluded_range_high = 0;
      }
      class_def->add_constraint_bound(bound);

      free(class_label);
      free(constraint_name);
}

void compile_constraint_unique(char*class_label, unsigned prop_idx)
{
      // Look up the class definition from the label
      vpiHandle class_h = vvp_lookup_handle(class_label);
      if (!class_h) {
	    fprintf(stderr, "ERROR: .constraint_unique: class label '%s' not found\n",
		    class_label);
	    free(class_label);
	    return;
      }

      class_type*class_def = dynamic_cast<class_type*>(class_h);
      if (!class_def) {
	    fprintf(stderr, "ERROR: .constraint_unique: '%s' is not a class\n",
		    class_label);
	    free(class_label);
	    return;
      }

      // Add the unique constraint
      class_def->add_unique_constraint(prop_idx);

      free(class_label);
}

void class_type::add_unique_constraint(size_t prop_idx)
{
      unique_props_.push_back(prop_idx);
}

size_t class_type::get_unique_constraint_prop(size_t idx) const
{
      assert(idx < unique_props_.size());
      return unique_props_[idx];
}

void class_type::add_enum_bound(size_t prop_idx, const std::vector<int64_t>& values)
{
      enum_values_[prop_idx] = values;
}

const std::vector<int64_t>* class_type::get_enum_values(size_t prop_idx) const
{
      auto it = enum_values_.find(prop_idx);
      if (it != enum_values_.end())
	    return &it->second;
      return nullptr;
}

void compile_enum_bound(char*class_label, unsigned prop_idx,
                        unsigned num_values, int64_t* values, unsigned count)
{
      // Look up the class definition from the label
      vpiHandle class_h = vvp_lookup_handle(class_label);
      if (!class_h) {
	    fprintf(stderr, "ERROR: .enum_bound: class label '%s' not found\n",
		    class_label);
	    free(class_label);
	    return;
      }

      class_type*class_def = dynamic_cast<class_type*>(class_h);
      if (!class_def) {
	    fprintf(stderr, "ERROR: .enum_bound: '%s' is not a class\n",
		    class_label);
	    free(class_label);
	    return;
      }

      // Collect the enum values into a vector
      std::vector<int64_t> enum_vals;
      for (unsigned i = 0; i < count; ++i) {
	    enum_vals.push_back(values[i]);
      }

      // Add the enum bound to the class
      class_def->add_enum_bound(prop_idx, enum_vals);

      free(class_label);
}

#ifdef CHECK_WITH_VALGRIND
void class_def_delete(class_type *item)
{
      delete item;
}
#endif
