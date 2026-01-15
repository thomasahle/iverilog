#ifndef IVL_VVP_COVERGROUP_H
#define IVL_VVP_COVERGROUP_H

#include <cstdint>
#include <string>
#include <vector>

struct cvg_bin_range_t {
      int64_t low;
      int64_t high;
};

struct cvg_bin_t {
      bool is_ignore = false;
      bool is_illegal = false;
      std::vector<cvg_bin_range_t> ranges;
};

struct cvg_coverpoint_t {
      int auto_bins = 0;
      std::vector<cvg_bin_t> bins;
};

struct cvg_info_t {
      std::string name;
      unsigned bins_count = 0;
      std::vector<cvg_coverpoint_t> coverpoints;
};

void cvginfo_register(unsigned id, const char*name, unsigned cp_count,
                      unsigned bins_count, const int64_t*values,
                      unsigned value_count);
const cvg_info_t* cvginfo_get(unsigned id);

#endif /* IVL_VVP_COVERGROUP_H */
