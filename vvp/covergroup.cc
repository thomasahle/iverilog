#include "covergroup.h"
#include "compile.h"

#include <cassert>
#include <cstdio>
#include <cstdlib>

static std::vector<cvg_info_t*> cvg_infos;

void cvginfo_register(unsigned id, const char*name, unsigned cp_count,
                      unsigned bins_count, const int64_t*values,
                      unsigned value_count)
{
      if (id == 0) {
            fprintf(stderr, "ERROR: .cvginfo id 0 is reserved\n");
            return;
      }

      if (cvg_infos.size() <= id)
            cvg_infos.resize(id + 1, nullptr);

      if (cvg_infos[id])
            return;

      cvg_info_t*info = new cvg_info_t();
      if (name)
            info->name = name;
      info->bins_count = bins_count;

      unsigned idx = 0;
      for (unsigned cp = 0; cp < cp_count; cp++) {
            if (idx + 2 > value_count) {
                  fprintf(stderr, "ERROR: .cvginfo data underrun for %s\n",
                          info->name.c_str());
                  break;
            }
            cvg_coverpoint_t cp_info;
            cp_info.auto_bins = static_cast<int>(values[idx++]);
            int64_t bin_count = values[idx++];
            if (bin_count < 0) bin_count = 0;

            for (int64_t b = 0; b < bin_count; b++) {
                  if (idx + 2 > value_count) {
                        fprintf(stderr, "ERROR: .cvginfo bin underrun for %s\n",
                                info->name.c_str());
                        break;
                  }
                  cvg_bin_t bin;
                  int64_t flags = values[idx++];
                  bin.is_ignore = (flags & 1) != 0;
                  bin.is_illegal = (flags & 2) != 0;

                  int64_t range_count = values[idx++];
                  if (range_count < 0) range_count = 0;
                  for (int64_t r = 0; r < range_count; r++) {
                        if (idx + 2 > value_count) {
                              fprintf(stderr, "ERROR: .cvginfo range underrun for %s\n",
                                      info->name.c_str());
                              break;
                        }
                        cvg_bin_range_t range;
                        range.low = values[idx++];
                        range.high = values[idx++];
                        bin.ranges.push_back(range);
                  }
                  cp_info.bins.push_back(bin);
            }
            info->coverpoints.push_back(cp_info);
      }

      cvg_infos[id] = info;
}

const cvg_info_t* cvginfo_get(unsigned id)
{
      if (id < cvg_infos.size())
            return cvg_infos[id];
      return nullptr;
}

void compile_cvginfo(unsigned id, char*name, unsigned cp_count,
                     unsigned bins_count, int64_t*values, unsigned count)
{
      cvginfo_register(id, name, cp_count, bins_count, values, count);
      free(name);
}
