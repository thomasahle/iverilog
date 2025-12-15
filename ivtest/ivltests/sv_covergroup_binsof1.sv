// Test binsof() and !binsof() syntax in cross coverage ignore_bins
// This test verifies the parsing works - covergroups are stub implementations
// Based on UART AVIP coverage syntax

typedef enum {FIVE_BIT, SIX_BIT, SEVEN_BIT, EIGHT_BIT} data_width_e;

class TestCoverage;
  data_width_e dw;
  bit [7:0] data;

  covergroup cg;
    option.per_instance = 1;

    DATA_WIDTH_CP : coverpoint dw {
      bins FIVE = {FIVE_BIT};
      bins SIX = {SIX_BIT};
      bins SEVEN = {SEVEN_BIT};
      bins EIGHT = {EIGHT_BIT};
    }

    DATA_PATTERN_5 : coverpoint data {
      bins pattern1_5 = {5'b11111};
      bins pattern2_5 = {5'b10101};
    }

    DATA_PATTERN_6 : coverpoint data {
      bins pattern1_6 = {6'b111111};
      bins pattern2_6 = {6'b101010};
    }

    // Cross with !binsof() negation - same syntax as UART AVIP
    DATA_PATTERN_5_DATA_WIDTH_CP : cross DATA_PATTERN_5, DATA_WIDTH_CP {
      ignore_bins data_5 = !binsof(DATA_WIDTH_CP) intersect {FIVE_BIT};
    }

    DATA_PATTERN_6_DATA_WIDTH_CP : cross DATA_PATTERN_6, DATA_WIDTH_CP {
      ignore_bins data_6 = !binsof(DATA_WIDTH_CP) intersect {SIX_BIT};
    }

    // Cross with binsof() (positive match)
    SIMPLE_CROSS : cross DATA_PATTERN_5, DATA_WIDTH_CP {
      ignore_bins five_only = binsof(DATA_WIDTH_CP) intersect {FIVE_BIT};
    }

  endgroup

endclass

module test;
  initial begin
    // Just verify the class with covergroup compiles correctly
    $display("PASSED");
    $finish;
  end
endmodule
