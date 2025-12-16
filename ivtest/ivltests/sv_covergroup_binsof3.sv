// Test binsof with hierarchical reference (coverpoint.bin_name)
// This test verifies that the syntax parses correctly
// Runtime coverage is stubbed - covergroups are not functional

typedef enum logic [2:0] {
   ADDR_LOW  = 3'b000,
   ADDR_MID  = 3'b010,
   ADDR_HIGH = 3'b111
} addr_type_e;

typedef enum logic [1:0] {
   DATA_ZERO  = 2'b00,
   DATA_ONE   = 2'b01,
   DATA_TWO   = 2'b10,
   DATA_THREE = 2'b11
} data_type_e;

class TestCoverage;
   addr_type_e addr;
   data_type_e data;

   covergroup cg;
      option.per_instance = 1;

      ADDR_CP : coverpoint addr {
         bins LOW  = {ADDR_LOW};
         bins MID  = {ADDR_MID};
         bins HIGH = {ADDR_HIGH};
      }

      DATA_CP : coverpoint data {
         bins ZERO  = {DATA_ZERO};
         bins ONE   = {DATA_ONE};
         bins TWO   = {DATA_TWO};
         bins THREE = {DATA_THREE};
      }

      // Cross coverage with binsof hierarchical reference
      // This is the syntax used in AXI4 Lite AVIP
      ADDR_X_DATA : cross ADDR_CP, DATA_CP {
         // Test binsof(coverpoint.bin_name) syntax with && operator
         ignore_bins low_zero = binsof(ADDR_CP.LOW) && binsof(DATA_CP.ZERO);
         ignore_bins high_three = binsof(ADDR_CP.HIGH) && binsof(DATA_CP.THREE);
         // Test with || operator
         ignore_bins mid_or_two = binsof(ADDR_CP.MID) || binsof(DATA_CP.TWO);
      }
   endgroup

endclass

module test;
   initial begin
      // Just verify the parsing worked - covergroups are not functional
      $display("Covergroup with binsof hierarchical reference parsed successfully");
      $display("PASSED");
      $finish;
   end
endmodule
