// Test covergroup with unbounded bin ranges using $
// This test verifies that unbounded ranges like {[0:$]} and {[$:100]} are parsed.

class test_coverage;
  int value;

  covergroup cg;
    option.per_instance = 1;

    // Test unbounded upper limit
    VALUE_CP : coverpoint value {
      bins LOW = {[0:99]};
      bins MID = {[100:999]};
      illegal_bins HIGH = {[1000:$]};  // Unbounded upper limit
    }
  endgroup
endclass

module test;
  initial begin
    $display("PASSED");
  end
endmodule
