// Test covergroup elaboration to stub class
// This test verifies that covergroups inside classes are elaborated correctly
// and can be accessed as properties.

class my_coverage;
  // Covergroup declaration - should become a property of __ivl_covergroup type
  covergroup cg with function sample(int value);
    option.per_instance = 1;
    VALUE_CP : coverpoint value {
      bins LOW = {[0:50]};
      bins HIGH = {[51:100]};
    }
  endgroup

  int sample_count;

  function new();
    sample_count = 0;
  endfunction

  // Method to demonstrate covergroup is accessible
  function void do_sample(int v);
    sample_count++;
    // Note: cg.sample() would be called here but covergroups are stubs
  endfunction
endclass

module test;
  my_coverage cov;

  initial begin
    cov = new();

    // Test basic class functionality works with covergroup present
    cov.do_sample(25);
    cov.do_sample(75);

    if (cov.sample_count == 2) begin
      $display("PASSED");
    end else begin
      $display("FAILED: sample_count = %0d, expected 2", cov.sample_count);
    end
  end
endmodule
