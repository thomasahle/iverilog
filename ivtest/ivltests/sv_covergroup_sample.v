// Test covergroup sample() and get_coverage() in class context
class coverage_collector;
  int val;

  covergroup cg;
    cp : coverpoint val {
      bins low = {[0:3]};
      bins mid = {[4:7]};
      bins high = {[8:15]};
    }
  endgroup

  function new();
    cg = new();
  endfunction

  function void sample_value(int v);
    val = v;
    cg.sample();
  endfunction

  function int get_sample_count();
    return cg.get_sample_count();
  endfunction

  function real get_cov();
    return cg.get_coverage();
  endfunction
endclass

module test;
  initial begin
    coverage_collector cc = new();

    // Sample a few values
    cc.sample_value(1);
    cc.sample_value(5);
    cc.sample_value(10);

    // Check the sample count
    $display("Sample count: %0d", cc.get_sample_count());

    // Coverage should be non-zero now
    $display("Coverage: %0.2f%%", cc.get_cov());

    if (cc.get_sample_count() >= 3)
      $display("PASSED");
    else
      $display("FAILED - sample count was %0d", cc.get_sample_count());
  end
endmodule
