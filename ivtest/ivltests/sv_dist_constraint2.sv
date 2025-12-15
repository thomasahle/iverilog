// Test dist constraints with various edge cases
// Including unbounded ranges with $ and mixed weights

class DistTest;
  rand bit [7:0] byte_val;
  rand int signed_val;
  rand bit [15:0] wide_val;

  // Test unbounded lower range [$:expr]
  constraint lower_unbounded { signed_val dist { [$:-100] := 10, [-99:99] :/ 80, [100:$] := 10 }; }

  // Test single values mixed with ranges
  constraint mixed_vals { byte_val dist { 0 := 5, [1:127] :/ 90, 255 := 5 }; }

  // Test wide values with ranges
  constraint wide_c { wide_val dist { [0:1000] := 50, [1001:$] :/ 50 }; }
endclass

module test;
  DistTest dt;

  initial begin
    dt = new;
    // Just verify compilation - dist is parsed but not enforced
    if (dt.randomize()) begin
      $display("randomize succeeded, byte_val=%0d", dt.byte_val);
    end
    $display("PASSED");
    $finish;
  end
endmodule
