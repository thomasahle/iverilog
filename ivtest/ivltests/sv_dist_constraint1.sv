// Test dist constraints with := (equal weight) and :/ (divided weight) operators
// Also test unbounded ranges with $

class TestDist;
  rand int value;
  rand int delay;
  rand bit [7:0] byte_val;

  // Basic dist with := (equal weight per value in range)
  constraint value_c { value dist { [1:10] := 80, [11:100] :/ 20 }; }

  // Unbounded range with $ (upper bound)
  constraint delay_c { delay dist { [1:10]:=94, [11:$]:/6 }; }

  // Simple dist with single values
  constraint byte_c { byte_val dist { 0 := 10, [1:127] :/ 80, [128:255] := 10 }; }
endclass

module test;
  TestDist td;

  initial begin
    td = new;
    // Just verify compilation - dist is parsed but not enforced
    if (td.randomize()) begin
      $display("randomize succeeded");
    end
    $display("PASSED");
    $finish;
  end
endmodule
