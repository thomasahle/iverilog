// Test dist constraint with multiple disjoint ranges
// Both ranges should produce values (using std::randomize)

module test;
  int x;
  int count_1_5 = 0;
  int count_10_15 = 0;
  int iterations = 200;
  
  initial begin
    // Test: dist with two disjoint ranges
    // Equal weights, so expect roughly 50/50 distribution
    for (int i = 0; i < iterations; i++) begin
      if (!std::randomize(x) with { x dist { [1:5] := 1, [10:15] := 1 }; }) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end
      
      if (x >= 1 && x <= 5) count_1_5++;
      else if (x >= 10 && x <= 15) count_10_15++;
      else begin
        $display("FAILED: x=%0d is outside both ranges", x);
        $finish;
      end
    end
    
    // With equal weights and same range sizes, expect roughly 50/50
    // Allow 30-70% for each range to account for randomness
    if (count_1_5 < 60 || count_1_5 > 140) begin
      $display("FAILED: Expected ~50%% in [1:5], got %0d/%0d", count_1_5, iterations);
      $finish;
    end
    
    if (count_10_15 < 60 || count_10_15 > 140) begin
      $display("FAILED: Expected ~50%% in [10:15], got %0d/%0d", count_10_15, iterations);
      $finish;
    end
    
    $display("PASSED");
    $display("dist {[1:5]:=1, [10:15]:=1}: range1=%0d range2=%0d", count_1_5, count_10_15);
  end
endmodule
