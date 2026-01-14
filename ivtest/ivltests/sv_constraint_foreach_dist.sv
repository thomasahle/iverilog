// Test foreach with dist constraint - weighted range selection
// With := syntax (weight per value), the probability of selecting from a range
// is proportional to (range_size * weight), not just weight.
// So [0:10] := 90 has total weight 11*90=990
// And [11:255] := 10 has total weight 245*10=2450
// Expected distribution: ~29% in [0:10], ~71% in [11:255]
module test;
  class tx;
    rand bit [7:0] data[];
    constraint c_size { data.size() == 10; }
    constraint c_dist {
      foreach (data[i]) data[i] dist { [0:10] := 90, [11:255] := 10 };
    }
  endclass

  initial begin
    tx t;
    int low_count, high_count;
    t = new;
    low_count = 0;
    high_count = 0;

    // Run 100 iterations with 10 elements each = 1000 total samples
    repeat(100) begin
      void'(t.randomize());
      foreach(t.data[i]) begin
        if (t.data[i] <= 10) low_count++;
        else high_count++;
      end
    end

    // With := semantics:
    // Expected ratio: 990:2450 = ~29%:71%
    // Allow wide margin: low should be 100-500 (10-50%), high should be 500-900
    if (low_count >= 100 && low_count <= 500 && high_count >= 500 && high_count <= 900)
      $display("PASSED");
    else begin
      $display("FAILED: low=%0d high=%0d", low_count, high_count);
    end
  end
endmodule
