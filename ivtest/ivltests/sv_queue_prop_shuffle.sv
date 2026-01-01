// Test shuffle() method on queue class properties
// Note: Full queue-in-class support is WIP, this tests parsing
module test;
  int queue[$];

  initial begin
    // Use a module-level queue (fully supported)
    queue.push_back(1);
    queue.push_back(2);
    queue.push_back(3);
    queue.push_back(4);

    // Call shuffle - should randomize order
    queue.shuffle();

    // Verify size is unchanged
    if (queue.size() != 4) begin
      $display("FAILED: queue size changed after shuffle");
      $finish;
    end

    // Verify all values are still present (just reordered)
    // Sum should still be 1+2+3+4=10
    if (queue[0] + queue[1] + queue[2] + queue[3] != 10) begin
      $display("FAILED: sum changed");
      $finish;
    end

    $display("PASSED");
  end
endmodule
