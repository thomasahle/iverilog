// Test unique_index on class queue properties using push_back
class Container;
  int data[$];

  function new();
    data = {};
  endfunction
endclass

module test;
  Container c;
  int indices[$];

  initial begin
    c = new();

    // Populate queue with push_back
    c.data.push_back(10);
    c.data.push_back(20);
    c.data.push_back(10);
    c.data.push_back(30);
    c.data.push_back(20);
    c.data.push_back(10);
    c.data.push_back(40);

    $display("Queue: size = %0d", c.data.size());

    // Test unique_index on class property
    indices = c.data.unique_index();
    $display("unique_index result: size = %0d", indices.size());

    if (indices.size() == 4 && indices[0] == 0 && indices[1] == 1 &&
        indices[2] == 3 && indices[3] == 6) begin
      $display("PASSED");
    end else begin
      $display("FAILED: expected {0, 1, 3, 6}, got %0d elements", indices.size());
      foreach(indices[i])
        $display("  indices[%0d] = %0d", i, indices[i]);
    end
    $finish;
  end
endmodule
