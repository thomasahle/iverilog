// Test conditional foreach constraints in named constraint blocks
// Verifies: foreach(arr[i]) if (condition) constraint
// Includes both simple conditions and OR conditions
module test;
  // Simple conditional: constrain first element to 0
  class simple_cond;
    rand bit [7:0] data[];
    constraint c_size { data.size() == 5; }
    constraint c_first {
      foreach (data[i]) if (i == 0) data[i] == 0;
    }
  endclass

  // OR conditional: constrain first and last elements to 0
  class or_cond;
    rand bit [7:0] data[];
    constraint c_size { data.size() == 5; }
    constraint c_ends {
      foreach (data[i]) if (i == 0 || i == 4) data[i] == 0;
    }
  endclass

  initial begin
    simple_cond s;
    or_cond o;
    int pass;
    int i;

    s = new;
    o = new;
    pass = 1;

    // Test simple conditional (10 iterations)
    for (i = 0; i < 10; i++) begin
      void'(s.randomize());
      if (s.data[0] != 0) begin
        pass = 0;
        $display("ERROR: simple_cond.data[0]=%0d (expected 0)", s.data[0]);
      end
    end

    // Test OR conditional (10 iterations)
    for (i = 0; i < 10; i++) begin
      void'(o.randomize());
      if (o.data[0] != 0) begin
        pass = 0;
        $display("ERROR: or_cond.data[0]=%0d (expected 0)", o.data[0]);
      end
      if (o.data[4] != 0) begin
        pass = 0;
        $display("ERROR: or_cond.data[4]=%0d (expected 0)", o.data[4]);
      end
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");

    $finish;
  end
endmodule
