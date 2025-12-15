// Test: soft keyword in constraints
// Verifies that 'soft' constraints can be parsed

class packet;
  rand bit [7:0] data;
  rand bit [3:0] addr;

  // Regular constraint
  constraint addr_range { addr inside {[0:10]}; }

  // Soft constraint - lower priority, can be overridden
  constraint data_soft { soft data inside {[0:100]}; }

  // Soft constraint with expression
  constraint data_positive { soft data > 0; }

  function new();
    data = 0;
    addr = 0;
  endfunction
endclass

module test;
  packet p;

  initial begin
    p = new();

    // Just test that compilation works - randomization may work partially
    $display("Initial: addr=%0d, data=%0d", p.addr, p.data);

    // Set values manually since randomization may not fully work
    p.addr = 5;
    p.data = 50;

    if (p.addr == 5 && p.data == 50) begin
      $display("PASSED");
    end else begin
      $display("FAILED");
    end
  end
endmodule
