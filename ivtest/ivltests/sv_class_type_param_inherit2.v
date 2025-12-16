// Test parse-time type parameter inheritance from base class
// This tests that REQ/RSP from a parameterized base class are
// available as type identifiers in the derived class body.

// Simple item class
class my_item;
  int data;
  function new(int d = 0);
    data = d;
  endfunction
endclass

// Base class with type parameters (similar to uvm_driver)
class base_driver #(type REQ = int, type RSP = REQ);
  REQ req_item;
  RSP rsp_item;
endclass

// Derived class that extends base_driver with specialization
// REQ and RSP should be available as types in this class
class my_driver extends base_driver#(my_item);
  // These should work - REQ and RSP inherited from base class
  REQ local_req;
  RSP local_rsp;

  function new();
    local_req = null;
    local_rsp = null;
  endfunction

  function void set_local(REQ r);
    local_req = r;
  endfunction
endclass

module test;
  initial begin
    my_driver drv;
    my_item item;

    drv = new();
    item = new(100);

    drv.set_local(item);

    if (drv.local_req == null) begin
      $display("FAILED: local_req is null after set_local");
      $finish;
    end

    if (drv.local_req.data != 100) begin
      $display("FAILED: local_req.data=%0d, expected 100", drv.local_req.data);
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
