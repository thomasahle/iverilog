// Test inheritance of type parameters from parameterized base class
// This is essential for UVM patterns like:
//   class my_driver extends uvm_driver#(my_transaction);
//
// Note: Derived classes use concrete types, not inherited param names.
// The REQ/RSP are used inside the base class (uvm_driver), not in derived classes.

module test;

// Simple transaction class
class base_item;
  int id;
  function new();
    id = 0;
  endfunction
endclass

// Derived transaction with data
class my_transaction extends base_item;
  int data;
  function new();
    super.new();
    data = 0;
  endfunction
endclass

// Parameterized base class (like uvm_driver)
class driver_base #(type REQ = base_item, type RSP = REQ);
  REQ req;
  RSP rsp;

  function new();
    req = null;
    rsp = null;
  endfunction

  virtual function void set_req(REQ r);
    req = r;
  endfunction

  virtual function REQ get_req();
    return req;
  endfunction

  // Method that uses both type parameters
  virtual function void process();
    if (req != null)
      $display("driver_base::process req.id=%0d", req.id);
  endfunction
endclass

// Derived class specializing the base class type parameters
class my_driver extends driver_base #(my_transaction);
  // REQ and RSP are set to my_transaction in this specialization
  // Methods use the inherited req/rsp properties with my_transaction type

  function new();
    super.new();
  endfunction

  // Override using concrete type (standard UVM pattern)
  virtual function void set_req(my_transaction r);
    super.set_req(r);
    $display("my_driver::set_req called, data=%0d", r.data);
  endfunction

  // Override process to access my_transaction specific fields
  virtual function void process();
    if (req != null) begin
      $display("my_driver::process data=%0d", req.data);
    end
  endfunction
endclass

initial begin
  my_driver drv;
  my_transaction tx;
  base_item item;

  drv = new();
  tx = new();
  tx.id = 42;
  tx.data = 100;

  // Pass my_transaction to driver
  drv.set_req(tx);

  // Call polymorphic process method
  drv.process();

  // Retrieve and verify via base class method
  item = drv.get_req();
  if (item.id !== 42) begin
    $display("FAILED: Expected id=42, got %0d", item.id);
    $finish;
  end

  // Cast back to my_transaction to access data
  if ($cast(tx, item)) begin
    if (tx.data !== 100) begin
      $display("FAILED: Expected data=100, got %0d", tx.data);
      $finish;
    end
  end else begin
    $display("FAILED: Cast to my_transaction failed");
    $finish;
  end

  $display("PASSED");
end

endmodule
