// Test const ref with struct types (UVM pattern)
// IEEE 1800-2005: const ref is commonly used with struct arguments

module test;

  // Simple struct type (like uvm_reg_bus_op)
  typedef struct packed {
    logic [31:0] addr;
    logic [31:0] data;
    logic write;
  } bus_op_t;

  // Function with const ref struct
  function automatic int process_op(const ref bus_op_t op);
    if (op.write)
      return op.addr + op.data;
    else
      return op.addr;
  endfunction

  // Task with const ref struct
  task automatic display_op(const ref bus_op_t op);
    $display("BusOp: addr=%0h data=%0h write=%0b", op.addr, op.data, op.write);
  endtask

  // Function with ref (non-const) that modifies
  function automatic void update_status(ref bus_op_t op, input logic [31:0] result);
    op.data = result;
  endfunction

  bus_op_t my_op;
  int result;

  initial begin
    // Test write operation
    my_op.addr = 32'h1000;
    my_op.data = 32'h55AA;
    my_op.write = 1;

    // Test const ref in function
    result = process_op(my_op);
    if (result !== 32'h65AA) begin
      $display("FAILED: process_op returned %0h, expected 65AA", result);
      $finish;
    end

    // Test const ref in task
    display_op(my_op);

    // Test ref modification
    update_status(my_op, 32'hDEAD);
    if (my_op.data !== 32'hDEAD) begin
      $display("FAILED: update_status didn't update data, got %0h", my_op.data);
      $finish;
    end

    // Test read operation
    my_op.write = 0;
    result = process_op(my_op);
    if (result !== 32'h1000) begin
      $display("FAILED: process_op read returned %0h, expected 1000", result);
      $finish;
    end

    $display("PASSED");
  end
endmodule
