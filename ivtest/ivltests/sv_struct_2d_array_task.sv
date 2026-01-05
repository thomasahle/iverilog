// Test passing structs with 2D arrays to tasks

parameter int DATA_WIDTH = 32;
parameter int LENGTH = 4;

typedef struct {
  bit [3:0] id;
  bit [15:0][DATA_WIDTH-1:0] data; // 2D array
  int count;
} transfer_s;

module test_struct_task;

  task process_transfer(inout transfer_s t);
    t.data[0] = 32'hDEADBEEF;
    t.count = 1;
  endtask

  initial begin
    transfer_s tx;
    tx.id = 4'hA;
    tx.count = 0;

    process_transfer(tx);

    if (tx.data[0] == 32'hDEADBEEF && tx.count == 1)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
