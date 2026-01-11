// Test enum type casting pattern
// Based on AHB AVIP pattern: enum_type'(value)

typedef enum bit [2:0] {
  OP_READ = 0,
  OP_WRITE = 1,
  OP_BURST = 2
} operation_e;

typedef enum bit [1:0] {
  SIZE_BYTE = 0,
  SIZE_HALF = 1,
  SIZE_WORD = 2
} size_e;

module test;
  bit [2:0] raw_op;
  bit [1:0] raw_size;
  operation_e op;
  size_e sz;
  int pass = 1;

  initial begin
    // Cast raw value to enum
    raw_op = 1;
    op = operation_e'(raw_op);
    if (op != OP_WRITE) begin
      $display("FAIL: op=%s, expected OP_WRITE", op.name());
      pass = 0;
    end

    raw_size = 2;
    sz = size_e'(raw_size);
    if (sz != SIZE_WORD) begin
      $display("FAIL: sz=%s, expected SIZE_WORD", sz.name());
      pass = 0;
    end

    // Cast from integer literal
    op = operation_e'(2);
    if (op != OP_BURST) begin
      $display("FAIL: op=%s, expected OP_BURST", op.name());
      pass = 0;
    end

    // Cast from expression
    raw_op = 0;
    op = operation_e'(raw_op + 1);
    if (op != OP_WRITE) begin
      $display("FAIL: op=%s, expected OP_WRITE from expression", op.name());
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
