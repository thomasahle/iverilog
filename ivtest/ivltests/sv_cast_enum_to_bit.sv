// Test casting enum to bit field
module test;
  typedef enum bit [15:0] {
    SLAVE_0  = 16'b0000_0000_0000_0001,
    SLAVE_1  = 16'b0000_0000_0000_0010
  } slave_no_e;

  typedef struct {
    bit [0:0] pselx;  // 1-bit field
  } test_struct;

  initial begin
    slave_no_e sel;
    test_struct ts;
    bit [0:0] single_bit;

    sel = SLAVE_0;
    $display("sel = %b (%0d)", sel, sel);

    // Direct assignment
    single_bit = sel;
    $display("Direct assignment: single_bit = %b", single_bit);

    // $cast to bit
    $cast(ts.pselx, sel);
    $display("$cast result: ts.pselx = %b", ts.pselx);

    // Expected: bit[0] of SLAVE_0 is 1
    if (single_bit == 1'b1 && ts.pselx == 1'b1) begin
      $display("PASSED");
    end else begin
      $display("FAILED: expected 1, got single_bit=%b, ts.pselx=%b", single_bit, ts.pselx);
    end

    $finish;
  end
endmodule
