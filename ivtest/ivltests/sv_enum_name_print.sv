// Test enum .name() method
module test;
  typedef enum bit [15:0] {
    SLAVE_0  = 16'b0000_0000_0000_0001,
    SLAVE_1  = 16'b0000_0000_0000_0010
  } slave_no_e;

  initial begin
    slave_no_e sel;

    sel = SLAVE_0;
    $display("sel = %b (%0d)", sel, sel);
    $display("sel.name() = '%s'", sel.name());

    sel = SLAVE_1;
    $display("sel = %b (%0d)", sel, sel);
    $display("sel.name() = '%s'", sel.name());

    if (sel.name() == "SLAVE_1") begin
      $display("PASSED");
    end else begin
      $display("FAILED: expected 'SLAVE_1', got '%s'", sel.name());
    end

    $finish;
  end
endmodule
