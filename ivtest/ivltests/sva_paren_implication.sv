// Test SVA parenthesized implication expressions
// Pattern: ((antecedent) |=> consequent)

module test;
  logic clk, reset;
  logic [1:0] htrans;
  logic [2:0] hburst;
  logic hready, hwrite;
  logic [31:0] hwdata;

  // Parenthesized overlapping implication
  property p_paren_ov;
    @(posedge clk) disable iff(reset)
    ((htrans == 2'b10 && hburst == 3'b000) |-> hready);
  endproperty : p_paren_ov

  // Parenthesized non-overlapping implication
  property p_paren_nov;
    @(posedge clk) disable iff(reset)
    ((htrans == 2'b10 && hready == 1 && hwrite == 1) |=> !$isunknown(hwdata));
  endproperty : p_paren_nov

  // Complex parenthesized with multiple conditions
  property p_complex;
    @(posedge clk) disable iff(!reset)
    ((htrans == 2'b10 || htrans == 2'b11) && hready == 1) |=> hwdata[0];
  endproperty : p_complex

  // Nested parentheses
  property p_nested;
    @(posedge clk)
    (((htrans == 2'b00) && hready) |-> (hburst == 3'b000));
  endproperty : p_nested

  // Assertions
  PAREN_OV: assert property (p_paren_ov);
  PAREN_NOV: assert property (p_paren_nov);
  COMPLEX: assert property (p_complex);
  NESTED: assert property (p_nested);

  // Cover with parenthesized implication
  COV_PAREN: cover property (@(posedge clk) ((htrans == 2'b10) |=> hready))
    $info("Covered parenthesized pattern");

  initial begin
    $display("PASSED - SVA parenthesized implication patterns parsed successfully");
    $finish;
  end
endmodule
