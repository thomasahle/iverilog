// Test named struct aggregate assignment pattern parsing
// IEEE 1800-2017 Section 10.9.2

module test;
  typedef struct packed {
    logic [7:0] field_a;
    logic [7:0] field_b;
    logic field_c;
  } my_struct_t;

  my_struct_t s;

  initial begin
    // Named aggregate assignment pattern - '{member: value, ...}
    s = '{field_a: 8'd10, field_b: 8'd20, field_c: 1'b1};
    $display("PASSED");
  end
endmodule
