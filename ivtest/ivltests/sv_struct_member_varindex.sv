// Test that variable indices to struct member arrays produce
// proper error messages instead of assertion crashes.
// This is a compile-error test (CE).
// Tests the fix for evaluate_index_prefix assertion failure.

module test;
  typedef struct packed {
    logic [7:0] alpha;
    logic [3:0][7:0] data;  // Packed array member
  } my_struct_t;

  my_struct_t s;
  int i;

  initial begin
    i = 2;
    // Multi-dimensional access with variable index - tests
    // evaluate_index_prefix error handling
    s.data[i][3:0] = 4'hA;
    $display("FAILED - should not compile");
  end
endmodule
