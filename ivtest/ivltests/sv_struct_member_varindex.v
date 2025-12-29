// Test that non-constant struct member array indices generate proper error
// This tests that the compiler doesn't crash (assertion failure) when
// accessing struct member arrays with non-constant indices in unsupported contexts.

module test;
  typedef struct packed {
    logic [3:0][7:0] data;
  } packet_t;

  packet_t pkt;
  int idx;

  initial begin
    idx = 2;
    // This should generate an error (non-constant index in packed struct member)
    // but NOT crash with an assertion failure
    pkt.data[idx] = 8'hAB;
    $display("FAILED: Should have gotten compile error");
  end
endmodule
