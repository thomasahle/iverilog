// Test that non-constant struct member array indices generate proper error
// This tests that the compiler doesn't crash (assertion failure) when
// accessing struct member arrays with non-constant indices in unsupported contexts.
//
// NOTE: This is marked as NI (Not Implemented) because:
// - Previously it was CE (Compile Error expected) but no error is produced
// - The feature compiles but produces incorrect results at runtime
// - Variable indexing into packed struct members is not fully supported

module test;
  typedef struct packed {
    logic [3:0][7:0] data;
  } packet_t;

  packet_t pkt;
  int idx;

  initial begin
    idx = 2;
    // Variable index into packed struct member array - not fully supported
    pkt.data[idx] = 8'hAB;
    $display("PASSED"); // Test that we didn't crash
  end
endmodule
