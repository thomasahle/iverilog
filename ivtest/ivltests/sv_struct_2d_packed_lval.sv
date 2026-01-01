// Test 2D packed array indexed access in struct
module test;
  typedef struct {
    bit [3:0][7:0] data;  // 4 elements of 8 bits each
  } pkt_t;

  pkt_t pkt;

  initial begin
    $display("Testing indexed lvalue assignment to 2D packed array in struct");

    // Set values one by one
    pkt.data[0] = 8'h11;
    pkt.data[1] = 8'h22;
    pkt.data[2] = 8'h33;
    pkt.data[3] = 8'h44;

    $display("After assignments:");
    $display("pkt.data = %h", pkt.data);
    $display("pkt.data[0] = %h (expected 11)", pkt.data[0]);
    $display("pkt.data[1] = %h (expected 22)", pkt.data[1]);
    $display("pkt.data[2] = %h (expected 33)", pkt.data[2]);
    $display("pkt.data[3] = %h (expected 44)", pkt.data[3]);

    if (pkt.data[0] == 8'h11 && pkt.data[1] == 8'h22 &&
        pkt.data[2] == 8'h33 && pkt.data[3] == 8'h44)
      $display("\nPASS: All indexed assignments work");
    else
      $display("\nFAIL: Some indexed assignments failed");

    // Also test modification
    pkt.data[1] = 8'hFF;
    $display("\nAfter pkt.data[1] = 8'hFF:");
    $display("pkt.data = %h", pkt.data);
    $display("pkt.data[1] = %h (expected FF)", pkt.data[1]);

    if (pkt.data[1] == 8'hFF && pkt.data[0] == 8'h11)
      $display("PASS: Modification works without affecting other elements");
    else
      $display("FAIL: Modification issue");
  end
endmodule
