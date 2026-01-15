// Test for queue sort with (item.field) clause
// Tests sorting a queue of packed structs by a specific member

module test;

  // Define a packed struct - member order: prio is MSB, data is LSB
  typedef struct packed {
    bit [7:0] prio;   // Sort key (bits 15:8)
    bit [7:0] data;   // Data payload (bits 7:0)
  } packet_t;

  packet_t q[$];
  packet_t pkt;
  int errors;

  initial begin
    errors = 0;

    // Initialize queue with packets in random order using temp variable
    pkt.prio = 50; pkt.data = 8'hAA; q.push_back(pkt);
    pkt.prio = 10; pkt.data = 8'hBB; q.push_back(pkt);
    pkt.prio = 30; pkt.data = 8'hCC; q.push_back(pkt);
    pkt.prio = 20; pkt.data = 8'hDD; q.push_back(pkt);
    pkt.prio = 40; pkt.data = 8'hEE; q.push_back(pkt);

    $display("Before sort:");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: prio=%0d, data=0x%02h", i, q[i].prio, q[i].data);
    end

    // Sort by prio field (ascending)
    q.sort with (item.prio);

    $display("");
    $display("After sort with (item.prio):");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: prio=%0d, data=0x%02h", i, q[i].prio, q[i].data);
    end

    // Verify sorted order (ascending by prio)
    if (q[0].prio != 10) begin
      $display("ERROR: q[0].prio should be 10, got %0d", q[0].prio);
      errors = errors + 1;
    end
    if (q[1].prio != 20) begin
      $display("ERROR: q[1].prio should be 20, got %0d", q[1].prio);
      errors = errors + 1;
    end
    if (q[2].prio != 30) begin
      $display("ERROR: q[2].prio should be 30, got %0d", q[2].prio);
      errors = errors + 1;
    end
    if (q[3].prio != 40) begin
      $display("ERROR: q[3].prio should be 40, got %0d", q[3].prio);
      errors = errors + 1;
    end
    if (q[4].prio != 50) begin
      $display("ERROR: q[4].prio should be 50, got %0d", q[4].prio);
      errors = errors + 1;
    end

    // Verify data values moved with their prios
    if (q[0].data != 8'hBB) begin
      $display("ERROR: q[0].data should be 0xBB, got 0x%02h", q[0].data);
      errors = errors + 1;
    end
    if (q[4].data != 8'hAA) begin
      $display("ERROR: q[4].data should be 0xAA, got 0x%02h", q[4].data);
      errors = errors + 1;
    end

    // Test rsort with (item.prio) - descending order
    q.rsort with (item.prio);

    $display("");
    $display("After rsort with (item.prio):");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: prio=%0d, data=0x%02h", i, q[i].prio, q[i].data);
    end

    // Verify sorted order (descending by prio)
    if (q[0].prio != 50) begin
      $display("ERROR: After rsort, q[0].prio should be 50, got %0d", q[0].prio);
      errors = errors + 1;
    end
    if (q[4].prio != 10) begin
      $display("ERROR: After rsort, q[4].prio should be 10, got %0d", q[4].prio);
      errors = errors + 1;
    end

    // Final result
    if (errors == 0) begin
      $display("");
      $display("PASSED: All sort with clause tests passed!");
    end else begin
      $display("");
      $display("FAILED: %0d errors detected", errors);
    end

    $finish;
  end

endmodule
