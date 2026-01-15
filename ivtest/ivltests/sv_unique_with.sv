// Test for queue unique with (item.field) clause
// Tests returning unique elements based on a specific struct member

module test;

  // Define a packed struct - member order: prio is MSB, data is LSB
  typedef struct packed {
    bit [7:0] prio;   // Unique key (bits 15:8)
    bit [7:0] data;   // Data payload (bits 7:0)
  } packet_t;

  packet_t q[$];
  packet_t result[$];
  int indices[$];
  packet_t pkt;
  int errors;

  initial begin
    errors = 0;

    // Initialize queue with packets (some with duplicate prio values)
    pkt.prio = 50; pkt.data = 8'hAA; q.push_back(pkt);  // First with prio=50
    pkt.prio = 10; pkt.data = 8'hBB; q.push_back(pkt);  // First with prio=10
    pkt.prio = 50; pkt.data = 8'hCC; q.push_back(pkt);  // Duplicate prio=50 (different data)
    pkt.prio = 20; pkt.data = 8'hDD; q.push_back(pkt);  // First with prio=20
    pkt.prio = 10; pkt.data = 8'hEE; q.push_back(pkt);  // Duplicate prio=10 (different data)
    pkt.prio = 30; pkt.data = 8'hFF; q.push_back(pkt);  // First with prio=30

    $display("Before unique:");
    for (int i = 0; i < q.size(); i = i + 1) begin
      $display("  q[%0d]: prio=%0d, data=0x%02h", i, q[i].prio, q[i].data);
    end

    // Get unique elements by prio field
    result = q.unique with (item.prio);

    $display("");
    $display("After unique with (item.prio):");
    for (int i = 0; i < result.size(); i = i + 1) begin
      $display("  result[%0d]: prio=%0d, data=0x%02h", i, result[i].prio, result[i].data);
    end

    // Verify unique result has 4 elements (unique prio values: 50, 10, 20, 30)
    if (result.size() != 4) begin
      $display("ERROR: unique result should have 4 elements, got %0d", result.size());
      errors = errors + 1;
    end

    // Verify first occurrences are preserved (first element with each prio)
    if (result[0].prio != 50 || result[0].data != 8'hAA) begin
      $display("ERROR: result[0] should be prio=50, data=0xAA");
      errors = errors + 1;
    end
    if (result[1].prio != 10 || result[1].data != 8'hBB) begin
      $display("ERROR: result[1] should be prio=10, data=0xBB");
      errors = errors + 1;
    end
    if (result[2].prio != 20 || result[2].data != 8'hDD) begin
      $display("ERROR: result[2] should be prio=20, data=0xDD");
      errors = errors + 1;
    end
    if (result[3].prio != 30 || result[3].data != 8'hFF) begin
      $display("ERROR: result[3] should be prio=30, data=0xFF");
      errors = errors + 1;
    end

    // Test unique_index with (item.prio)
    indices = q.unique_index with (item.prio);

    $display("");
    $display("unique_index with (item.prio):");
    for (int i = 0; i < indices.size(); i = i + 1) begin
      $display("  index[%0d] = %0d (q[%0d].prio = %0d)", i, indices[i], indices[i], q[indices[i]].prio);
    end

    // Verify unique_index result
    if (indices.size() != 4) begin
      $display("ERROR: unique_index result should have 4 elements, got %0d", indices.size());
      errors = errors + 1;
    end

    // Verify indices point to first occurrences (0, 1, 3, 5)
    if (indices[0] != 0) begin
      $display("ERROR: indices[0] should be 0, got %0d", indices[0]);
      errors = errors + 1;
    end
    if (indices[1] != 1) begin
      $display("ERROR: indices[1] should be 1, got %0d", indices[1]);
      errors = errors + 1;
    end
    if (indices[2] != 3) begin
      $display("ERROR: indices[2] should be 3, got %0d", indices[2]);
      errors = errors + 1;
    end
    if (indices[3] != 5) begin
      $display("ERROR: indices[3] should be 5, got %0d", indices[3]);
      errors = errors + 1;
    end

    // Final result
    if (errors == 0) begin
      $display("");
      $display("PASSED: All unique with clause tests passed!");
    end else begin
      $display("");
      $display("FAILED: %0d errors detected", errors);
    end

    $finish;
  end

endmodule
