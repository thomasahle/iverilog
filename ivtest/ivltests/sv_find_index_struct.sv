// Test find_last_index with struct member access
// Tests both packed and unpacked structs

module test;

  typedef struct packed {
    int awid;
    int data;
  } packed_entry_t;

  typedef struct {  // unpacked
    int awid;
    int data;
  } unpacked_entry_t;

  packed_entry_t packed_queue[$];
  unpacked_entry_t unpacked_queue[$];
  int result_q[$];
  int passed = 1;

  initial begin
    // Test packed struct
    packed_queue.push_back('{awid: 1, data: 100});
    packed_queue.push_back('{awid: 2, data: 200});
    packed_queue.push_back('{awid: 2, data: 300});
    packed_queue.push_back('{awid: 3, data: 400});

    result_q = packed_queue.find_last_index with (item.awid == 2);
    if (result_q.size() != 1 || result_q[0] != 2) begin
      $display("FAILED: packed find_last_index expected [2], got size=%0d", result_q.size());
      if (result_q.size() > 0) $display("  result[0] = %0d", result_q[0]);
      passed = 0;
    end

    result_q = packed_queue.find_first_index with (item.awid == 2);
    if (result_q.size() != 1 || result_q[0] != 1) begin
      $display("FAILED: packed find_first_index expected [1], got size=%0d", result_q.size());
      if (result_q.size() > 0) $display("  result[0] = %0d", result_q[0]);
      passed = 0;
    end

    result_q = packed_queue.find_index with (item.awid == 2);
    if (result_q.size() != 2 || result_q[0] != 1 || result_q[1] != 2) begin
      $display("FAILED: packed find_index expected [1,2], got size=%0d", result_q.size());
      passed = 0;
    end

    // Test unpacked struct
    unpacked_queue.push_back('{awid: 1, data: 100});
    unpacked_queue.push_back('{awid: 2, data: 200});
    unpacked_queue.push_back('{awid: 2, data: 300});
    unpacked_queue.push_back('{awid: 3, data: 400});

    result_q = unpacked_queue.find_last_index with (item.awid == 2);
    if (result_q.size() != 1 || result_q[0] != 2) begin
      $display("FAILED: unpacked find_last_index expected [2], got size=%0d", result_q.size());
      if (result_q.size() > 0) $display("  result[0] = %0d", result_q[0]);
      passed = 0;
    end

    result_q = unpacked_queue.find_first_index with (item.awid == 2);
    if (result_q.size() != 1 || result_q[0] != 1) begin
      $display("FAILED: unpacked find_first_index expected [1], got size=%0d", result_q.size());
      if (result_q.size() > 0) $display("  result[0] = %0d", result_q[0]);
      passed = 0;
    end

    result_q = unpacked_queue.find_index with (item.awid == 2);
    if (result_q.size() != 2 || result_q[0] != 1 || result_q[1] != 2) begin
      $display("FAILED: unpacked find_index expected [1,2], got size=%0d", result_q.size());
      passed = 0;
    end

    // Test accessing second member (data)
    result_q = packed_queue.find_index with (item.data == 200);
    if (result_q.size() != 1 || result_q[0] != 1) begin
      $display("FAILED: packed find_index by data expected [1], got size=%0d", result_q.size());
      passed = 0;
    end

    result_q = unpacked_queue.find_index with (item.data == 300);
    if (result_q.size() != 1 || result_q[0] != 2) begin
      $display("FAILED: unpacked find_index by data expected [2], got size=%0d", result_q.size());
      passed = 0;
    end

    if (passed)
      $display("PASSED");

    $finish;
  end
endmodule
