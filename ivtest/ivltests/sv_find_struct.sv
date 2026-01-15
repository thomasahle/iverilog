// Test find/find_first/find_last on struct queues (return elements, not indices)
module test;

typedef struct packed {
  logic [7:0] awid;
  logic [31:0] addr;
} pkt_t;

pkt_t q[$];
pkt_t results[$];

initial begin
  q.push_back('{awid: 1, addr: 100});
  q.push_back('{awid: 2, addr: 200});
  q.push_back('{awid: 2, addr: 300});
  q.push_back('{awid: 3, addr: 400});

  // Test find_last with struct member
  results = q.find_last with (item.awid == 2);
  if (results.size() != 1 || results[0].addr != 300) begin
    $display("FAILED: find_last expected addr=300, got size=%0d", results.size());
    $finish;
  end

  // Test find_first with struct member
  results = q.find_first with (item.awid == 2);
  if (results.size() != 1 || results[0].addr != 200) begin
    $display("FAILED: find_first expected addr=200, got size=%0d", results.size());
    $finish;
  end

  // Test find with struct member (all matches)
  results = q.find with (item.awid == 2);
  if (results.size() != 2) begin
    $display("FAILED: find expected size=2, got size=%0d", results.size());
    $finish;
  end

  $display("PASSED");
  $finish;
end

endmodule
