// Test queue sort() and rsort() methods
module test;
   int iq[$];
   real rq[$];
   string sq[$];

   initial begin
      // Test integer queue sort
      iq = '{5, 2, 8, 1, 9, 3};
      iq.sort();
      if (iq[0] == 1 && iq[1] == 2 && iq[2] == 3 && iq[3] == 5 && iq[4] == 8 && iq[5] == 9)
         $display("PASSED: Integer queue sort");
      else
         $display("FAILED: Integer queue sort - got %p", iq);

      // Test integer queue rsort
      iq = '{5, 2, 8, 1, 9, 3};
      iq.rsort();
      if (iq[0] == 9 && iq[1] == 8 && iq[2] == 5 && iq[3] == 3 && iq[4] == 2 && iq[5] == 1)
         $display("PASSED: Integer queue rsort");
      else
         $display("FAILED: Integer queue rsort - got %p", iq);

      // Test real queue sort
      rq = '{3.3, 1.1, 2.2};
      rq.sort();
      if (rq[0] == 1.1 && rq[1] == 2.2 && rq[2] == 3.3)
         $display("PASSED: Real queue sort");
      else
         $display("FAILED: Real queue sort - got %p", rq);

      // Test real queue rsort
      rq = '{3.3, 1.1, 2.2};
      rq.rsort();
      if (rq[0] == 3.3 && rq[1] == 2.2 && rq[2] == 1.1)
         $display("PASSED: Real queue rsort");
      else
         $display("FAILED: Real queue rsort - got %p", rq);

      // Test string queue sort
      sq = '{"charlie", "alpha", "bravo"};
      sq.sort();
      if (sq[0] == "alpha" && sq[1] == "bravo" && sq[2] == "charlie")
         $display("PASSED: String queue sort");
      else
         $display("FAILED: String queue sort - got %p", sq);

      // Test string queue rsort
      sq = '{"charlie", "alpha", "bravo"};
      sq.rsort();
      if (sq[0] == "charlie" && sq[1] == "bravo" && sq[2] == "alpha")
         $display("PASSED: String queue rsort");
      else
         $display("FAILED: String queue rsort - got %p", sq);

      // Test empty queue (should not crash)
      iq = '{};
      iq.sort();
      iq.rsort();
      $display("PASSED: Empty queue sort/rsort (no crash)");

      // Test single element (should remain unchanged)
      iq = '{42};
      iq.sort();
      if (iq.size() == 1 && iq[0] == 42)
         $display("PASSED: Single element sort");
      else
         $display("FAILED: Single element sort");
   end
endmodule
