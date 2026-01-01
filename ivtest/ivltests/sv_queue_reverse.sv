// Test queue reverse() method
module test;
   int iq[$];
   real rq[$];
   string sq[$];

   initial begin
      // Test integer queue reverse
      iq = '{1, 2, 3, 4, 5};
      iq.reverse();
      if (iq[0] == 5 && iq[1] == 4 && iq[2] == 3 && iq[3] == 2 && iq[4] == 1)
         $display("PASSED: Integer queue reverse");
      else
         $display("FAILED: Integer queue reverse - got %p", iq);

      // Test real queue reverse
      rq = '{1.1, 2.2, 3.3};
      rq.reverse();
      if (rq[0] == 3.3 && rq[1] == 2.2 && rq[2] == 1.1)
         $display("PASSED: Real queue reverse");
      else
         $display("FAILED: Real queue reverse - got %p", rq);

      // Test string queue reverse
      sq = '{"first", "second", "third"};
      sq.reverse();
      if (sq[0] == "third" && sq[1] == "second" && sq[2] == "first")
         $display("PASSED: String queue reverse");
      else
         $display("FAILED: String queue reverse - got %p", sq);

      // Test single element (should remain same)
      iq = '{42};
      iq.reverse();
      if (iq.size() == 1 && iq[0] == 42)
         $display("PASSED: Single element reverse");
      else
         $display("FAILED: Single element reverse");

      // Test two elements
      iq = '{10, 20};
      iq.reverse();
      if (iq[0] == 20 && iq[1] == 10)
         $display("PASSED: Two element reverse");
      else
         $display("FAILED: Two element reverse");
   end
endmodule
