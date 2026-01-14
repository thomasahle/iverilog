// Test conditional constraint else branch with $countones
// Bug: The else branch of if-else-if conditional constraints was not
// properly enforced when the condition variable was also random.
// The enum iterator was starting from first_name() which returns an
// iterator to the first declared name, but std::map is ordered
// lexicographically. If the first declared name comes last
// lexicographically (like "BIT_8" among "BIT_16", "BIT_24", "BIT_32", "BIT_8"),
// the iterator immediately reaches end() after the first increment.

typedef enum {BIT_8, BIT_16, BIT_24, BIT_32} transfer_size_e;

class apb_tx;
  rand bit [3:0] pstrb;
  rand transfer_size_e transfer_size;

  // Constraint with if-else-if chain testing $countones
  constraint transfer_size_c {
    if(transfer_size == BIT_8)
      $countones(pstrb) == 1;
    else if(transfer_size == BIT_16)
      $countones(pstrb) == 2;
    else if(transfer_size == BIT_24)
      $countones(pstrb) == 3;
    else
      $countones(pstrb) == 4;  // This is the BIT_32 case
  }
endclass

module tb;
  apb_tx tx;
  int expected, actual;
  int pass = 0, fail = 0;

  initial begin
    tx = new();

    repeat (40) begin
      if (tx.randomize()) begin
        case (tx.transfer_size)
          BIT_8: expected = 1;
          BIT_16: expected = 2;
          BIT_24: expected = 3;
          BIT_32: expected = 4;
        endcase
        actual = $countones(tx.pstrb);
        if (actual != expected) begin
          $display("FAIL: size=%s pstrb=%b expected=%0d actual=%0d",
                   tx.transfer_size.name(), tx.pstrb, expected, actual);
          fail++;
        end else begin
          pass++;
        end
      end
    end

    $display("Pass: %0d, Fail: %0d", pass, fail);
    if (fail == 0)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
