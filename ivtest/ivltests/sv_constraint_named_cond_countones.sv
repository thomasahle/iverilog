// Test conditional $countones in named constraints
// This was documented as not working, but Session 110 may have fixed it

module test;
  typedef enum logic [1:0] { BYTE=0, HALFWORD=1, WORD=2 } size_t;

  class Transaction;
    rand size_t transfer_size;
    rand logic [3:0] strobe;

    // Named constraint with conditional $countones
    constraint strobeValid {
      if (transfer_size == BYTE) $countones(strobe) == 1;
      else if (transfer_size == HALFWORD) $countones(strobe) == 2;
      else $countones(strobe) == 4;
    }
  endclass

  initial begin
    Transaction t;
    int byte_count = 0, halfword_count = 0, word_count = 0;
    int i;

    t = new();

    // Test multiple randomizations
    for (i = 0; i < 100; i++) begin
      if (!t.randomize()) begin
        $display("FAILED: randomize() returned 0");
        $finish;
      end

      // Check constraint is satisfied
      case (t.transfer_size)
        BYTE: begin
          byte_count++;
          if ($countones(t.strobe) != 1) begin
            $display("FAILED: BYTE should have countones=1, got %0d, strobe=%b",
                     $countones(t.strobe), t.strobe);
            $finish;
          end
        end
        HALFWORD: begin
          halfword_count++;
          if ($countones(t.strobe) != 2) begin
            $display("FAILED: HALFWORD should have countones=2, got %0d, strobe=%b",
                     $countones(t.strobe), t.strobe);
            $finish;
          end
        end
        WORD: begin
          word_count++;
          if ($countones(t.strobe) != 4) begin
            $display("FAILED: WORD should have countones=4, got %0d, strobe=%b",
                     $countones(t.strobe), t.strobe);
            $finish;
          end
        end
      endcase
    end

    $display("Tested 100 randomizations:");
    $display("  BYTE: %0d (countones=1)", byte_count);
    $display("  HALFWORD: %0d (countones=2)", halfword_count);
    $display("  WORD: %0d (countones=4)", word_count);

    if (byte_count == 0 || halfword_count == 0 || word_count == 0) begin
      $display("FAILED: Not all transfer_size values were generated");
      $finish;
    end

    $display("PASSED");
    $finish;
  end
endmodule
