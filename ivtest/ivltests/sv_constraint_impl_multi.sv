// Test multiple implication constraints
// Verifies: mode == X -> constraint_for_X

module test;

  typedef enum bit [1:0] {
    IDLE  = 2'b00,
    READ  = 2'b01,
    WRITE = 2'b10,
    BURST = 2'b11
  } mode_t;

  class Transaction;
    rand mode_t mode;
    rand bit [7:0] addr;
    rand bit [7:0] data;
    rand bit [3:0] len;

    // Mode-based constraints using implication
    constraint c_read_mode {
      mode == READ -> addr[7:4] == 4'h0;  // Read addresses in lower range
    }

    constraint c_write_mode {
      mode == WRITE -> data != 0;  // Write data non-zero
    }

    constraint c_burst_mode {
      mode == BURST -> len >= 2;  // Burst needs at least 2 transfers
    }
  endclass

  initial begin
    Transaction tx;
    int i;
    int read_ok, write_ok, burst_ok;

    tx = new();
    read_ok = 0;
    write_ok = 0;
    burst_ok = 0;

    repeat (100) begin
      if (!tx.randomize()) begin
        $display("FAILED: randomize returned 0");
        $finish;
      end

      // Verify constraints based on mode
      case (tx.mode)
        READ: begin
          if (tx.addr[7:4] != 4'h0) begin
            $display("FAILED: READ mode but addr[7:4]=%h (expected 0)", tx.addr[7:4]);
            $finish;
          end
          read_ok++;
        end
        WRITE: begin
          if (tx.data == 0) begin
            $display("FAILED: WRITE mode but data=0");
            $finish;
          end
          write_ok++;
        end
        BURST: begin
          if (tx.len < 2) begin
            $display("FAILED: BURST mode but len=%0d (expected >=2)", tx.len);
            $finish;
          end
          burst_ok++;
        end
        default: ; // IDLE has no constraints
      endcase
    end

    $display("PASSED");
    $finish;
  end

endmodule
