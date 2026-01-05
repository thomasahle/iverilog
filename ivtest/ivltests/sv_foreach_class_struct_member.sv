// Test foreach loop on class property that is a struct with array member
// This tests the fix for foreach on struct member arrays

module test;

  typedef struct packed {
    logic [7:0] header;
    logic [3:0][7:0] data;  // Packed array within struct
    logic [7:0] footer;
  } packet_t;

  class PacketHandler;
    packet_t pkt;

    function new();
      pkt.header = 8'hAA;
      pkt.footer = 8'hBB;
      foreach(pkt.data[i]) begin
        pkt.data[i] = i * 10;
      end
    endfunction

    function int sum_data();
      int total = 0;
      foreach(pkt.data[i]) begin
        total = total + pkt.data[i];
      end
      return total;
    endfunction

    function void print_data();
      $display("Header: %h", pkt.header);
      foreach(pkt.data[i]) begin
        $display("Data[%0d]: %0d", i, pkt.data[i]);
      end
      $display("Footer: %h", pkt.footer);
    endfunction
  endclass

  initial begin
    PacketHandler handler;
    int sum;
    int errors = 0;

    handler = new();
    handler.print_data();

    sum = handler.sum_data();
    $display("Sum: %0d", sum);

    // Expected: 0 + 10 + 20 + 30 = 60
    if (sum !== 60) begin
      $display("FAILED: Expected sum 60, got %0d", sum);
      errors++;
    end

    if (handler.pkt.header !== 8'hAA) begin
      $display("FAILED: Header mismatch");
      errors++;
    end

    if (handler.pkt.footer !== 8'hBB) begin
      $display("FAILED: Footer mismatch");
      errors++;
    end

    if (errors == 0)
      $display("PASSED");
    else
      $display("FAILED with %0d errors", errors);
  end

endmodule
