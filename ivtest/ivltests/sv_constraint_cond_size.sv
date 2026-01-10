// Test conditional size constraints
module test;
  typedef enum {SINGLE, BURST4, BURST8} burst_t;

  class packet;
    rand burst_t burst;
    rand bit [7:0] data[];
    
    constraint data_size_c {
      if (burst == SINGLE) data.size() == 1;
      else if (burst == BURST4) data.size() == 4;
      else data.size() == 8;
    }
    
    function new();
    endfunction
  endclass
  
  packet pkt;
  int pass = 1;
  
  initial begin
    pkt = new();
    
    // Test SINGLE
    pkt.burst = SINGLE;
    if (!pkt.randomize() with { burst == SINGLE; }) begin
      $display("FAILED: randomize failed for SINGLE");
      $finish;
    end
    if (pkt.data.size() != 1) begin
      $display("FAILED: SINGLE should have size 1, got %0d", pkt.data.size());
      pass = 0;
    end
    
    // Test BURST4  
    if (!pkt.randomize() with { burst == BURST4; }) begin
      $display("FAILED: randomize failed for BURST4");
      $finish;
    end
    if (pkt.data.size() != 4) begin
      $display("FAILED: BURST4 should have size 4, got %0d", pkt.data.size());
      pass = 0;
    end
    
    // Test BURST8
    if (!pkt.randomize() with { burst == BURST8; }) begin
      $display("FAILED: randomize failed for BURST8");
      $finish;
    end
    if (pkt.data.size() != 8) begin
      $display("FAILED: BURST8 should have size 8, got %0d", pkt.data.size());
      pass = 0;
    end
    
    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
