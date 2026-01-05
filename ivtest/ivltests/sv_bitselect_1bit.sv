// Test bit-select on 1-bit signal in always_comb
// This tests the APB pattern where pselx is [0:0] and we use pselx[0]

module test;
  logic clk;
  logic [0:0] src_sel;   // 1-bit signal
  logic [0:0] dst_sel;   // 1-bit signal

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Route using bit-select on 1-bit signal
  always_comb begin
    case(src_sel)
      2'b01: begin
        dst_sel = src_sel[0];  // bit-select on 1-bit
        $display("[%0t] Case 2'b01 matched: src_sel=%b, src_sel[0]=%b, dst_sel=%b",
                 $time, src_sel, src_sel[0], dst_sel);
      end
      default: begin
        dst_sel = 1'b0;
        $display("[%0t] Default case: src_sel=%b, dst_sel=%b",
                 $time, src_sel, dst_sel);
      end
    endcase
  end

  initial begin
    src_sel = 0;
    #20;

    $display("Setting src_sel = 1");
    src_sel = 1;
    #1;  // Let combinational logic settle

    $display("[%0t] After assign: src_sel=%b, dst_sel=%b", $time, src_sel, dst_sel);

    if (dst_sel !== 1'b1) begin
      $display("FAILED: Expected dst_sel=1, got %b", dst_sel);
      $finish;
    end

    #20;
    $display("PASSED");
    $finish;
  end
endmodule
