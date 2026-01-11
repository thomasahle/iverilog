// Test foreach on queue of structs
// Uses temp variable workaround for struct element access
//
// Note: Direct access like packets[i].member is not supported.
// Workaround: temp = packets[i]; temp.member

typedef struct {
  int id;
  bit [7:0] data;
  bit valid;
} PacketInfo;

module test;
  PacketInfo packets[$];
  int pass = 1;

  initial begin
    PacketInfo p;
    PacketInfo temp;
    int count = 0;
    int sum = 0;

    // Add packets
    p.id = 1; p.data = 8'h10; p.valid = 1;
    packets.push_back(p);
    p.id = 2; p.data = 8'h20; p.valid = 1;
    packets.push_back(p);
    p.id = 3; p.data = 8'h30; p.valid = 0;
    packets.push_back(p);

    // Iterate with temp variable workaround
    foreach (packets[i]) begin
      temp = packets[i];
      count++;
      sum = sum + temp.data;
    end

    if (count != 3) begin
      $display("FAIL: count=%0d, expected 3", count);
      pass = 0;
    end

    // Sum of 0x10 + 0x20 + 0x30 = 0x60 = 96
    if (sum != 96) begin
      $display("FAIL: sum=%0d, expected 96", sum);
      pass = 0;
    end

    // Access last element
    temp = packets[$];
    if (temp.id != 3) begin
      $display("FAIL: last.id=%0d, expected 3", temp.id);
      pass = 0;
    end

    if (pass)
      $display("PASSED");
    else
      $display("FAILED");
    $finish;
  end
endmodule
