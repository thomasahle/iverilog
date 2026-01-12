// Test foreach element equality with extern task like I2S

class Transaction;
   rand bit[7:0] txSdLeftChannel[];
   constraint size_c { txSdLeftChannel.size() == 4; }
endclass

class Sequence;
   rand bit[7:0] txSdLeftChannelSeq[];
   Transaction i2sTransmitterTransaction;

   extern function new(string name = "Sequence");
   extern task body();
endclass

function Sequence::new(string name = "Sequence");
   i2sTransmitterTransaction = new();
   txSdLeftChannelSeq = new[4];
endfunction

task Sequence::body();
   // Set sequence values
   txSdLeftChannelSeq[0] = 8'hAA;
   txSdLeftChannelSeq[1] = 8'hBB;
   txSdLeftChannelSeq[2] = 8'hCC;
   txSdLeftChannelSeq[3] = 8'hDD;

   // This is the I2S AVIP pattern with extern task
   if (!i2sTransmitterTransaction.randomize() with {
      foreach(txSdLeftChannelSeq[i]) {
         txSdLeftChannel[i] == txSdLeftChannelSeq[i];
      }
   }) begin
      $display("ERROR: Randomization failed");
   end
endtask

module test;
   Sequence seq;

   initial begin
      seq = new();
      seq.body();

      $display("Left[0]=%h Left[1]=%h Left[2]=%h Left[3]=%h",
               seq.i2sTransmitterTransaction.txSdLeftChannel[0],
               seq.i2sTransmitterTransaction.txSdLeftChannel[1],
               seq.i2sTransmitterTransaction.txSdLeftChannel[2],
               seq.i2sTransmitterTransaction.txSdLeftChannel[3]);

      // Check values
      if (seq.i2sTransmitterTransaction.txSdLeftChannel[0] == 8'hAA &&
          seq.i2sTransmitterTransaction.txSdLeftChannel[1] == 8'hBB &&
          seq.i2sTransmitterTransaction.txSdLeftChannel[2] == 8'hCC &&
          seq.i2sTransmitterTransaction.txSdLeftChannel[3] == 8'hDD) begin
         $display("PASSED");
      end else begin
         $display("FAILED");
      end
   end
endmodule
