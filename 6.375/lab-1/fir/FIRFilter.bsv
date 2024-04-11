import FIFO::*;
import FixedPoint::*;
import Vector::*;

import AudioProcessorTypes::*;
import FilterCoefficients::*;
import Multiplier::*;

module mkFIRFilter (AudioProcessor);
    FIFO#(Sample) infifo <- mkFIFO();
    FIFO#(Sample) outfifo <- mkFIFO();

    Vector#(9, Multiplier) mul <- replicateM(mkMultiplier());
    Vector#(8, Reg#(Sample)) r <- replicateM(mkReg(0));

    rule putOperands (True);
        Sample sample = infifo.first();
        infifo.deq();

        r[0] <= sample;
        for (Integer i = 0; i < 7; i = i+1) begin
            r[i+1] <= r[i];
        end

        mul[0].putOperands(c[0], sample);
        for (Integer i = 1; i < 9; i = i + 1) begin
            mul[i].putOperands(c[i], r[i - 1]);
        end
    endrule

    rule getResult (True);
        FixedPoint#(16, 16) accumulate <- mul[0].getResult();
        for (Integer i = 1; i < 9; i = i + 1) begin
            let x <- mul[i].getResult();
            accumulate = accumulate + x;
        end
        outfifo.enq(fxptGetInt(accumulate));
    endrule

    method Action putSampleInput(Sample in);
        infifo.enq(in);
    endmethod

    method ActionValue#(Sample) getSampleOutput();
        outfifo.deq();
        return outfifo.first();
    endmethod
endmodule