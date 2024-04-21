import Vector::*;
import FIFO::*;
import FixedPoint::*;

import AudioProcessorTypes::*;
import FilterCoefficients::*;
import Multiplier::*;

module mkFIRFilter (Vector#(tnp1, FixedPoint#(16, 16)) coeffs, AudioProcessor ifc);
    FIFO#(Sample) infifo <- mkFIFO();
    FIFO#(Sample) outfifo <- mkFIFO();

    Vector#(TSub#(tnp1, 1), Reg#(Sample)) r <- replicateM(mkReg(0));

    Vector#(tnp1, Multiplier) multiplier <- replicateM(mkMultiplier());

    rule mul_step;
        Integer numtaps = valueOf(TSub#(tnp1, 1));

        let sample = infifo.first();
        infifo.deq();

        r[0] <= sample;
        for (Integer i = 0; i < numtaps - 1; i = i + 1) begin
            r[i + 1] <= r[i];
        end 

        multiplier[0].putOperands(c[0], sample);
        for (Integer i = 0; i < numtaps; i = i + 1) begin
            multiplier[i + 1].putOperands(c[i + 1], r[i]);
        end
    endrule 

    rule acc_out ;
        Integer numtaps = valueOf(TSub#(tnp1, 1));
        Vector#(tnp1, FixedPoint#(16, 16)) acc;

        acc[0] <- multiplier[0].getResult();
        for (Integer i = 1; i < valueOf(tnp1); i = i + 1) begin
            let temp <- multiplier[i].getResult();
            acc[i] = acc[i - 1] + temp; 
        end

        outfifo.enq(fxptGetInt(acc[numtaps]));
    endrule

    method Action putSampleInput(Sample in);
        infifo.enq(in);
    endmethod

    method ActionValue#(Sample) getSampleOutput();
        outfifo.deq();
        return outfifo.first();
    endmethod

endmodule