import Ehr::*;
import Vector::*;

//////////////////
// Fifo interface 

interface Fifo#(numeric type n, type t);
    method Bool notFull;
    method Action enq(t x);
    method Bool notEmpty;
    method Action deq;
    method t first;
    method Action clear;
endinterface

/////////////////
// Conflict FIFO

// Exercise 1
// 循环队列
module mkMyConflictFifo( Fifo#(n, t) ) provisos (Bits#(t,tSz));

    Vector#(n, Reg#(t)) data <- replicateM(mkRegU);
    // enq pos
    Reg#(Bit#(TAdd#(TLog#(n), 1))) enqPos <- mkReg(0);
    // deq pos
    Reg#(Bit#(TAdd#(TLog#(n), 1))) deqPos <- mkReg(0);
    Reg#(Bool) full <- mkReg(False);
    Reg#(Bool) empty <- mkReg(True);
    
    method Bool notFull();
        return !full;
    endmethod

    method Action enq(t x) if (!full);
        let bitsN = fromInteger(valueOf(n));
        data[enqPos] <= x;
        enqPos <= (enqPos + 1) % bitsN;
        empty <= False;
        full <= ((enqPos + 1) % bitsN) == deqPos;
    endmethod

    method Bool notEmpty();
        return !empty;
    endmethod

    method Action deq() if (!empty);
        let bitsN = fromInteger(valueOf(n));
        deqPos <= (deqPos + 1) % bitsN;
        empty <= ((deqPos + 1) % bitsN == enqPos);
        // deq 之后就不可能 full 了
        full <= False;
    endmethod

    method t first() if (!empty);
        return data[deqPos];
    endmethod

    method Action clear();
        enqPos <= 0;
        deqPos <= 0;
        full <= False;
        empty <= True;
    endmethod
endmodule


//Exercise 2
// Pipeline FIFO
// Intended schedule:
//      {notEmpty, first, deq} < {notFull, enq} < clear
module mkMyPipelineFifo( Fifo#(n, t) ) provisos (Bits#(t,tSz));
    Vector#(n, Reg#(t)) data <- replicateM(mkRegU);
    // enq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) enqPos <- mkEhr(0);
    // deq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) deqPos <- mkEhr(0);
    Ehr#(3, Bool) full <- mkEhr(False);
    Ehr#(3, Bool) empty <- mkEhr(True);
    
    method Bool notFull();
        return !full[1];
    endmethod

    method Action enq(t x) if (!full[1]);
        let bitsN = fromInteger(valueOf(n));
        data[enqPos[1]] <= x;
        enqPos[1] <= (enqPos[1] + 1) % bitsN;
        empty[1] <= False;
        full[1] <= ((enqPos[1] + 1) % bitsN) == deqPos[1];
    endmethod

    method Bool notEmpty();
        return !empty[0];
    endmethod

    method Action deq() if (!empty[0]);
        let bitsN = fromInteger(valueOf(n));
        deqPos[0] <= (deqPos[0] + 1) % bitsN;
        empty[0] <= ((deqPos[0] + 1) % bitsN == enqPos[0]);
        // deq 之后就不可能 full 了
        full[0] <= False;
    endmethod

    method t first() if (!empty[0]);
        return data[deqPos[0]];
    endmethod

    method Action clear();
        enqPos[2] <= 0;
        deqPos[2] <= 0;
        full[2] <= False;
        empty[2] <= True;
    endmethod
endmodule

// Exercise 2
// Bypass FIFO
// Intended schedule:
//      {notFull, enq} < {notEmpty, first, deq} < clear
module mkMyBypassFifo( Fifo#(n, t) ) provisos (Bits#(t,tSz));
    Vector#(n, Reg#(t)) data <- replicateM(mkRegU);
    // enq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) enqPos <- mkEhr(0);
    // deq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) deqPos <- mkEhr(0);
    Ehr#(3, Bool) full <- mkEhr(False);
    Ehr#(3, Bool) empty <- mkEhr(True);
    
    method Bool notFull();
        return !full[0];
    endmethod

    method Action enq(t x) if (!full[0]);
        let bitsN = fromInteger(valueOf(n));
        data[enqPos[0]] <= x;
        enqPos[0] <= (enqPos[0] + 1) % bitsN;
        empty[0] <= False;
        full[0] <= ((enqPos[0] + 1) % bitsN) == deqPos[0];
    endmethod

    method Bool notEmpty();
        return !empty[1];
    endmethod

    method Action deq() if (!empty[1]);
        let bitsN = fromInteger(valueOf(n));
        deqPos[1] <= (deqPos[1] + 1) % bitsN;
        empty[1] <= ((deqPos[1] + 1) % bitsN == enqPos[1]);
        // deq 之后就不可能 full 了
        full[1] <= False;
    endmethod

    method t first() if (!empty[1]);
        return data[deqPos[1]];
    endmethod

    method Action clear();
        enqPos[2] <= 0;
        deqPos[2] <= 0;
        full[2] <= False;
        empty[2] <= True;
    endmethod
endmodule


// Exercise 3
// Exercise 4
// Conflict-free fifo
// Intended schedule:
//      {notFull, enq} CF {notEmpty, first, deq}
//      {notFull, enq, notEmpty, first, deq} < clear
module mkMyCFFifo( Fifo#(n, t) ) provisos (Bits#(t,tSz));
    Vector#(n, Ehr#(2, t)) data <- replicateM(mkEhr(?));
    // enq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) enqPos <- mkEhr(0);
    // deq pos
    Ehr#(3, Bit#(TAdd#(TLog#(n), 1))) deqPos <- mkEhr(0);
    Ehr#(3, Bool) full <- mkEhr(False);
    Ehr#(3, Bool) empty <- mkEhr(True);

    // 存在写入的 cf 的 function call 需要走 ehr
    Ehr#(2, Maybe#(t)) enq_request <- mkEhr(?);
    Ehr#(2, Bool) deq_request <- mkEhr(?);

    // 同时处理 enq deq 请求
    // 无视隐式 guard，并断言这条规则在每个时钟周期触发
    // 注意不要触发双写
    (* no_implicit_conditions, fire_when_enabled *)
    rule processing;
        let bitsN = fromInteger(valueOf(n));

        let nextEnqPos = isValid(enq_request[1]) ? (enqPos[1] + 1) % bitsN : enqPos[1];
        let nextDeqPos = deq_request[1] ? (deqPos[1] + 1) % bitsN : deqPos[1];

        if (isValid(enq_request[1])) begin
            data[enqPos[1]][1] <= fromMaybe(?, enq_request[1]);
        end

        enqPos[1] <= nextEnqPos;
        deqPos[1] <= nextDeqPos;
        
        if (nextEnqPos == nextDeqPos) begin
            if (isValid(enq_request[1]))
                full[1] <= True;
            else if(deq_request[1])
                empty[1] <= True;
        end
        else begin
            if(isValid(enq_request[1]))
                empty[1] <= False;
            if(deq_request[1])
                full[1] <= False;
        end

        enq_request[1] <= tagged Invalid;
        deq_request[1] <= False;
    endrule
    
    method Bool notFull();
        return !full[0];
    endmethod

    method Action enq(t x) if (!full[0]);
        enq_request[0] <= tagged Valid x;
    endmethod

    method Bool notEmpty();
        return !empty[0];
    endmethod

    method Action deq() if (!empty[0]);
        deq_request[0] <= True;
    endmethod

    method t first() if (!empty[0]);
        return data[deqPos[0]][0];
    endmethod

    method Action clear();
        enqPos[2] <= 0;
        deqPos[2] <= 0;
        full[2] <= False;
        empty[2] <= True;
    endmethod
endmodule

