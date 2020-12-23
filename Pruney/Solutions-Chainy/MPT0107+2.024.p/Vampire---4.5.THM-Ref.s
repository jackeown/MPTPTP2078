%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:12 EST 2020

% Result     : Theorem 4.34s
% Output     : Refutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  118 (17979 expanded)
%              Number of leaves         :    9 (6147 expanded)
%              Depth                    :   43
%              Number of atoms          :  132 (20179 expanded)
%              Number of equality atoms :  102 (16398 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6501,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6490,f5048])).

fof(f5048,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X30,X28) = k4_xboole_0(X30,k2_xboole_0(X28,k4_xboole_0(X29,X29))) ),
    inference(superposition,[],[f4685,f4663])).

fof(f4663,plain,(
    ! [X19,X18] : k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,X19)) ),
    inference(forward_demodulation,[],[f4662,f1700])).

fof(f1700,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f1685,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1685,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),X7) ),
    inference(resolution,[],[f1646,f907])).

fof(f907,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1,X0),X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1646,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,X10)) ),
    inference(forward_demodulation,[],[f1645,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1645,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X10)))) ),
    inference(forward_demodulation,[],[f1644,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f43,f19])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f28,f19])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f13,f15,f15])).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1644,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X10))))) ),
    inference(forward_demodulation,[],[f1643,f86])).

fof(f86,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)) = k4_xboole_0(X7,k2_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f75,f19])).

fof(f75,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)) = k4_xboole_0(k4_xboole_0(X7,X8),X9) ),
    inference(superposition,[],[f19,f29])).

fof(f1643,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X10)),k4_xboole_0(X10,k2_xboole_0(X10,X10))))) ),
    inference(forward_demodulation,[],[f1642,f19])).

fof(f1642,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X10))),k4_xboole_0(X10,k2_xboole_0(X10,X10)))) ),
    inference(forward_demodulation,[],[f1602,f453])).

fof(f453,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3))) ),
    inference(forward_demodulation,[],[f370,f19])).

fof(f370,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3))) ),
    inference(superposition,[],[f46,f19])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f19,f28])).

fof(f1602,plain,(
    ! [X10,X11] : ~ r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,k2_xboole_0(X10,X10)),k4_xboole_0(X10,k2_xboole_0(X10,X10)))))) ),
    inference(superposition,[],[f533,f657])).

fof(f657,plain,(
    ! [X0] : k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0)))) ),
    inference(superposition,[],[f86,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(backward_demodulation,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f17,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f533,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X3,k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)))) ),
    inference(forward_demodulation,[],[f520,f19])).

fof(f520,plain,(
    ! [X2,X0,X3,X1] : ~ r2_hidden(X3,k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2))) ),
    inference(superposition,[],[f467,f19])).

fof(f467,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X0))) ),
    inference(forward_demodulation,[],[f390,f19])).

fof(f390,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) ),
    inference(superposition,[],[f160,f46])).

fof(f160,plain,(
    ! [X12,X13,X11] : ~ r2_hidden(X13,k4_xboole_0(X11,k2_xboole_0(X12,X11))) ),
    inference(subsumption_resolution,[],[f145,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f33,f19])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f145,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X13,k4_xboole_0(X11,k2_xboole_0(X12,X11)))
      | ~ r2_hidden(X13,k4_xboole_0(X11,X12)) ) ),
    inference(superposition,[],[f32,f109])).

fof(f109,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f108,f19])).

fof(f108,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f90,f71])).

fof(f71,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f29,f28])).

fof(f90,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f71,f28])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f4662,plain,(
    ! [X19,X18] : k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,k2_xboole_0(X19,X19))) ),
    inference(forward_demodulation,[],[f4661,f156])).

fof(f156,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(X12,X11)) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f155,f118])).

fof(f118,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f101,f19])).

fof(f101,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f19,f71])).

fof(f155,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f140,f19])).

fof(f140,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f109,f71])).

fof(f4661,plain,(
    ! [X19,X18] : k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,k2_xboole_0(X19,k4_xboole_0(X19,X19)))) ),
    inference(forward_demodulation,[],[f4611,f19])).

fof(f4611,plain,(
    ! [X19,X18] : k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(k4_xboole_0(X19,X19),k4_xboole_0(X19,X19))) ),
    inference(superposition,[],[f4577,f1953])).

fof(f1953,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f1702,f1685])).

fof(f1702,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X5))) ),
    inference(superposition,[],[f1685,f28])).

fof(f4577,plain,(
    ! [X25] : k2_xboole_0(X25,X25) = k2_xboole_0(X25,k4_xboole_0(X25,X25)) ),
    inference(forward_demodulation,[],[f4576,f35])).

fof(f4576,plain,(
    ! [X25] : k2_xboole_0(X25,k4_xboole_0(X25,X25)) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(X25,k2_xboole_0(X25,X25))) ),
    inference(forward_demodulation,[],[f4575,f19])).

fof(f4575,plain,(
    ! [X25] : k2_xboole_0(X25,k4_xboole_0(X25,X25)) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(k4_xboole_0(X25,X25),X25)) ),
    inference(forward_demodulation,[],[f4485,f4573])).

fof(f4573,plain,(
    ! [X24,X23] : k2_xboole_0(X23,k4_xboole_0(X24,X24)) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) ),
    inference(forward_demodulation,[],[f4572,f1832])).

fof(f1832,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(X20,X20)) ),
    inference(forward_demodulation,[],[f1831,f1700])).

fof(f1831,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(X20,k2_xboole_0(X20,k2_xboole_0(X21,X21)))) ),
    inference(forward_demodulation,[],[f1725,f19])).

fof(f1725,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(k4_xboole_0(X20,X20),k2_xboole_0(X21,X21))) ),
    inference(superposition,[],[f35,f1685])).

fof(f4572,plain,(
    ! [X24,X23] : k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) ),
    inference(forward_demodulation,[],[f4571,f1700])).

fof(f4571,plain,(
    ! [X24,X23] : k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,k2_xboole_0(X24,X23))) ),
    inference(forward_demodulation,[],[f4484,f19])).

fof(f4484,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(k4_xboole_0(X24,X24),X23)) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) ),
    inference(superposition,[],[f30,f1702])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f18,f17,f15])).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f4485,plain,(
    ! [X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(k4_xboole_0(X25,X25),X25)) = k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(X25,X25)) ),
    inference(superposition,[],[f30,f71])).

fof(f4685,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k4_xboole_0(X15,k2_xboole_0(X16,X16)) ),
    inference(forward_demodulation,[],[f4684,f4663])).

fof(f4684,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) ),
    inference(forward_demodulation,[],[f4683,f29])).

fof(f4683,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f4628,f4675])).

fof(f4675,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f4626,f3958])).

fof(f3958,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X12,X12)) ),
    inference(forward_demodulation,[],[f3870,f71])).

fof(f3870,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X12,X12)) ),
    inference(superposition,[],[f28,f2136])).

fof(f2136,plain,(
    ! [X28,X29,X27] : k4_xboole_0(X29,X29) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X27)),X27) ),
    inference(superposition,[],[f1961,f46])).

fof(f1961,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X8,k2_xboole_0(X9,X8)) = k4_xboole_0(X10,X10) ),
    inference(superposition,[],[f1702,f957])).

fof(f957,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X15,k2_xboole_0(X16,X15)) = k4_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X15)),X17) ),
    inference(resolution,[],[f907,f160])).

fof(f4626,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f46,f4577])).

fof(f4628,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) = k4_xboole_0(X15,k2_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16)))) ),
    inference(superposition,[],[f86,f4577])).

fof(f6490,plain,(
    ! [X0] : k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(X0,X0))) ),
    inference(superposition,[],[f6265,f19])).

fof(f6265,plain,(
    ! [X0] : k4_xboole_0(sK0,sK1) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f4621,f6028])).

fof(f6028,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,X20)) ),
    inference(forward_demodulation,[],[f6027,f4685])).

fof(f6027,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X20,X20))) ),
    inference(forward_demodulation,[],[f6026,f156])).

fof(f6026,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X20,k4_xboole_0(X20,X20)))) ),
    inference(forward_demodulation,[],[f5931,f19])).

fof(f5931,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(k4_xboole_0(X20,X20),k4_xboole_0(X20,X20))) ),
    inference(superposition,[],[f5630,f1953])).

fof(f5630,plain,(
    ! [X6] : k2_xboole_0(X6,X6) = k4_xboole_0(X6,k4_xboole_0(X6,X6)) ),
    inference(backward_demodulation,[],[f5385,f5629])).

fof(f5629,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,X20)) ),
    inference(forward_demodulation,[],[f5628,f4685])).

fof(f5628,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,k2_xboole_0(X20,X20))) ),
    inference(forward_demodulation,[],[f5627,f156])).

fof(f5627,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,k2_xboole_0(X20,k4_xboole_0(X20,X20)))) ),
    inference(forward_demodulation,[],[f5581,f19])).

fof(f5581,plain,(
    ! [X19,X20] : k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(k4_xboole_0(X20,X20),k4_xboole_0(X20,X20))) ),
    inference(superposition,[],[f4715,f1953])).

fof(f4715,plain,(
    ! [X23] : k2_xboole_0(X23,X23) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23)) ),
    inference(forward_demodulation,[],[f4714,f4202])).

fof(f4202,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X30,X30) = k2_xboole_0(k4_xboole_0(X30,k4_xboole_0(X30,X30)),k4_xboole_0(X31,k2_xboole_0(X32,X31))) ),
    inference(superposition,[],[f35,f2142])).

fof(f2142,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f1961,f109])).

fof(f4714,plain,(
    ! [X23] : k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(X23,k2_xboole_0(X23,X23))) ),
    inference(forward_demodulation,[],[f4713,f19])).

fof(f4713,plain,(
    ! [X23] : k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(k4_xboole_0(X23,X23),X23)) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23)) ),
    inference(forward_demodulation,[],[f4631,f29])).

fof(f4631,plain,(
    ! [X23] : k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(k4_xboole_0(X23,X23),X23)) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X23,X23)))) ),
    inference(superposition,[],[f30,f4577])).

fof(f5385,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X6),k4_xboole_0(X7,X7)) = k4_xboole_0(X6,k4_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f5343,f4685])).

fof(f5343,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X6,X6))) = k4_xboole_0(k2_xboole_0(X6,X6),k4_xboole_0(X7,X7)) ),
    inference(superposition,[],[f28,f4757])).

fof(f4757,plain,(
    ! [X57,X58] : k4_xboole_0(X58,X58) = k4_xboole_0(k2_xboole_0(X57,X57),X57) ),
    inference(superposition,[],[f4685,f1958])).

fof(f1958,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f1702,f1685])).

fof(f4621,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2196,f4577])).

fof(f2196,plain,(
    ! [X203] : k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X203,X203)) ),
    inference(superposition,[],[f36,f1961])).

fof(f36,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f34,f19])).

fof(f34,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f27,f29])).

fof(f27,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f12,f17,f15])).

fof(f12,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:00:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.58  % (19899)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.58  % (19904)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.59  % (19915)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.59  % (19907)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.59  % (19920)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.59  % (19912)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (19915)Refutation not found, incomplete strategy% (19915)------------------------------
% 0.22/0.59  % (19915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (19920)Refutation not found, incomplete strategy% (19920)------------------------------
% 0.22/0.59  % (19920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (19907)Refutation not found, incomplete strategy% (19907)------------------------------
% 0.22/0.59  % (19907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (19920)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (19920)Memory used [KB]: 10618
% 0.22/0.60  % (19920)Time elapsed: 0.152 s
% 0.22/0.60  % (19920)------------------------------
% 0.22/0.60  % (19920)------------------------------
% 0.22/0.60  % (19902)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.60  % (19903)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.60  % (19902)Refutation not found, incomplete strategy% (19902)------------------------------
% 0.22/0.60  % (19902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (19902)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (19902)Memory used [KB]: 6140
% 0.22/0.60  % (19902)Time elapsed: 0.165 s
% 0.22/0.60  % (19902)------------------------------
% 0.22/0.60  % (19902)------------------------------
% 0.22/0.60  % (19908)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  % (19908)Refutation not found, incomplete strategy% (19908)------------------------------
% 0.22/0.60  % (19908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (19908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (19908)Memory used [KB]: 10618
% 0.22/0.60  % (19908)Time elapsed: 0.164 s
% 0.22/0.60  % (19908)------------------------------
% 0.22/0.60  % (19908)------------------------------
% 0.22/0.61  % (19901)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.61  % (19898)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.61  % (19915)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (19915)Memory used [KB]: 10618
% 0.22/0.61  % (19915)Time elapsed: 0.149 s
% 0.22/0.61  % (19915)------------------------------
% 0.22/0.61  % (19915)------------------------------
% 0.22/0.61  % (19898)Refutation not found, incomplete strategy% (19898)------------------------------
% 0.22/0.61  % (19898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (19898)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (19898)Memory used [KB]: 1663
% 0.22/0.61  % (19898)Time elapsed: 0.171 s
% 0.22/0.61  % (19898)------------------------------
% 0.22/0.61  % (19898)------------------------------
% 0.22/0.61  % (19913)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.61  % (19907)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.61  
% 0.22/0.61  % (19907)Memory used [KB]: 10618
% 0.22/0.61  % (19907)Time elapsed: 0.151 s
% 0.22/0.61  % (19907)------------------------------
% 0.22/0.61  % (19907)------------------------------
% 0.22/0.61  % (19921)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.62  % (19921)Refutation not found, incomplete strategy% (19921)------------------------------
% 0.22/0.62  % (19921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.62  % (19921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.62  
% 0.22/0.62  % (19921)Memory used [KB]: 1663
% 0.22/0.62  % (19921)Time elapsed: 0.128 s
% 0.22/0.62  % (19921)------------------------------
% 0.22/0.62  % (19921)------------------------------
% 0.22/0.62  % (19900)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.88/0.63  % (19927)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.88/0.63  % (19926)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.88/0.63  % (19925)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.88/0.63  % (19905)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.88/0.63  % (19919)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.88/0.64  % (19906)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.20/0.64  % (19924)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.20/0.64  % (19900)Refutation not found, incomplete strategy% (19900)------------------------------
% 2.20/0.64  % (19900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (19900)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.64  
% 2.20/0.64  % (19900)Memory used [KB]: 10618
% 2.20/0.64  % (19900)Time elapsed: 0.203 s
% 2.20/0.64  % (19900)------------------------------
% 2.20/0.64  % (19900)------------------------------
% 2.20/0.64  % (19923)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.20/0.64  % (19923)Refutation not found, incomplete strategy% (19923)------------------------------
% 2.20/0.64  % (19923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (19923)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.64  
% 2.20/0.64  % (19923)Memory used [KB]: 6140
% 2.20/0.64  % (19923)Time elapsed: 0.202 s
% 2.20/0.64  % (19923)------------------------------
% 2.20/0.64  % (19923)------------------------------
% 2.22/0.64  % (19917)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.22/0.64  % (19922)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.22/0.64  % (19914)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.22/0.64  % (19916)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.22/0.65  % (19911)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.22/0.65  % (19909)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.22/0.65  % (19910)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.22/0.65  % (19918)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.22/0.65  % (19918)Refutation not found, incomplete strategy% (19918)------------------------------
% 2.22/0.65  % (19918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (19918)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.65  
% 2.22/0.65  % (19918)Memory used [KB]: 10618
% 2.22/0.65  % (19918)Time elapsed: 0.213 s
% 2.22/0.65  % (19918)------------------------------
% 2.22/0.65  % (19918)------------------------------
% 2.22/0.65  % (19919)Refutation not found, incomplete strategy% (19919)------------------------------
% 2.22/0.65  % (19919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (19919)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.65  
% 2.22/0.65  % (19919)Memory used [KB]: 1663
% 2.22/0.65  % (19919)Time elapsed: 0.213 s
% 2.22/0.65  % (19919)------------------------------
% 2.22/0.65  % (19919)------------------------------
% 2.22/0.66  % (19906)Refutation not found, incomplete strategy% (19906)------------------------------
% 2.22/0.66  % (19906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.66  % (19906)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.66  
% 2.22/0.66  % (19906)Memory used [KB]: 10618
% 2.22/0.66  % (19906)Time elapsed: 0.222 s
% 2.22/0.66  % (19906)------------------------------
% 2.22/0.66  % (19906)------------------------------
% 2.51/0.73  % (19975)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.51/0.73  % (19974)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.51/0.74  % (19967)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.51/0.75  % (19968)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.51/0.75  % (19965)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.74/0.75  % (19964)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.74/0.75  % (19964)Refutation not found, incomplete strategy% (19964)------------------------------
% 2.74/0.75  % (19964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.74/0.75  % (19964)Termination reason: Refutation not found, incomplete strategy
% 2.74/0.75  
% 2.74/0.75  % (19964)Memory used [KB]: 6140
% 2.74/0.75  % (19964)Time elapsed: 0.120 s
% 2.74/0.75  % (19964)------------------------------
% 2.74/0.75  % (19964)------------------------------
% 2.74/0.76  % (19966)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.74/0.77  % (19969)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.74/0.77  % (19970)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.74/0.78  % (19971)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.74/0.79  % (19973)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.74/0.80  % (19976)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.74/0.80  % (19973)Refutation not found, incomplete strategy% (19973)------------------------------
% 2.74/0.80  % (19973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.74/0.80  % (19973)Termination reason: Refutation not found, incomplete strategy
% 2.74/0.80  
% 2.74/0.80  % (19973)Memory used [KB]: 1663
% 2.74/0.80  % (19973)Time elapsed: 0.129 s
% 2.74/0.80  % (19973)------------------------------
% 2.74/0.80  % (19973)------------------------------
% 2.74/0.85  % (19903)Time limit reached!
% 2.74/0.85  % (19903)------------------------------
% 2.74/0.85  % (19903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.74/0.85  % (19903)Termination reason: Time limit
% 2.74/0.85  % (19903)Termination phase: Saturation
% 2.74/0.85  
% 2.74/0.85  % (19903)Memory used [KB]: 9083
% 2.74/0.85  % (19903)Time elapsed: 0.400 s
% 2.74/0.85  % (19903)------------------------------
% 2.74/0.85  % (19903)------------------------------
% 3.28/0.87  % (20014)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.66/0.94  % (20032)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.66/0.94  % (20032)Refutation not found, incomplete strategy% (20032)------------------------------
% 3.66/0.94  % (20032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.94  % (20032)Termination reason: Refutation not found, incomplete strategy
% 3.66/0.94  
% 3.66/0.94  % (20032)Memory used [KB]: 1663
% 3.66/0.94  % (20032)Time elapsed: 0.103 s
% 3.66/0.94  % (20032)------------------------------
% 3.66/0.94  % (20032)------------------------------
% 3.66/0.95  % (19899)Time limit reached!
% 3.66/0.95  % (19899)------------------------------
% 3.66/0.95  % (19899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.95  % (19899)Termination reason: Time limit
% 3.66/0.95  
% 3.66/0.95  % (19899)Memory used [KB]: 9978
% 3.66/0.95  % (19899)Time elapsed: 0.511 s
% 3.66/0.95  % (19899)------------------------------
% 3.66/0.95  % (19899)------------------------------
% 3.66/0.96  % (19910)Time limit reached!
% 3.66/0.96  % (19910)------------------------------
% 3.66/0.96  % (19910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.96  % (19910)Termination reason: Time limit
% 3.66/0.96  
% 3.66/0.96  % (19910)Memory used [KB]: 9338
% 3.66/0.96  % (19910)Time elapsed: 0.521 s
% 3.66/0.96  % (19910)------------------------------
% 3.66/0.96  % (19910)------------------------------
% 3.66/0.99  % (20058)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.99/1.03  % (19914)Time limit reached!
% 3.99/1.03  % (19914)------------------------------
% 3.99/1.03  % (19914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/1.04  % (19967)Time limit reached!
% 3.99/1.04  % (19967)------------------------------
% 3.99/1.04  % (19967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/1.04  % (19967)Termination reason: Time limit
% 3.99/1.04  % (19967)Termination phase: Saturation
% 3.99/1.04  
% 3.99/1.04  % (19967)Memory used [KB]: 8187
% 3.99/1.04  % (19967)Time elapsed: 0.400 s
% 3.99/1.04  % (19967)------------------------------
% 3.99/1.04  % (19967)------------------------------
% 3.99/1.04  % (19914)Termination reason: Time limit
% 3.99/1.04  % (19914)Termination phase: Saturation
% 3.99/1.04  
% 3.99/1.04  % (19914)Memory used [KB]: 17654
% 3.99/1.04  % (19914)Time elapsed: 0.600 s
% 3.99/1.04  % (19914)------------------------------
% 3.99/1.04  % (19914)------------------------------
% 3.99/1.05  % (19926)Time limit reached!
% 3.99/1.05  % (19926)------------------------------
% 3.99/1.05  % (19926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/1.05  % (19926)Termination reason: Time limit
% 3.99/1.05  
% 3.99/1.05  % (19926)Memory used [KB]: 9978
% 3.99/1.05  % (19926)Time elapsed: 0.618 s
% 3.99/1.05  % (19926)------------------------------
% 3.99/1.05  % (19926)------------------------------
% 4.34/1.06  % (19968)Time limit reached!
% 4.34/1.06  % (19968)------------------------------
% 4.34/1.06  % (19968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.06  % (19968)Termination reason: Time limit
% 4.34/1.06  
% 4.34/1.06  % (19968)Memory used [KB]: 14200
% 4.34/1.06  % (19968)Time elapsed: 0.416 s
% 4.34/1.06  % (19968)------------------------------
% 4.34/1.06  % (19968)------------------------------
% 4.34/1.06  % (20119)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.34/1.07  % (20118)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.34/1.08  % (20123)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.34/1.08  % (20123)Refutation not found, incomplete strategy% (20123)------------------------------
% 4.34/1.08  % (20123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.08  % (20123)Termination reason: Refutation not found, incomplete strategy
% 4.34/1.08  
% 4.34/1.08  % (20123)Memory used [KB]: 6140
% 4.34/1.08  % (20123)Time elapsed: 0.112 s
% 4.34/1.08  % (20123)------------------------------
% 4.34/1.08  % (20123)------------------------------
% 4.34/1.11  % (19905)Time limit reached!
% 4.34/1.11  % (19905)------------------------------
% 4.34/1.11  % (19905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.11  % (19905)Termination reason: Time limit
% 4.34/1.11  
% 4.34/1.11  % (19905)Memory used [KB]: 10874
% 4.34/1.11  % (19905)Time elapsed: 0.613 s
% 4.34/1.11  % (19905)------------------------------
% 4.34/1.11  % (19905)------------------------------
% 4.34/1.11  % (19904)Refutation found. Thanks to Tanya!
% 4.34/1.11  % SZS status Theorem for theBenchmark
% 4.34/1.11  % SZS output start Proof for theBenchmark
% 4.34/1.11  fof(f6501,plain,(
% 4.34/1.11    $false),
% 4.34/1.11    inference(subsumption_resolution,[],[f6490,f5048])).
% 4.34/1.11  fof(f5048,plain,(
% 4.34/1.11    ( ! [X30,X28,X29] : (k4_xboole_0(X30,X28) = k4_xboole_0(X30,k2_xboole_0(X28,k4_xboole_0(X29,X29)))) )),
% 4.34/1.11    inference(superposition,[],[f4685,f4663])).
% 4.34/1.11  fof(f4663,plain,(
% 4.34/1.11    ( ! [X19,X18] : (k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,X19))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4662,f1700])).
% 4.34/1.11  fof(f1700,plain,(
% 4.34/1.11    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 4.34/1.11    inference(superposition,[],[f1685,f19])).
% 4.34/1.11  fof(f19,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f5])).
% 4.34/1.11  fof(f5,axiom,(
% 4.34/1.11    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.34/1.11  fof(f1685,plain,(
% 4.34/1.11    ( ! [X6,X7] : (k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),X7)) )),
% 4.34/1.11    inference(resolution,[],[f1646,f907])).
% 4.34/1.11  fof(f907,plain,(
% 4.34/1.11    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) )),
% 4.34/1.11    inference(factoring,[],[f21])).
% 4.34/1.11  fof(f21,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 4.34/1.11    inference(cnf_transformation,[],[f2])).
% 4.34/1.11  fof(f2,axiom,(
% 4.34/1.11    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.34/1.11  fof(f1646,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,X10))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1645,f29])).
% 4.34/1.11  fof(f29,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.34/1.11    inference(definition_unfolding,[],[f16,f15])).
% 4.34/1.11  fof(f15,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f7])).
% 4.34/1.11  fof(f7,axiom,(
% 4.34/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.34/1.11  fof(f16,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f6])).
% 4.34/1.11  fof(f6,axiom,(
% 4.34/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.34/1.11  fof(f1645,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X10))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1644,f54])).
% 4.34/1.11  fof(f54,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f43,f19])).
% 4.34/1.11  fof(f43,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 4.34/1.11    inference(superposition,[],[f28,f19])).
% 4.34/1.11  fof(f28,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.34/1.11    inference(definition_unfolding,[],[f13,f15,f15])).
% 4.34/1.11  fof(f13,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.34/1.11    inference(cnf_transformation,[],[f1])).
% 4.34/1.11  fof(f1,axiom,(
% 4.34/1.11    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.34/1.11  fof(f1644,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X10)))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1643,f86])).
% 4.34/1.11  fof(f86,plain,(
% 4.34/1.11    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)) = k4_xboole_0(X7,k2_xboole_0(X8,X9))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f75,f19])).
% 4.34/1.11  fof(f75,plain,(
% 4.34/1.11    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)) = k4_xboole_0(k4_xboole_0(X7,X8),X9)) )),
% 4.34/1.11    inference(superposition,[],[f19,f29])).
% 4.34/1.11  fof(f1643,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X10)),k4_xboole_0(X10,k2_xboole_0(X10,X10)))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1642,f19])).
% 4.34/1.11  fof(f1642,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X10))),k4_xboole_0(X10,k2_xboole_0(X10,X10))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1602,f453])).
% 4.34/1.11  fof(f453,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f370,f19])).
% 4.34/1.11  fof(f370,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))),X3) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X3)))) )),
% 4.34/1.11    inference(superposition,[],[f46,f19])).
% 4.34/1.11  fof(f46,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 4.34/1.11    inference(superposition,[],[f19,f28])).
% 4.34/1.11  fof(f1602,plain,(
% 4.34/1.11    ( ! [X10,X11] : (~r2_hidden(X11,k4_xboole_0(X10,k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,k2_xboole_0(X10,X10)),k4_xboole_0(X10,k2_xboole_0(X10,X10))))))) )),
% 4.34/1.11    inference(superposition,[],[f533,f657])).
% 4.34/1.11  fof(f657,plain,(
% 4.34/1.11    ( ! [X0] : (k4_xboole_0(X0,k2_xboole_0(X0,X0)) = k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X0))))) )),
% 4.34/1.11    inference(superposition,[],[f86,f35])).
% 4.34/1.11  fof(f35,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 4.34/1.11    inference(backward_demodulation,[],[f26,f19])).
% 4.34/1.11  fof(f26,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 4.34/1.11    inference(definition_unfolding,[],[f14,f17])).
% 4.34/1.11  fof(f17,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f3])).
% 4.34/1.11  fof(f3,axiom,(
% 4.34/1.11    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 4.34/1.11  fof(f14,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f8])).
% 4.34/1.11  fof(f8,axiom,(
% 4.34/1.11    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.34/1.11  fof(f533,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f520,f19])).
% 4.34/1.11  fof(f520,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)))) )),
% 4.34/1.11    inference(superposition,[],[f467,f19])).
% 4.34/1.11  fof(f467,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X1,X0),X0)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f390,f19])).
% 4.34/1.11  fof(f390,plain,(
% 4.34/1.11    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0))) )),
% 4.34/1.11    inference(superposition,[],[f160,f46])).
% 4.34/1.11  fof(f160,plain,(
% 4.34/1.11    ( ! [X12,X13,X11] : (~r2_hidden(X13,k4_xboole_0(X11,k2_xboole_0(X12,X11)))) )),
% 4.34/1.11    inference(subsumption_resolution,[],[f145,f38])).
% 4.34/1.11  fof(f38,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k2_xboole_0(X1,X2))) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 4.34/1.11    inference(superposition,[],[f33,f19])).
% 4.34/1.11  fof(f33,plain,(
% 4.34/1.11    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 4.34/1.11    inference(equality_resolution,[],[f23])).
% 4.34/1.11  fof(f23,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.34/1.11    inference(cnf_transformation,[],[f2])).
% 4.34/1.11  fof(f145,plain,(
% 4.34/1.11    ( ! [X12,X13,X11] : (~r2_hidden(X13,k4_xboole_0(X11,k2_xboole_0(X12,X11))) | ~r2_hidden(X13,k4_xboole_0(X11,X12))) )),
% 4.34/1.11    inference(superposition,[],[f32,f109])).
% 4.34/1.11  fof(f109,plain,(
% 4.34/1.11    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f108,f19])).
% 4.34/1.11  fof(f108,plain,(
% 4.34/1.11    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f90,f71])).
% 4.34/1.11  fof(f71,plain,(
% 4.34/1.11    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 4.34/1.11    inference(superposition,[],[f29,f28])).
% 4.34/1.11  fof(f90,plain,(
% 4.34/1.11    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))))) )),
% 4.34/1.11    inference(superposition,[],[f71,f28])).
% 4.34/1.11  fof(f32,plain,(
% 4.34/1.11    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 4.34/1.11    inference(equality_resolution,[],[f24])).
% 4.34/1.11  fof(f24,plain,(
% 4.34/1.11    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.34/1.11    inference(cnf_transformation,[],[f2])).
% 4.34/1.11  fof(f4662,plain,(
% 4.34/1.11    ( ! [X19,X18] : (k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,k2_xboole_0(X19,X19)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4661,f156])).
% 4.34/1.11  fof(f156,plain,(
% 4.34/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(X12,X11)) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X12)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f155,f118])).
% 4.34/1.11  fof(f118,plain,(
% 4.34/1.11    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f101,f19])).
% 4.34/1.11  fof(f101,plain,(
% 4.34/1.11    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 4.34/1.11    inference(superposition,[],[f19,f71])).
% 4.34/1.11  fof(f155,plain,(
% 4.34/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) = k4_xboole_0(X11,k2_xboole_0(X12,k4_xboole_0(X11,X12)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f140,f19])).
% 4.34/1.11  fof(f140,plain,(
% 4.34/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X11)) = k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) )),
% 4.34/1.11    inference(superposition,[],[f109,f71])).
% 4.34/1.11  fof(f4661,plain,(
% 4.34/1.11    ( ! [X19,X18] : (k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(X19,k2_xboole_0(X19,k4_xboole_0(X19,X19))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4611,f19])).
% 4.34/1.11  fof(f4611,plain,(
% 4.34/1.11    ( ! [X19,X18] : (k2_xboole_0(X18,X18) = k2_xboole_0(X18,k4_xboole_0(k4_xboole_0(X19,X19),k4_xboole_0(X19,X19)))) )),
% 4.34/1.11    inference(superposition,[],[f4577,f1953])).
% 4.34/1.11  fof(f1953,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 4.34/1.11    inference(superposition,[],[f1702,f1685])).
% 4.34/1.11  fof(f1702,plain,(
% 4.34/1.11    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X5,X5)))) )),
% 4.34/1.11    inference(superposition,[],[f1685,f28])).
% 4.34/1.11  fof(f4577,plain,(
% 4.34/1.11    ( ! [X25] : (k2_xboole_0(X25,X25) = k2_xboole_0(X25,k4_xboole_0(X25,X25))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4576,f35])).
% 4.34/1.11  fof(f4576,plain,(
% 4.34/1.11    ( ! [X25] : (k2_xboole_0(X25,k4_xboole_0(X25,X25)) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(X25,k2_xboole_0(X25,X25)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4575,f19])).
% 4.34/1.11  fof(f4575,plain,(
% 4.34/1.11    ( ! [X25] : (k2_xboole_0(X25,k4_xboole_0(X25,X25)) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(k4_xboole_0(X25,X25),X25))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4485,f4573])).
% 4.34/1.11  fof(f4573,plain,(
% 4.34/1.11    ( ! [X24,X23] : (k2_xboole_0(X23,k4_xboole_0(X24,X24)) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4572,f1832])).
% 4.34/1.11  fof(f1832,plain,(
% 4.34/1.11    ( ! [X21,X20] : (k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(X20,X20))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1831,f1700])).
% 4.34/1.11  fof(f1831,plain,(
% 4.34/1.11    ( ! [X21,X20] : (k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(X20,k2_xboole_0(X20,k2_xboole_0(X21,X21))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f1725,f19])).
% 4.34/1.11  fof(f1725,plain,(
% 4.34/1.11    ( ! [X21,X20] : (k2_xboole_0(X21,k4_xboole_0(X20,X20)) = k2_xboole_0(k4_xboole_0(X21,k4_xboole_0(X20,X20)),k4_xboole_0(k4_xboole_0(X20,X20),k2_xboole_0(X21,X21)))) )),
% 4.34/1.11    inference(superposition,[],[f35,f1685])).
% 4.34/1.11  fof(f4572,plain,(
% 4.34/1.11    ( ! [X24,X23] : (k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4571,f1700])).
% 4.34/1.11  fof(f4571,plain,(
% 4.34/1.11    ( ! [X24,X23] : (k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,k2_xboole_0(X24,X23)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4484,f19])).
% 4.34/1.11  fof(f4484,plain,(
% 4.34/1.11    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(k4_xboole_0(X24,X24),X23)) = k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X24,X24)),k4_xboole_0(X24,X24))) )),
% 4.34/1.11    inference(superposition,[],[f30,f1702])).
% 4.34/1.11  fof(f30,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.34/1.11    inference(definition_unfolding,[],[f18,f17,f15])).
% 4.34/1.11  fof(f18,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.34/1.11    inference(cnf_transformation,[],[f4])).
% 4.34/1.11  fof(f4,axiom,(
% 4.34/1.11    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 4.34/1.11  fof(f4485,plain,(
% 4.34/1.11    ( ! [X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(k4_xboole_0(X25,X25),X25)) = k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X25)),k4_xboole_0(X25,X25))) )),
% 4.34/1.11    inference(superposition,[],[f30,f71])).
% 4.34/1.11  fof(f4685,plain,(
% 4.34/1.11    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k4_xboole_0(X15,k2_xboole_0(X16,X16))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4684,f4663])).
% 4.34/1.11  fof(f4684,plain,(
% 4.34/1.11    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16)))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4683,f29])).
% 4.34/1.11  fof(f4683,plain,(
% 4.34/1.11    ( ! [X15,X16] : (k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4628,f4675])).
% 4.34/1.11  fof(f4675,plain,(
% 4.34/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4626,f3958])).
% 4.34/1.11  fof(f3958,plain,(
% 4.34/1.11    ( ! [X12,X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X12,X12))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f3870,f71])).
% 4.34/1.11  fof(f3870,plain,(
% 4.34/1.11    ( ! [X12,X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X12,X12))) )),
% 4.34/1.11    inference(superposition,[],[f28,f2136])).
% 4.34/1.11  fof(f2136,plain,(
% 4.34/1.11    ( ! [X28,X29,X27] : (k4_xboole_0(X29,X29) = k4_xboole_0(k4_xboole_0(X28,k4_xboole_0(X28,X27)),X27)) )),
% 4.34/1.11    inference(superposition,[],[f1961,f46])).
% 4.34/1.11  fof(f1961,plain,(
% 4.34/1.11    ( ! [X10,X8,X9] : (k4_xboole_0(X8,k2_xboole_0(X9,X8)) = k4_xboole_0(X10,X10)) )),
% 4.34/1.11    inference(superposition,[],[f1702,f957])).
% 4.34/1.11  fof(f957,plain,(
% 4.34/1.11    ( ! [X17,X15,X16] : (k4_xboole_0(X15,k2_xboole_0(X16,X15)) = k4_xboole_0(k4_xboole_0(X15,k2_xboole_0(X16,X15)),X17)) )),
% 4.34/1.11    inference(resolution,[],[f907,f160])).
% 4.34/1.11  fof(f4626,plain,(
% 4.34/1.11    ( ! [X12,X11] : (k4_xboole_0(X11,k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12))) = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),k4_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12)))) )),
% 4.34/1.11    inference(superposition,[],[f46,f4577])).
% 4.34/1.11  fof(f4628,plain,(
% 4.34/1.11    ( ! [X15,X16] : (k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) = k4_xboole_0(X15,k2_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X15,k4_xboole_0(X15,X16))))) )),
% 4.34/1.11    inference(superposition,[],[f86,f4577])).
% 4.34/1.11  fof(f6490,plain,(
% 4.34/1.11    ( ! [X0] : (k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(X0,X0)))) )),
% 4.34/1.11    inference(superposition,[],[f6265,f19])).
% 4.34/1.11  fof(f6265,plain,(
% 4.34/1.11    ( ! [X0] : (k4_xboole_0(sK0,sK1) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X0,X0))) )),
% 4.34/1.11    inference(superposition,[],[f4621,f6028])).
% 4.34/1.11  fof(f6028,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,X20))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f6027,f4685])).
% 4.34/1.11  fof(f6027,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X20,X20)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f6026,f156])).
% 4.34/1.11  fof(f6026,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X20,k4_xboole_0(X20,X20))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f5931,f19])).
% 4.34/1.11  fof(f5931,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(X19,k4_xboole_0(k4_xboole_0(X20,X20),k4_xboole_0(X20,X20)))) )),
% 4.34/1.11    inference(superposition,[],[f5630,f1953])).
% 4.34/1.11  fof(f5630,plain,(
% 4.34/1.11    ( ! [X6] : (k2_xboole_0(X6,X6) = k4_xboole_0(X6,k4_xboole_0(X6,X6))) )),
% 4.34/1.11    inference(backward_demodulation,[],[f5385,f5629])).
% 4.34/1.11  fof(f5629,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,X20))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f5628,f4685])).
% 4.34/1.11  fof(f5628,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,k2_xboole_0(X20,X20)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f5627,f156])).
% 4.34/1.11  fof(f5627,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(X20,k2_xboole_0(X20,k4_xboole_0(X20,X20))))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f5581,f19])).
% 4.34/1.11  fof(f5581,plain,(
% 4.34/1.11    ( ! [X19,X20] : (k2_xboole_0(X19,X19) = k4_xboole_0(k2_xboole_0(X19,X19),k4_xboole_0(k4_xboole_0(X20,X20),k4_xboole_0(X20,X20)))) )),
% 4.34/1.11    inference(superposition,[],[f4715,f1953])).
% 4.34/1.11  fof(f4715,plain,(
% 4.34/1.11    ( ! [X23] : (k2_xboole_0(X23,X23) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4714,f4202])).
% 4.34/1.11  fof(f4202,plain,(
% 4.34/1.11    ( ! [X30,X31,X32] : (k2_xboole_0(X30,X30) = k2_xboole_0(k4_xboole_0(X30,k4_xboole_0(X30,X30)),k4_xboole_0(X31,k2_xboole_0(X32,X31)))) )),
% 4.34/1.11    inference(superposition,[],[f35,f2142])).
% 4.34/1.11  fof(f2142,plain,(
% 4.34/1.11    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 4.34/1.11    inference(superposition,[],[f1961,f109])).
% 4.34/1.11  fof(f4714,plain,(
% 4.34/1.11    ( ! [X23] : (k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23)) = k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(X23,k2_xboole_0(X23,X23)))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4713,f19])).
% 4.34/1.11  fof(f4713,plain,(
% 4.34/1.11    ( ! [X23] : (k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(k4_xboole_0(X23,X23),X23)) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,X23))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f4631,f29])).
% 4.34/1.11  fof(f4631,plain,(
% 4.34/1.11    ( ! [X23] : (k2_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,X23)),k4_xboole_0(k4_xboole_0(X23,X23),X23)) = k4_xboole_0(k2_xboole_0(X23,X23),k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X23,X23))))) )),
% 4.34/1.11    inference(superposition,[],[f30,f4577])).
% 4.34/1.11  fof(f5385,plain,(
% 4.34/1.11    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X6),k4_xboole_0(X7,X7)) = k4_xboole_0(X6,k4_xboole_0(X6,X6))) )),
% 4.34/1.11    inference(forward_demodulation,[],[f5343,f4685])).
% 4.34/1.11  fof(f5343,plain,(
% 4.34/1.11    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X6,X6))) = k4_xboole_0(k2_xboole_0(X6,X6),k4_xboole_0(X7,X7))) )),
% 4.34/1.11    inference(superposition,[],[f28,f4757])).
% 4.34/1.11  fof(f4757,plain,(
% 4.34/1.11    ( ! [X57,X58] : (k4_xboole_0(X58,X58) = k4_xboole_0(k2_xboole_0(X57,X57),X57)) )),
% 4.34/1.11    inference(superposition,[],[f4685,f1958])).
% 4.34/1.11  fof(f1958,plain,(
% 4.34/1.11    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(X1,X1)) )),
% 4.34/1.11    inference(superposition,[],[f1702,f1685])).
% 4.34/1.11  fof(f4621,plain,(
% 4.34/1.11    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.34/1.11    inference(superposition,[],[f2196,f4577])).
% 4.34/1.11  fof(f2196,plain,(
% 4.34/1.11    ( ! [X203] : (k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X203,X203))) )),
% 4.34/1.11    inference(superposition,[],[f36,f1961])).
% 4.34/1.11  fof(f36,plain,(
% 4.34/1.11    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 4.34/1.11    inference(backward_demodulation,[],[f34,f19])).
% 4.34/1.11  fof(f34,plain,(
% 4.34/1.11    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 4.34/1.11    inference(backward_demodulation,[],[f27,f29])).
% 4.34/1.11  fof(f27,plain,(
% 4.34/1.11    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 4.34/1.11    inference(definition_unfolding,[],[f12,f17,f15])).
% 4.34/1.11  fof(f12,plain,(
% 4.34/1.11    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.34/1.11    inference(cnf_transformation,[],[f11])).
% 4.34/1.11  fof(f11,plain,(
% 4.34/1.11    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.34/1.11    inference(ennf_transformation,[],[f10])).
% 4.34/1.11  fof(f10,negated_conjecture,(
% 4.34/1.11    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.34/1.11    inference(negated_conjecture,[],[f9])).
% 4.34/1.11  fof(f9,conjecture,(
% 4.34/1.11    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.34/1.11    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.34/1.11  % SZS output end Proof for theBenchmark
% 4.34/1.11  % (19904)------------------------------
% 4.34/1.11  % (19904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.11  % (19904)Termination reason: Refutation
% 4.34/1.11  
% 4.34/1.11  % (19904)Memory used [KB]: 12025
% 4.34/1.11  % (19904)Time elapsed: 0.655 s
% 4.34/1.11  % (19904)------------------------------
% 4.34/1.11  % (19904)------------------------------
% 4.34/1.12  % (19897)Success in time 0.74 s
%------------------------------------------------------------------------------
