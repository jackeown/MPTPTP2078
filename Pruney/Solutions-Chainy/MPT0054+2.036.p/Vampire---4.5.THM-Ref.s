%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:02 EST 2020

% Result     : Theorem 36.49s
% Output     : Refutation 36.49s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 219 expanded)
%              Number of leaves         :   14 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :   95 ( 244 expanded)
%              Number of equality atoms :   70 ( 195 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141465,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f141464])).

fof(f141464,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f19,f135417])).

fof(f135417,plain,(
    ! [X64,X63] : k4_xboole_0(X63,X64) = k4_xboole_0(X63,k3_xboole_0(X63,X64)) ),
    inference(forward_demodulation,[],[f135022,f60369])).

fof(f60369,plain,(
    ! [X151,X149,X150] : k4_xboole_0(X151,X149) = k4_xboole_0(k4_xboole_0(X151,X149),k3_xboole_0(X150,X149)) ),
    inference(superposition,[],[f1392,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1392,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X29,k2_xboole_0(X30,X28)) = k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28) ),
    inference(forward_demodulation,[],[f1391,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1391,plain,(
    ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28) = k4_xboole_0(k4_xboole_0(X29,X30),X28) ),
    inference(forward_demodulation,[],[f1348,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1348,plain,(
    ! [X30,X28,X29] : k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28) = k4_xboole_0(k2_xboole_0(X28,k4_xboole_0(X29,X30)),X28) ),
    inference(superposition,[],[f50,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f135022,plain,(
    ! [X64,X63] : k4_xboole_0(k4_xboole_0(X63,X64),k3_xboole_0(X63,X64)) = k4_xboole_0(X63,k3_xboole_0(X63,X64)) ),
    inference(superposition,[],[f26,f133573])).

fof(f133573,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f133572,f25])).

fof(f133572,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f133571,f23])).

fof(f133571,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f133435,f864])).

fof(f864,plain,(
    ! [X33,X34,X32] : k2_xboole_0(X34,X32) = k2_xboole_0(k4_xboole_0(X32,X33),k2_xboole_0(X34,X32)) ),
    inference(superposition,[],[f121,f161])).

fof(f161,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f45,f23])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f121,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f133435,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(resolution,[],[f133280,f2184])).

fof(f2184,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | k2_xboole_0(X0,X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1)) ) ),
    inference(forward_demodulation,[],[f2183,f269])).

fof(f269,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k2_xboole_0(X9,X10)) = k2_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10))) ),
    inference(forward_demodulation,[],[f268,f31])).

fof(f268,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10))) ),
    inference(forward_demodulation,[],[f252,f31])).

fof(f252,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X9,X8),X10)) ),
    inference(superposition,[],[f31,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f56,f27])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f26])).

fof(f2183,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X2) = k2_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X0,X1)))
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2) ) ),
    inference(forward_demodulation,[],[f2168,f121])).

fof(f2168,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | k2_xboole_0(X0,X2) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ) ),
    inference(superposition,[],[f66,f50])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | k2_xboole_0(X1,X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f133280,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k3_xboole_0(X10,X11)) ),
    inference(superposition,[],[f4327,f59980])).

fof(f59980,plain,(
    ! [X52,X51] : k2_xboole_0(k4_xboole_0(X52,k4_xboole_0(X52,X51)),X51) = X51 ),
    inference(superposition,[],[f72,f59737])).

fof(f59737,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = X10 ),
    inference(forward_demodulation,[],[f59736,f161])).

fof(f59736,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) ),
    inference(forward_demodulation,[],[f59402,f3360])).

fof(f3360,plain,(
    ! [X41,X42,X40] : k2_xboole_0(X41,k4_xboole_0(X42,X40)) = k2_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X40,X41))) ),
    inference(forward_demodulation,[],[f3304,f1322])).

fof(f1322,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f98,f23])).

fof(f3304,plain,(
    ! [X41,X42,X40] : k2_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X40,X41))) = k2_xboole_0(X41,k4_xboole_0(X42,k2_xboole_0(X41,X40))) ),
    inference(superposition,[],[f98,f262])).

fof(f262,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f244,f231])).

fof(f231,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f45,f50])).

fof(f244,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f59,f27])).

fof(f59402,plain,(
    ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X10))) ),
    inference(superposition,[],[f1381,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f27])).

fof(f1381,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f1380,f98])).

fof(f1380,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f1335,f919])).

fof(f919,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k2_xboole_0(X37,X38),X36) = k4_xboole_0(k2_xboole_0(X38,k2_xboole_0(X36,X37)),X36) ),
    inference(superposition,[],[f50,f121])).

fof(f1335,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ),
    inference(superposition,[],[f98,f26])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f39,f23])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f4327,plain,(
    ! [X59,X60,X58] : r1_tarski(k4_xboole_0(X58,X59),k3_xboole_0(X58,k2_xboole_0(k4_xboole_0(X58,X59),X60))) ),
    inference(forward_demodulation,[],[f4277,f22])).

fof(f4277,plain,(
    ! [X59,X60,X58] : r1_tarski(k4_xboole_0(X58,X59),k3_xboole_0(k2_xboole_0(k4_xboole_0(X58,X59),X60),X58)) ),
    inference(superposition,[],[f495,f165])).

fof(f165,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f24,f45])).

fof(f495,plain,(
    ! [X26,X27,X25] : r1_tarski(k3_xboole_0(X25,X27),k3_xboole_0(k2_xboole_0(X25,X26),X27)) ),
    inference(superposition,[],[f33,f80])).

fof(f80,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(X6,X8) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:39:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (4698)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (4699)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (4703)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (4701)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.44  % (4697)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.46  % (4696)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.46  % (4694)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.46  % (4705)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.47  % (4700)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.47  % (4695)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.48  % (4704)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.48  % (4702)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 5.39/1.03  % (4695)Time limit reached!
% 5.39/1.03  % (4695)------------------------------
% 5.39/1.03  % (4695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.39/1.03  % (4695)Termination reason: Time limit
% 5.39/1.03  % (4695)Termination phase: Saturation
% 5.39/1.03  
% 5.39/1.03  % (4695)Memory used [KB]: 22643
% 5.39/1.03  % (4695)Time elapsed: 0.600 s
% 5.39/1.03  % (4695)------------------------------
% 5.39/1.03  % (4695)------------------------------
% 8.21/1.45  % (4694)Time limit reached!
% 8.21/1.45  % (4694)------------------------------
% 8.21/1.45  % (4694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.21/1.45  % (4694)Termination reason: Time limit
% 8.21/1.45  % (4694)Termination phase: Saturation
% 8.21/1.45  
% 8.21/1.45  % (4694)Memory used [KB]: 39786
% 8.21/1.45  % (4694)Time elapsed: 1.0000 s
% 8.21/1.45  % (4694)------------------------------
% 8.21/1.45  % (4694)------------------------------
% 36.49/4.97  % (4697)Refutation found. Thanks to Tanya!
% 36.49/4.97  % SZS status Theorem for theBenchmark
% 36.49/4.97  % SZS output start Proof for theBenchmark
% 36.49/4.97  fof(f141465,plain,(
% 36.49/4.97    $false),
% 36.49/4.97    inference(trivial_inequality_removal,[],[f141464])).
% 36.49/4.97  fof(f141464,plain,(
% 36.49/4.97    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 36.49/4.97    inference(superposition,[],[f19,f135417])).
% 36.49/4.97  fof(f135417,plain,(
% 36.49/4.97    ( ! [X64,X63] : (k4_xboole_0(X63,X64) = k4_xboole_0(X63,k3_xboole_0(X63,X64))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f135022,f60369])).
% 36.49/4.97  fof(f60369,plain,(
% 36.49/4.97    ( ! [X151,X149,X150] : (k4_xboole_0(X151,X149) = k4_xboole_0(k4_xboole_0(X151,X149),k3_xboole_0(X150,X149))) )),
% 36.49/4.97    inference(superposition,[],[f1392,f41])).
% 36.49/4.97  fof(f41,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 36.49/4.97    inference(superposition,[],[f25,f22])).
% 36.49/4.97  fof(f22,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f2])).
% 36.49/4.97  fof(f2,axiom,(
% 36.49/4.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 36.49/4.97  fof(f25,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 36.49/4.97    inference(cnf_transformation,[],[f7])).
% 36.49/4.97  fof(f7,axiom,(
% 36.49/4.97    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 36.49/4.97  fof(f1392,plain,(
% 36.49/4.97    ( ! [X30,X28,X29] : (k4_xboole_0(X29,k2_xboole_0(X30,X28)) = k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28)) )),
% 36.49/4.97    inference(forward_demodulation,[],[f1391,f30])).
% 36.49/4.97  fof(f30,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 36.49/4.97    inference(cnf_transformation,[],[f11])).
% 36.49/4.97  fof(f11,axiom,(
% 36.49/4.97    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 36.49/4.97  fof(f1391,plain,(
% 36.49/4.97    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28) = k4_xboole_0(k4_xboole_0(X29,X30),X28)) )),
% 36.49/4.97    inference(forward_demodulation,[],[f1348,f50])).
% 36.49/4.97  fof(f50,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 36.49/4.97    inference(superposition,[],[f26,f23])).
% 36.49/4.97  fof(f23,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f1])).
% 36.49/4.97  fof(f1,axiom,(
% 36.49/4.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 36.49/4.97  fof(f26,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f10])).
% 36.49/4.97  fof(f10,axiom,(
% 36.49/4.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 36.49/4.97  fof(f1348,plain,(
% 36.49/4.97    ( ! [X30,X28,X29] : (k4_xboole_0(k4_xboole_0(X29,k2_xboole_0(X30,X28)),X28) = k4_xboole_0(k2_xboole_0(X28,k4_xboole_0(X29,X30)),X28)) )),
% 36.49/4.97    inference(superposition,[],[f50,f98])).
% 36.49/4.97  fof(f98,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 36.49/4.97    inference(superposition,[],[f27,f30])).
% 36.49/4.97  fof(f27,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 36.49/4.97    inference(cnf_transformation,[],[f9])).
% 36.49/4.97  fof(f9,axiom,(
% 36.49/4.97    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 36.49/4.97  fof(f135022,plain,(
% 36.49/4.97    ( ! [X64,X63] : (k4_xboole_0(k4_xboole_0(X63,X64),k3_xboole_0(X63,X64)) = k4_xboole_0(X63,k3_xboole_0(X63,X64))) )),
% 36.49/4.97    inference(superposition,[],[f26,f133573])).
% 36.49/4.97  fof(f133573,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 36.49/4.97    inference(forward_demodulation,[],[f133572,f25])).
% 36.49/4.97  fof(f133572,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f133571,f23])).
% 36.49/4.97  fof(f133571,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f133435,f864])).
% 36.49/4.97  fof(f864,plain,(
% 36.49/4.97    ( ! [X33,X34,X32] : (k2_xboole_0(X34,X32) = k2_xboole_0(k4_xboole_0(X32,X33),k2_xboole_0(X34,X32))) )),
% 36.49/4.97    inference(superposition,[],[f121,f161])).
% 36.49/4.97  fof(f161,plain,(
% 36.49/4.97    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 36.49/4.97    inference(superposition,[],[f45,f23])).
% 36.49/4.97  fof(f45,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 36.49/4.97    inference(resolution,[],[f28,f20])).
% 36.49/4.97  fof(f20,plain,(
% 36.49/4.97    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f8])).
% 36.49/4.97  fof(f8,axiom,(
% 36.49/4.97    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 36.49/4.97  fof(f28,plain,(
% 36.49/4.97    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 36.49/4.97    inference(cnf_transformation,[],[f17])).
% 36.49/4.97  fof(f17,plain,(
% 36.49/4.97    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 36.49/4.97    inference(ennf_transformation,[],[f3])).
% 36.49/4.97  fof(f3,axiom,(
% 36.49/4.97    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 36.49/4.97  fof(f121,plain,(
% 36.49/4.97    ( ! [X6,X7,X5] : (k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6))) )),
% 36.49/4.97    inference(superposition,[],[f31,f23])).
% 36.49/4.97  fof(f31,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 36.49/4.97    inference(cnf_transformation,[],[f13])).
% 36.49/4.97  fof(f13,axiom,(
% 36.49/4.97    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 36.49/4.97  fof(f133435,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(X0,X1),X0))) )),
% 36.49/4.97    inference(resolution,[],[f133280,f2184])).
% 36.49/4.97  fof(f2184,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),X2) | k2_xboole_0(X0,X2) = k2_xboole_0(X0,k2_xboole_0(X2,X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f2183,f269])).
% 36.49/4.97  fof(f269,plain,(
% 36.49/4.97    ( ! [X10,X8,X9] : (k2_xboole_0(X8,k2_xboole_0(X9,X10)) = k2_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10)))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f268,f31])).
% 36.49/4.97  fof(f268,plain,(
% 36.49/4.97    ( ! [X10,X8,X9] : (k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10)))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f252,f31])).
% 36.49/4.97  fof(f252,plain,(
% 36.49/4.97    ( ! [X10,X8,X9] : (k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(X8,k2_xboole_0(k2_xboole_0(X9,X8),X10))) )),
% 36.49/4.97    inference(superposition,[],[f31,f59])).
% 36.49/4.97  fof(f59,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f56,f27])).
% 36.49/4.97  fof(f56,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 36.49/4.97    inference(superposition,[],[f27,f26])).
% 36.49/4.97  fof(f2183,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X2) = k2_xboole_0(X0,k2_xboole_0(X2,k2_xboole_0(X0,X1))) | ~r1_tarski(k4_xboole_0(X1,X0),X2)) )),
% 36.49/4.97    inference(forward_demodulation,[],[f2168,f121])).
% 36.49/4.97  fof(f2168,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),X2) | k2_xboole_0(X0,X2) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 36.49/4.97    inference(superposition,[],[f66,f50])).
% 36.49/4.97  fof(f66,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | k2_xboole_0(X1,X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 36.49/4.97    inference(resolution,[],[f32,f28])).
% 36.49/4.97  fof(f32,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f18])).
% 36.49/4.97  fof(f18,plain,(
% 36.49/4.97    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 36.49/4.97    inference(ennf_transformation,[],[f12])).
% 36.49/4.97  fof(f12,axiom,(
% 36.49/4.97    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 36.49/4.97  fof(f133280,plain,(
% 36.49/4.97    ( ! [X10,X11] : (r1_tarski(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k3_xboole_0(X10,X11))) )),
% 36.49/4.97    inference(superposition,[],[f4327,f59980])).
% 36.49/4.97  fof(f59980,plain,(
% 36.49/4.97    ( ! [X52,X51] : (k2_xboole_0(k4_xboole_0(X52,k4_xboole_0(X52,X51)),X51) = X51) )),
% 36.49/4.97    inference(superposition,[],[f72,f59737])).
% 36.49/4.97  fof(f59737,plain,(
% 36.49/4.97    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = X10) )),
% 36.49/4.97    inference(forward_demodulation,[],[f59736,f161])).
% 36.49/4.97  fof(f59736,plain,(
% 36.49/4.97    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10)))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f59402,f3360])).
% 36.49/4.97  fof(f3360,plain,(
% 36.49/4.97    ( ! [X41,X42,X40] : (k2_xboole_0(X41,k4_xboole_0(X42,X40)) = k2_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X40,X41)))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f3304,f1322])).
% 36.49/4.97  fof(f1322,plain,(
% 36.49/4.97    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 36.49/4.97    inference(superposition,[],[f98,f23])).
% 36.49/4.97  fof(f3304,plain,(
% 36.49/4.97    ( ! [X41,X42,X40] : (k2_xboole_0(X41,k4_xboole_0(X42,k4_xboole_0(X40,X41))) = k2_xboole_0(X41,k4_xboole_0(X42,k2_xboole_0(X41,X40)))) )),
% 36.49/4.97    inference(superposition,[],[f98,f262])).
% 36.49/4.97  fof(f262,plain,(
% 36.49/4.97    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 36.49/4.97    inference(forward_demodulation,[],[f244,f231])).
% 36.49/4.97  fof(f231,plain,(
% 36.49/4.97    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k4_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 36.49/4.97    inference(superposition,[],[f45,f50])).
% 36.49/4.97  fof(f244,plain,(
% 36.49/4.97    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 36.49/4.97    inference(superposition,[],[f59,f27])).
% 36.49/4.97  fof(f59402,plain,(
% 36.49/4.97    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10))) = k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,X10)))) )),
% 36.49/4.97    inference(superposition,[],[f1381,f57])).
% 36.49/4.97  fof(f57,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 36.49/4.97    inference(superposition,[],[f26,f27])).
% 36.49/4.97  fof(f1381,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f1380,f98])).
% 36.49/4.97  fof(f1380,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f1335,f919])).
% 36.49/4.97  fof(f919,plain,(
% 36.49/4.97    ( ! [X37,X38,X36] : (k4_xboole_0(k2_xboole_0(X37,X38),X36) = k4_xboole_0(k2_xboole_0(X38,k2_xboole_0(X36,X37)),X36)) )),
% 36.49/4.97    inference(superposition,[],[f50,f121])).
% 36.49/4.97  fof(f1335,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1))) )),
% 36.49/4.97    inference(superposition,[],[f98,f26])).
% 36.49/4.97  fof(f72,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 36.49/4.97    inference(resolution,[],[f62,f28])).
% 36.49/4.97  fof(f62,plain,(
% 36.49/4.97    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 36.49/4.97    inference(superposition,[],[f39,f23])).
% 36.49/4.97  fof(f39,plain,(
% 36.49/4.97    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 36.49/4.97    inference(superposition,[],[f33,f24])).
% 36.49/4.97  fof(f24,plain,(
% 36.49/4.97    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 36.49/4.97    inference(cnf_transformation,[],[f6])).
% 36.49/4.97  fof(f6,axiom,(
% 36.49/4.97    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 36.49/4.97  fof(f33,plain,(
% 36.49/4.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 36.49/4.97    inference(superposition,[],[f21,f22])).
% 36.49/4.97  fof(f21,plain,(
% 36.49/4.97    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 36.49/4.97    inference(cnf_transformation,[],[f5])).
% 36.49/4.97  fof(f5,axiom,(
% 36.49/4.97    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 36.49/4.97  fof(f4327,plain,(
% 36.49/4.97    ( ! [X59,X60,X58] : (r1_tarski(k4_xboole_0(X58,X59),k3_xboole_0(X58,k2_xboole_0(k4_xboole_0(X58,X59),X60)))) )),
% 36.49/4.97    inference(forward_demodulation,[],[f4277,f22])).
% 36.49/4.97  fof(f4277,plain,(
% 36.49/4.97    ( ! [X59,X60,X58] : (r1_tarski(k4_xboole_0(X58,X59),k3_xboole_0(k2_xboole_0(k4_xboole_0(X58,X59),X60),X58))) )),
% 36.49/4.97    inference(superposition,[],[f495,f165])).
% 36.49/4.97  fof(f165,plain,(
% 36.49/4.97    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 36.49/4.97    inference(superposition,[],[f24,f45])).
% 36.49/4.97  fof(f495,plain,(
% 36.49/4.97    ( ! [X26,X27,X25] : (r1_tarski(k3_xboole_0(X25,X27),k3_xboole_0(k2_xboole_0(X25,X26),X27))) )),
% 36.49/4.97    inference(superposition,[],[f33,f80])).
% 36.49/4.97  fof(f80,plain,(
% 36.49/4.97    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(X6,X8)) )),
% 36.49/4.97    inference(superposition,[],[f29,f24])).
% 36.49/4.97  fof(f29,plain,(
% 36.49/4.97    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 36.49/4.97    inference(cnf_transformation,[],[f4])).
% 36.49/4.97  fof(f4,axiom,(
% 36.49/4.97    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 36.49/4.97  fof(f19,plain,(
% 36.49/4.97    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 36.49/4.97    inference(cnf_transformation,[],[f16])).
% 36.49/4.97  fof(f16,plain,(
% 36.49/4.97    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.49/4.97    inference(ennf_transformation,[],[f15])).
% 36.49/4.97  fof(f15,negated_conjecture,(
% 36.49/4.97    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.49/4.97    inference(negated_conjecture,[],[f14])).
% 36.49/4.97  fof(f14,conjecture,(
% 36.49/4.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.49/4.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 36.49/4.97  % SZS output end Proof for theBenchmark
% 36.49/4.97  % (4697)------------------------------
% 36.49/4.97  % (4697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.49/4.97  % (4697)Termination reason: Refutation
% 36.49/4.97  
% 36.49/4.97  % (4697)Memory used [KB]: 139699
% 36.49/4.97  % (4697)Time elapsed: 4.548 s
% 36.49/4.97  % (4697)------------------------------
% 36.49/4.97  % (4697)------------------------------
% 36.49/4.98  % (4693)Success in time 4.614 s
%------------------------------------------------------------------------------
