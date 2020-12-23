%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:23 EST 2020

% Result     : Theorem 17.15s
% Output     : Refutation 17.15s
% Verified   : 
% Statistics : Number of formulae       :  114 (2772 expanded)
%              Number of leaves         :   11 ( 923 expanded)
%              Depth                    :   30
%              Number of atoms          :  115 (2773 expanded)
%              Number of equality atoms :  114 (2772 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f58332])).

fof(f58332,plain,(
    ! [X127,X126] : k5_xboole_0(X126,X127) = k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) ),
    inference(forward_demodulation,[],[f58331,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f58331,plain,(
    ! [X127,X126] : k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k2_xboole_0(X126,X126),X127) ),
    inference(forward_demodulation,[],[f58330,f5704])).

fof(f5704,plain,(
    ! [X21,X19,X20] : k5_xboole_0(k4_xboole_0(X20,X19),k5_xboole_0(X19,X21)) = k5_xboole_0(k2_xboole_0(X19,X20),X21) ),
    inference(backward_demodulation,[],[f1962,f5702])).

fof(f5702,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X2,X1),X1) = k2_xboole_0(X1,X2) ),
    inference(backward_demodulation,[],[f1954,f5698])).

fof(f5698,plain,(
    ! [X62,X63] : k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),X62) ),
    inference(backward_demodulation,[],[f5528,f5610])).

fof(f5610,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f5569,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f5569,plain,(
    ! [X26,X25] : k3_xboole_0(k2_xboole_0(X25,X26),X25) = X25 ),
    inference(forward_demodulation,[],[f5543,f2858])).

fof(f2858,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = X5 ),
    inference(forward_demodulation,[],[f2857,f19])).

fof(f2857,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k2_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f2856,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f2856,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X5)) ),
    inference(backward_demodulation,[],[f2182,f2854])).

fof(f2854,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k4_xboole_0(X6,X6) ),
    inference(forward_demodulation,[],[f2853,f1955])).

fof(f1955,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k4_xboole_0(X3,X3) ),
    inference(superposition,[],[f24,f1942])).

fof(f1942,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1919,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1919,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f65,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f65,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X11,k3_xboole_0(X9,X10)) = k5_xboole_0(X11,k3_xboole_0(X9,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2853,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k3_xboole_0(X6,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f2832,f20])).

fof(f2832,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k3_xboole_0(k4_xboole_0(X5,X6),X6) ),
    inference(superposition,[],[f24,f1945])).

fof(f1945,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f1942,f1942])).

fof(f2182,plain,(
    ! [X4,X5] : k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f47,f1999])).

fof(f1999,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f23,f1950])).

fof(f1950,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f1942,f24])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f26,f22])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5543,plain,(
    ! [X26,X25] : k3_xboole_0(k2_xboole_0(X25,X26),X25) = k5_xboole_0(k2_xboole_0(X25,X26),k4_xboole_0(X26,X25)) ),
    inference(superposition,[],[f3608,f3422])).

fof(f3422,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f3399,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f3399,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X6,X6),X7) = X7 ),
    inference(superposition,[],[f2225,f1955])).

fof(f2225,plain,(
    ! [X33,X34,X32] : k2_xboole_0(k3_xboole_0(X33,k4_xboole_0(X32,X34)),X32) = X32 ),
    inference(superposition,[],[f2199,f145])).

fof(f145,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f59,f27])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f27,f20])).

fof(f2199,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[],[f2188,f24])).

fof(f2188,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f37,f2187])).

fof(f2187,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f2186,f1942])).

fof(f2186,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f2185,f2062])).

fof(f2062,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f109,f2059])).

fof(f2059,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k3_xboole_0(X21,k4_xboole_0(X21,X22)) ),
    inference(forward_demodulation,[],[f1990,f1945])).

fof(f1990,plain,(
    ! [X21,X22] : k4_xboole_0(X21,X22) = k3_xboole_0(X21,k4_xboole_0(k4_xboole_0(X21,X22),X22)) ),
    inference(superposition,[],[f1950,f145])).

fof(f109,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f20])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f24])).

fof(f2185,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f2184,f23])).

fof(f2184,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k4_xboole_0(X3,k3_xboole_0(X2,X3)))) ),
    inference(forward_demodulation,[],[f2181,f27])).

fof(f2181,plain,(
    ! [X2,X3] : k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f48,f1999])).

fof(f48,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(superposition,[],[f26,f23])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f24])).

fof(f3608,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f3560,f23])).

fof(f3560,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k5_xboole_0(X15,X16)) = X16 ),
    inference(backward_demodulation,[],[f2009,f3490])).

fof(f3490,plain,(
    ! [X4,X5] : k5_xboole_0(k4_xboole_0(X5,X5),X4) = X4 ),
    inference(superposition,[],[f2715,f3434])).

fof(f3434,plain,(
    ! [X41,X42] : k4_xboole_0(X41,X41) = k4_xboole_0(X42,X42) ),
    inference(superposition,[],[f3399,f2938])).

fof(f2938,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k4_xboole_0(X0,X0)) = X1 ),
    inference(superposition,[],[f961,f1955])).

fof(f961,plain,(
    ! [X144,X142,X143,X141] : k2_xboole_0(X143,k3_xboole_0(X141,k4_xboole_0(k4_xboole_0(X143,X144),X142))) = X143 ),
    inference(superposition,[],[f389,f374])).

fof(f374,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X7,X8),X6) = k3_xboole_0(X7,k4_xboole_0(X6,X8)) ),
    inference(superposition,[],[f145,f20])).

fof(f389,plain,(
    ! [X12,X10,X11] : k2_xboole_0(X10,k3_xboole_0(X11,k4_xboole_0(X10,X12))) = X10 ),
    inference(superposition,[],[f21,f145])).

fof(f2715,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[],[f2191,f1950])).

fof(f2191,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(backward_demodulation,[],[f1815,f2188])).

fof(f1815,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f37,f20])).

fof(f2009,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X15,X15),X16) = k5_xboole_0(X15,k5_xboole_0(X15,X16)) ),
    inference(superposition,[],[f48,f1950])).

fof(f5528,plain,(
    ! [X62,X63] : k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),k3_xboole_0(X62,k2_xboole_0(X62,X63))) ),
    inference(forward_demodulation,[],[f5497,f20])).

fof(f5497,plain,(
    ! [X62,X63] : k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),k3_xboole_0(k2_xboole_0(X62,X63),X62)) ),
    inference(superposition,[],[f2187,f3422])).

fof(f1954,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X2,X1),X1) = k5_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f22,f1942])).

fof(f1962,plain,(
    ! [X21,X19,X20] : k5_xboole_0(k2_xboole_0(k4_xboole_0(X20,X19),X19),X21) = k5_xboole_0(k4_xboole_0(X20,X19),k5_xboole_0(X19,X21)) ),
    inference(superposition,[],[f47,f1942])).

fof(f58330,plain,(
    ! [X127,X126] : k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k4_xboole_0(X126,X126),k5_xboole_0(X126,X127)) ),
    inference(forward_demodulation,[],[f58329,f10176])).

fof(f10176,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X20,X20) = k3_xboole_0(X20,k4_xboole_0(X22,k2_xboole_0(X20,X21))) ),
    inference(forward_demodulation,[],[f10088,f2990])).

fof(f2990,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X1) = k3_xboole_0(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f2989,f2854])).

fof(f2989,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2988,f2102])).

fof(f2102,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2063,f24])).

fof(f2063,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f115,f2059])).

fof(f115,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f24,f36])).

fof(f2988,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(forward_demodulation,[],[f2987,f27])).

fof(f2987,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1)) ),
    inference(forward_demodulation,[],[f2986,f145])).

fof(f2986,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2923,f20])).

fof(f2923,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1955,f24])).

fof(f10088,plain,(
    ! [X21,X22,X20] : k3_xboole_0(X22,k4_xboole_0(X20,X20)) = k3_xboole_0(X20,k4_xboole_0(X22,k2_xboole_0(X20,X21))) ),
    inference(superposition,[],[f145,f5712])).

fof(f5712,plain,(
    ! [X19,X18] : k4_xboole_0(X18,X18) = k4_xboole_0(X18,k2_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f5631,f1999])).

fof(f5631,plain,(
    ! [X19,X18] : k5_xboole_0(X18,X18) = k4_xboole_0(X18,k2_xboole_0(X18,X19)) ),
    inference(superposition,[],[f34,f5569])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f20])).

fof(f58329,plain,(
    ! [X127,X126] : k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k3_xboole_0(X126,k4_xboole_0(X127,k2_xboole_0(X126,X127))),k5_xboole_0(X126,X127)) ),
    inference(forward_demodulation,[],[f58055,f27])).

fof(f58055,plain,(
    ! [X127,X126] : k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X126,X127),k2_xboole_0(X126,X127)),k5_xboole_0(X126,X127)) ),
    inference(superposition,[],[f28225,f2736])).

fof(f2736,plain,(
    ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f47,f2191])).

fof(f28225,plain,(
    ! [X121,X120] : k4_xboole_0(X120,X121) = k5_xboole_0(k4_xboole_0(X121,X120),k5_xboole_0(X120,X121)) ),
    inference(superposition,[],[f28155,f3972])).

fof(f3972,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f48,f2234])).

fof(f2234,plain,(
    ! [X10,X9] : k5_xboole_0(k3_xboole_0(X10,X9),k4_xboole_0(X9,X10)) = X9 ),
    inference(backward_demodulation,[],[f2070,f2214])).

fof(f2214,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f2199,f20])).

fof(f2070,plain,(
    ! [X10,X9] : k2_xboole_0(k3_xboole_0(X10,X9),X9) = k5_xboole_0(k3_xboole_0(X10,X9),k4_xboole_0(X9,X10)) ),
    inference(backward_demodulation,[],[f319,f2059])).

fof(f319,plain,(
    ! [X10,X9] : k2_xboole_0(k3_xboole_0(X10,X9),X9) = k5_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f22,f109])).

fof(f28155,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f28009,f8982])).

fof(f8982,plain,(
    ! [X2,X1] : k5_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2 ),
    inference(superposition,[],[f3560,f6085])).

fof(f6085,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k5_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f6068,f23])).

fof(f6068,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k5_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f47,f3616])).

fof(f3616,plain,(
    ! [X21,X22] : k3_xboole_0(X22,X21) = k5_xboole_0(k4_xboole_0(X21,X22),X21) ),
    inference(superposition,[],[f3560,f2191])).

fof(f28009,plain,(
    ! [X2,X3] : k5_xboole_0(X3,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f47,f3972])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:12:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (5876)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.43  % (5881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (5871)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (5866)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (5869)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (5870)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5872)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (5879)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (5878)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5880)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (5874)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (5883)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (5868)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (5882)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (5877)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (5877)Refutation not found, incomplete strategy% (5877)------------------------------
% 0.21/0.49  % (5877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5877)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5877)Memory used [KB]: 10490
% 0.21/0.49  % (5877)Time elapsed: 0.079 s
% 0.21/0.49  % (5877)------------------------------
% 0.21/0.49  % (5877)------------------------------
% 0.21/0.50  % (5875)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (5865)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (5873)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 5.29/1.03  % (5870)Time limit reached!
% 5.29/1.03  % (5870)------------------------------
% 5.29/1.03  % (5870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.29/1.03  % (5870)Termination reason: Time limit
% 5.29/1.03  % (5870)Termination phase: Saturation
% 5.29/1.03  
% 5.29/1.03  % (5870)Memory used [KB]: 15223
% 5.29/1.03  % (5870)Time elapsed: 0.600 s
% 5.29/1.03  % (5870)------------------------------
% 5.29/1.03  % (5870)------------------------------
% 12.36/1.92  % (5872)Time limit reached!
% 12.36/1.92  % (5872)------------------------------
% 12.36/1.92  % (5872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.36/1.92  % (5872)Termination reason: Time limit
% 12.36/1.92  % (5872)Termination phase: Saturation
% 12.36/1.92  
% 12.36/1.92  % (5872)Memory used [KB]: 39786
% 12.36/1.92  % (5872)Time elapsed: 1.500 s
% 12.36/1.92  % (5872)------------------------------
% 12.36/1.92  % (5872)------------------------------
% 12.96/2.04  % (5871)Time limit reached!
% 12.96/2.04  % (5871)------------------------------
% 12.96/2.04  % (5871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.96/2.04  % (5871)Termination reason: Time limit
% 12.96/2.04  % (5871)Termination phase: Saturation
% 12.96/2.04  
% 12.96/2.04  % (5871)Memory used [KB]: 44135
% 12.96/2.04  % (5871)Time elapsed: 1.500 s
% 12.96/2.04  % (5871)------------------------------
% 12.96/2.04  % (5871)------------------------------
% 14.76/2.21  % (5868)Time limit reached!
% 14.76/2.21  % (5868)------------------------------
% 14.76/2.21  % (5868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.76/2.21  % (5868)Termination reason: Time limit
% 14.76/2.21  
% 14.76/2.21  % (5868)Memory used [KB]: 43240
% 14.76/2.21  % (5868)Time elapsed: 1.803 s
% 14.76/2.21  % (5868)------------------------------
% 14.76/2.21  % (5868)------------------------------
% 17.15/2.51  % (5882)Refutation found. Thanks to Tanya!
% 17.15/2.51  % SZS status Theorem for theBenchmark
% 17.15/2.51  % SZS output start Proof for theBenchmark
% 17.15/2.51  fof(f58333,plain,(
% 17.15/2.51    $false),
% 17.15/2.51    inference(subsumption_resolution,[],[f18,f58332])).
% 17.15/2.51  fof(f58332,plain,(
% 17.15/2.51    ( ! [X127,X126] : (k5_xboole_0(X126,X127) = k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127))) )),
% 17.15/2.51    inference(forward_demodulation,[],[f58331,f19])).
% 17.15/2.51  fof(f19,plain,(
% 17.15/2.51    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 17.15/2.51    inference(cnf_transformation,[],[f14])).
% 17.15/2.51  fof(f14,plain,(
% 17.15/2.51    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 17.15/2.51    inference(rectify,[],[f2])).
% 17.15/2.52  fof(f2,axiom,(
% 17.15/2.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 17.15/2.52  fof(f58331,plain,(
% 17.15/2.52    ( ! [X127,X126] : (k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k2_xboole_0(X126,X126),X127)) )),
% 17.15/2.52    inference(forward_demodulation,[],[f58330,f5704])).
% 17.15/2.52  fof(f5704,plain,(
% 17.15/2.52    ( ! [X21,X19,X20] : (k5_xboole_0(k4_xboole_0(X20,X19),k5_xboole_0(X19,X21)) = k5_xboole_0(k2_xboole_0(X19,X20),X21)) )),
% 17.15/2.52    inference(backward_demodulation,[],[f1962,f5702])).
% 17.15/2.52  fof(f5702,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X2,X1),X1) = k2_xboole_0(X1,X2)) )),
% 17.15/2.52    inference(backward_demodulation,[],[f1954,f5698])).
% 17.15/2.52  fof(f5698,plain,(
% 17.15/2.52    ( ! [X62,X63] : (k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),X62)) )),
% 17.15/2.52    inference(backward_demodulation,[],[f5528,f5610])).
% 17.15/2.52  fof(f5610,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 17.15/2.52    inference(superposition,[],[f5569,f20])).
% 17.15/2.52  fof(f20,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 17.15/2.52    inference(cnf_transformation,[],[f1])).
% 17.15/2.52  fof(f1,axiom,(
% 17.15/2.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 17.15/2.52  fof(f5569,plain,(
% 17.15/2.52    ( ! [X26,X25] : (k3_xboole_0(k2_xboole_0(X25,X26),X25) = X25) )),
% 17.15/2.52    inference(forward_demodulation,[],[f5543,f2858])).
% 17.15/2.52  fof(f2858,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = X5) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2857,f19])).
% 17.15/2.52  fof(f2857,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k2_xboole_0(X5,X5)) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2856,f22])).
% 17.15/2.52  fof(f22,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(cnf_transformation,[],[f11])).
% 17.15/2.52  fof(f11,axiom,(
% 17.15/2.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 17.15/2.52  fof(f2856,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k5_xboole_0(X5,k4_xboole_0(X5,X5))) )),
% 17.15/2.52    inference(backward_demodulation,[],[f2182,f2854])).
% 17.15/2.52  fof(f2854,plain,(
% 17.15/2.52    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k4_xboole_0(X6,X6)) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2853,f1955])).
% 17.15/2.52  fof(f1955,plain,(
% 17.15/2.52    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X3)) = k4_xboole_0(X3,X3)) )),
% 17.15/2.52    inference(superposition,[],[f24,f1942])).
% 17.15/2.52  fof(f1942,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 17.15/2.52    inference(forward_demodulation,[],[f1919,f21])).
% 17.15/2.52  fof(f21,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 17.15/2.52    inference(cnf_transformation,[],[f5])).
% 17.15/2.52  fof(f5,axiom,(
% 17.15/2.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 17.15/2.52  fof(f1919,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(superposition,[],[f65,f23])).
% 17.15/2.52  fof(f23,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(cnf_transformation,[],[f3])).
% 17.15/2.52  fof(f3,axiom,(
% 17.15/2.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 17.15/2.52  fof(f65,plain,(
% 17.15/2.52    ( ! [X10,X11,X9] : (k2_xboole_0(X11,k3_xboole_0(X9,X10)) = k5_xboole_0(X11,k3_xboole_0(X9,k4_xboole_0(X10,X11)))) )),
% 17.15/2.52    inference(superposition,[],[f22,f27])).
% 17.15/2.52  fof(f27,plain,(
% 17.15/2.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 17.15/2.52    inference(cnf_transformation,[],[f8])).
% 17.15/2.52  fof(f8,axiom,(
% 17.15/2.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 17.15/2.52  fof(f24,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(cnf_transformation,[],[f7])).
% 17.15/2.52  fof(f7,axiom,(
% 17.15/2.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 17.15/2.52  fof(f2853,plain,(
% 17.15/2.52    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k3_xboole_0(X6,k4_xboole_0(X5,X6))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2832,f20])).
% 17.15/2.52  fof(f2832,plain,(
% 17.15/2.52    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k3_xboole_0(k4_xboole_0(X5,X6),X6)) )),
% 17.15/2.52    inference(superposition,[],[f24,f1945])).
% 17.15/2.52  fof(f1945,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 17.15/2.52    inference(superposition,[],[f1942,f1942])).
% 17.15/2.52  fof(f2182,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k5_xboole_0(k2_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)))) )),
% 17.15/2.52    inference(superposition,[],[f47,f1999])).
% 17.15/2.52  fof(f1999,plain,(
% 17.15/2.52    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) )),
% 17.15/2.52    inference(superposition,[],[f23,f1950])).
% 17.15/2.52  fof(f1950,plain,(
% 17.15/2.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 17.15/2.52    inference(superposition,[],[f1942,f24])).
% 17.15/2.52  fof(f47,plain,(
% 17.15/2.52    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 17.15/2.52    inference(superposition,[],[f26,f22])).
% 17.15/2.52  fof(f26,plain,(
% 17.15/2.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 17.15/2.52    inference(cnf_transformation,[],[f10])).
% 17.15/2.52  fof(f10,axiom,(
% 17.15/2.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 17.15/2.52  fof(f5543,plain,(
% 17.15/2.52    ( ! [X26,X25] : (k3_xboole_0(k2_xboole_0(X25,X26),X25) = k5_xboole_0(k2_xboole_0(X25,X26),k4_xboole_0(X26,X25))) )),
% 17.15/2.52    inference(superposition,[],[f3608,f3422])).
% 17.15/2.52  fof(f3422,plain,(
% 17.15/2.52    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 17.15/2.52    inference(superposition,[],[f3399,f29])).
% 17.15/2.52  fof(f29,plain,(
% 17.15/2.52    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 17.15/2.52    inference(cnf_transformation,[],[f6])).
% 17.15/2.52  fof(f6,axiom,(
% 17.15/2.52    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 17.15/2.52  fof(f3399,plain,(
% 17.15/2.52    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X6,X6),X7) = X7) )),
% 17.15/2.52    inference(superposition,[],[f2225,f1955])).
% 17.15/2.52  fof(f2225,plain,(
% 17.15/2.52    ( ! [X33,X34,X32] : (k2_xboole_0(k3_xboole_0(X33,k4_xboole_0(X32,X34)),X32) = X32) )),
% 17.15/2.52    inference(superposition,[],[f2199,f145])).
% 17.15/2.52  fof(f145,plain,(
% 17.15/2.52    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 17.15/2.52    inference(superposition,[],[f59,f27])).
% 17.15/2.52  fof(f59,plain,(
% 17.15/2.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 17.15/2.52    inference(superposition,[],[f27,f20])).
% 17.15/2.52  fof(f2199,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 17.15/2.52    inference(superposition,[],[f2188,f24])).
% 17.15/2.52  fof(f2188,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 17.15/2.52    inference(backward_demodulation,[],[f37,f2187])).
% 17.15/2.52  fof(f2187,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2186,f1942])).
% 17.15/2.52  fof(f2186,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2185,f2062])).
% 17.15/2.52  fof(f2062,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(backward_demodulation,[],[f109,f2059])).
% 17.15/2.52  fof(f2059,plain,(
% 17.15/2.52    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k3_xboole_0(X21,k4_xboole_0(X21,X22))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f1990,f1945])).
% 17.15/2.52  fof(f1990,plain,(
% 17.15/2.52    ( ! [X21,X22] : (k4_xboole_0(X21,X22) = k3_xboole_0(X21,k4_xboole_0(k4_xboole_0(X21,X22),X22))) )),
% 17.15/2.52    inference(superposition,[],[f1950,f145])).
% 17.15/2.52  fof(f109,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(superposition,[],[f36,f20])).
% 17.15/2.52  fof(f36,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(superposition,[],[f24,f24])).
% 17.15/2.52  fof(f2185,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2184,f23])).
% 17.15/2.52  fof(f2184,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X2,k4_xboole_0(X3,k3_xboole_0(X2,X3))))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2181,f27])).
% 17.15/2.52  fof(f2181,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)))) )),
% 17.15/2.52    inference(superposition,[],[f48,f1999])).
% 17.15/2.52  fof(f48,plain,(
% 17.15/2.52    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 17.15/2.52    inference(superposition,[],[f26,f23])).
% 17.15/2.52  fof(f37,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(superposition,[],[f22,f24])).
% 17.15/2.52  fof(f3608,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 17.15/2.52    inference(superposition,[],[f3560,f23])).
% 17.15/2.52  fof(f3560,plain,(
% 17.15/2.52    ( ! [X15,X16] : (k5_xboole_0(X15,k5_xboole_0(X15,X16)) = X16) )),
% 17.15/2.52    inference(backward_demodulation,[],[f2009,f3490])).
% 17.15/2.52  fof(f3490,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k5_xboole_0(k4_xboole_0(X5,X5),X4) = X4) )),
% 17.15/2.52    inference(superposition,[],[f2715,f3434])).
% 17.15/2.52  fof(f3434,plain,(
% 17.15/2.52    ( ! [X41,X42] : (k4_xboole_0(X41,X41) = k4_xboole_0(X42,X42)) )),
% 17.15/2.52    inference(superposition,[],[f3399,f2938])).
% 17.15/2.52  fof(f2938,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X0,X0)) = X1) )),
% 17.15/2.52    inference(superposition,[],[f961,f1955])).
% 17.15/2.52  fof(f961,plain,(
% 17.15/2.52    ( ! [X144,X142,X143,X141] : (k2_xboole_0(X143,k3_xboole_0(X141,k4_xboole_0(k4_xboole_0(X143,X144),X142))) = X143) )),
% 17.15/2.52    inference(superposition,[],[f389,f374])).
% 17.15/2.52  fof(f374,plain,(
% 17.15/2.52    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X7,X8),X6) = k3_xboole_0(X7,k4_xboole_0(X6,X8))) )),
% 17.15/2.52    inference(superposition,[],[f145,f20])).
% 17.15/2.52  fof(f389,plain,(
% 17.15/2.52    ( ! [X12,X10,X11] : (k2_xboole_0(X10,k3_xboole_0(X11,k4_xboole_0(X10,X12))) = X10) )),
% 17.15/2.52    inference(superposition,[],[f21,f145])).
% 17.15/2.52  fof(f2715,plain,(
% 17.15/2.52    ( ! [X0] : (k5_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 17.15/2.52    inference(superposition,[],[f2191,f1950])).
% 17.15/2.52  fof(f2191,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0) )),
% 17.15/2.52    inference(backward_demodulation,[],[f1815,f2188])).
% 17.15/2.52  fof(f1815,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(superposition,[],[f37,f20])).
% 17.15/2.52  fof(f2009,plain,(
% 17.15/2.52    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X15,X15),X16) = k5_xboole_0(X15,k5_xboole_0(X15,X16))) )),
% 17.15/2.52    inference(superposition,[],[f48,f1950])).
% 17.15/2.52  fof(f5528,plain,(
% 17.15/2.52    ( ! [X62,X63] : (k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),k3_xboole_0(X62,k2_xboole_0(X62,X63)))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f5497,f20])).
% 17.15/2.52  fof(f5497,plain,(
% 17.15/2.52    ( ! [X62,X63] : (k2_xboole_0(X62,X63) = k5_xboole_0(k4_xboole_0(X63,X62),k3_xboole_0(k2_xboole_0(X62,X63),X62))) )),
% 17.15/2.52    inference(superposition,[],[f2187,f3422])).
% 17.15/2.52  fof(f1954,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X2,X1),X1) = k5_xboole_0(k4_xboole_0(X2,X1),X1)) )),
% 17.15/2.52    inference(superposition,[],[f22,f1942])).
% 17.15/2.52  fof(f1962,plain,(
% 17.15/2.52    ( ! [X21,X19,X20] : (k5_xboole_0(k2_xboole_0(k4_xboole_0(X20,X19),X19),X21) = k5_xboole_0(k4_xboole_0(X20,X19),k5_xboole_0(X19,X21))) )),
% 17.15/2.52    inference(superposition,[],[f47,f1942])).
% 17.15/2.52  fof(f58330,plain,(
% 17.15/2.52    ( ! [X127,X126] : (k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k4_xboole_0(X126,X126),k5_xboole_0(X126,X127))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f58329,f10176])).
% 17.15/2.52  fof(f10176,plain,(
% 17.15/2.52    ( ! [X21,X22,X20] : (k4_xboole_0(X20,X20) = k3_xboole_0(X20,k4_xboole_0(X22,k2_xboole_0(X20,X21)))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f10088,f2990])).
% 17.15/2.52  fof(f2990,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X1,X1) = k3_xboole_0(X0,k4_xboole_0(X1,X1))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2989,f2854])).
% 17.15/2.52  fof(f2989,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2988,f2102])).
% 17.15/2.52  fof(f2102,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k3_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2063,f24])).
% 17.15/2.52  fof(f2063,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 17.15/2.52    inference(backward_demodulation,[],[f115,f2059])).
% 17.15/2.52  fof(f115,plain,(
% 17.15/2.52    ( ! [X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 17.15/2.52    inference(superposition,[],[f24,f36])).
% 17.15/2.52  fof(f2988,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X1,X1)))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2987,f27])).
% 17.15/2.52  fof(f2987,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X1))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2986,f145])).
% 17.15/2.52  fof(f2986,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f2923,f20])).
% 17.15/2.52  fof(f2923,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k3_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 17.15/2.52    inference(superposition,[],[f1955,f24])).
% 17.15/2.52  fof(f10088,plain,(
% 17.15/2.52    ( ! [X21,X22,X20] : (k3_xboole_0(X22,k4_xboole_0(X20,X20)) = k3_xboole_0(X20,k4_xboole_0(X22,k2_xboole_0(X20,X21)))) )),
% 17.15/2.52    inference(superposition,[],[f145,f5712])).
% 17.15/2.52  fof(f5712,plain,(
% 17.15/2.52    ( ! [X19,X18] : (k4_xboole_0(X18,X18) = k4_xboole_0(X18,k2_xboole_0(X18,X19))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f5631,f1999])).
% 17.15/2.52  fof(f5631,plain,(
% 17.15/2.52    ( ! [X19,X18] : (k5_xboole_0(X18,X18) = k4_xboole_0(X18,k2_xboole_0(X18,X19))) )),
% 17.15/2.52    inference(superposition,[],[f34,f5569])).
% 17.15/2.52  fof(f34,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(superposition,[],[f23,f20])).
% 17.15/2.52  fof(f58329,plain,(
% 17.15/2.52    ( ! [X127,X126] : (k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k3_xboole_0(X126,k4_xboole_0(X127,k2_xboole_0(X126,X127))),k5_xboole_0(X126,X127))) )),
% 17.15/2.52    inference(forward_demodulation,[],[f58055,f27])).
% 17.15/2.52  fof(f58055,plain,(
% 17.15/2.52    ( ! [X127,X126] : (k4_xboole_0(k2_xboole_0(X126,X127),k3_xboole_0(X126,X127)) = k5_xboole_0(k4_xboole_0(k3_xboole_0(X126,X127),k2_xboole_0(X126,X127)),k5_xboole_0(X126,X127))) )),
% 17.15/2.52    inference(superposition,[],[f28225,f2736])).
% 17.15/2.52  fof(f2736,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k2_xboole_0(X1,X0),k3_xboole_0(X1,X0))) )),
% 17.15/2.52    inference(superposition,[],[f47,f2191])).
% 17.15/2.52  fof(f28225,plain,(
% 17.15/2.52    ( ! [X121,X120] : (k4_xboole_0(X120,X121) = k5_xboole_0(k4_xboole_0(X121,X120),k5_xboole_0(X120,X121))) )),
% 17.15/2.52    inference(superposition,[],[f28155,f3972])).
% 17.15/2.52  fof(f3972,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) )),
% 17.15/2.52    inference(superposition,[],[f48,f2234])).
% 17.15/2.52  fof(f2234,plain,(
% 17.15/2.52    ( ! [X10,X9] : (k5_xboole_0(k3_xboole_0(X10,X9),k4_xboole_0(X9,X10)) = X9) )),
% 17.15/2.52    inference(backward_demodulation,[],[f2070,f2214])).
% 17.15/2.52  fof(f2214,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),X1) = X1) )),
% 17.15/2.52    inference(superposition,[],[f2199,f20])).
% 17.15/2.52  fof(f2070,plain,(
% 17.15/2.52    ( ! [X10,X9] : (k2_xboole_0(k3_xboole_0(X10,X9),X9) = k5_xboole_0(k3_xboole_0(X10,X9),k4_xboole_0(X9,X10))) )),
% 17.15/2.52    inference(backward_demodulation,[],[f319,f2059])).
% 17.15/2.52  fof(f319,plain,(
% 17.15/2.52    ( ! [X10,X9] : (k2_xboole_0(k3_xboole_0(X10,X9),X9) = k5_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 17.15/2.52    inference(superposition,[],[f22,f109])).
% 17.15/2.52  fof(f28155,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = X2) )),
% 17.15/2.52    inference(forward_demodulation,[],[f28009,f8982])).
% 17.15/2.52  fof(f8982,plain,(
% 17.15/2.52    ( ! [X2,X1] : (k5_xboole_0(k2_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = X2) )),
% 17.15/2.52    inference(superposition,[],[f3560,f6085])).
% 17.15/2.52  fof(f6085,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k5_xboole_0(k2_xboole_0(X1,X0),X0)) )),
% 17.15/2.52    inference(forward_demodulation,[],[f6068,f23])).
% 17.15/2.52  fof(f6068,plain,(
% 17.15/2.52    ( ! [X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k5_xboole_0(k2_xboole_0(X1,X0),X0)) )),
% 17.15/2.52    inference(superposition,[],[f47,f3616])).
% 17.15/2.52  fof(f3616,plain,(
% 17.15/2.52    ( ! [X21,X22] : (k3_xboole_0(X22,X21) = k5_xboole_0(k4_xboole_0(X21,X22),X21)) )),
% 17.15/2.52    inference(superposition,[],[f3560,f2191])).
% 17.15/2.52  fof(f28009,plain,(
% 17.15/2.52    ( ! [X2,X3] : (k5_xboole_0(X3,k5_xboole_0(X2,X3)) = k5_xboole_0(k2_xboole_0(X3,X2),k4_xboole_0(X3,X2))) )),
% 17.15/2.52    inference(superposition,[],[f47,f3972])).
% 17.15/2.52  fof(f18,plain,(
% 17.15/2.52    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 17.15/2.52    inference(cnf_transformation,[],[f17])).
% 17.15/2.52  fof(f17,plain,(
% 17.15/2.52    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 17.15/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 17.15/2.52  fof(f16,plain,(
% 17.15/2.52    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 17.15/2.52    introduced(choice_axiom,[])).
% 17.15/2.52  fof(f15,plain,(
% 17.15/2.52    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 17.15/2.52    inference(ennf_transformation,[],[f13])).
% 17.15/2.52  fof(f13,negated_conjecture,(
% 17.15/2.52    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 17.15/2.52    inference(negated_conjecture,[],[f12])).
% 17.15/2.52  fof(f12,conjecture,(
% 17.15/2.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 17.15/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 17.15/2.52  % SZS output end Proof for theBenchmark
% 17.15/2.52  % (5882)------------------------------
% 17.15/2.52  % (5882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.15/2.52  % (5882)Termination reason: Refutation
% 17.15/2.52  
% 17.15/2.52  % (5882)Memory used [KB]: 46054
% 17.15/2.52  % (5882)Time elapsed: 2.083 s
% 17.15/2.52  % (5882)------------------------------
% 17.15/2.52  % (5882)------------------------------
% 17.15/2.52  % (5864)Success in time 2.16 s
%------------------------------------------------------------------------------
