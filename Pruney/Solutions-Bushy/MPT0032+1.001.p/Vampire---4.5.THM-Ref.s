%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0032+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:13 EST 2020

% Result     : Theorem 7.60s
% Output     : Refutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 319 expanded)
%              Number of leaves         :    8 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          :   75 ( 319 expanded)
%              Number of equality atoms :   74 ( 318 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16571,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16570,f16320])).

fof(f16320,plain,(
    ! [X333,X331,X332,X330] : k2_xboole_0(X333,k3_xboole_0(X332,k2_xboole_0(X330,X331))) = k2_xboole_0(X333,k3_xboole_0(X332,k2_xboole_0(X331,X330))) ),
    inference(superposition,[],[f9354,f15789])).

fof(f15789,plain,(
    ! [X198,X202,X199] : k3_xboole_0(X202,k2_xboole_0(X198,X199)) = k3_xboole_0(k2_xboole_0(X199,X198),X202) ),
    inference(forward_demodulation,[],[f15788,f1347])).

fof(f1347,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X30,X31) = k2_xboole_0(X31,k2_xboole_0(X30,k3_xboole_0(X32,X31))) ),
    inference(forward_demodulation,[],[f1294,f237])).

fof(f237,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) = k2_xboole_0(X8,k3_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f197,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f197,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k3_xboole_0(X10,k2_xboole_0(X8,X9))) = k3_xboole_0(k2_xboole_0(X8,X10),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f19,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f18,f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1294,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X30,X31) = k2_xboole_0(X31,k2_xboole_0(X30,k3_xboole_0(X32,k2_xboole_0(X30,X31)))) ),
    inference(superposition,[],[f59,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f16,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f59,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f15788,plain,(
    ! [X198,X202,X199,X201] : k3_xboole_0(X202,k2_xboole_0(X198,X199)) = k3_xboole_0(k2_xboole_0(X198,k2_xboole_0(X199,k3_xboole_0(X201,X198))),X202) ),
    inference(forward_demodulation,[],[f15787,f4686])).

fof(f4686,plain,(
    ! [X57,X54,X56,X55] : k2_xboole_0(X54,k3_xboole_0(X57,X55)) = k2_xboole_0(X54,k3_xboole_0(X57,k2_xboole_0(X55,k3_xboole_0(X54,X56)))) ),
    inference(forward_demodulation,[],[f4685,f223])).

fof(f223,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,k3_xboole_0(k2_xboole_0(X12,X11),X13)) = k2_xboole_0(X11,k3_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f184,f181])).

fof(f181,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k3_xboole_0(X3,X4)) = k3_xboole_0(k2_xboole_0(X3,X2),k2_xboole_0(X2,X4)) ),
    inference(superposition,[],[f19,f15])).

fof(f184,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,k3_xboole_0(k2_xboole_0(X12,X11),X13)) = k3_xboole_0(k2_xboole_0(X12,X11),k2_xboole_0(X11,X13)) ),
    inference(superposition,[],[f19,f77])).

fof(f77,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f58,f15])).

fof(f4685,plain,(
    ! [X57,X54,X56,X55] : k2_xboole_0(X54,k3_xboole_0(X57,k2_xboole_0(X55,k3_xboole_0(k2_xboole_0(X54,X55),X56)))) = k2_xboole_0(X54,k3_xboole_0(X57,X55)) ),
    inference(forward_demodulation,[],[f4591,f19])).

fof(f4591,plain,(
    ! [X57,X54,X56,X55] : k2_xboole_0(X54,k3_xboole_0(X57,k2_xboole_0(X55,k3_xboole_0(k2_xboole_0(X54,X55),X56)))) = k3_xboole_0(k2_xboole_0(X54,X57),k2_xboole_0(X54,X55)) ),
    inference(superposition,[],[f19,f67])).

fof(f67,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(X11,k2_xboole_0(X12,k3_xboole_0(k2_xboole_0(X11,X12),X13))) ),
    inference(superposition,[],[f18,f16])).

fof(f15787,plain,(
    ! [X198,X202,X200,X199,X201] : k3_xboole_0(X202,k2_xboole_0(X198,X199)) = k3_xboole_0(k2_xboole_0(X198,k2_xboole_0(X199,k3_xboole_0(X201,k2_xboole_0(X198,k3_xboole_0(X199,X200))))),X202) ),
    inference(forward_demodulation,[],[f15786,f18])).

fof(f15786,plain,(
    ! [X198,X202,X200,X199,X201] : k3_xboole_0(k2_xboole_0(k2_xboole_0(X198,X199),k3_xboole_0(X201,k2_xboole_0(X198,k3_xboole_0(X199,X200)))),X202) = k3_xboole_0(X202,k2_xboole_0(X198,X199)) ),
    inference(forward_demodulation,[],[f15785,f794])).

fof(f794,plain,(
    ! [X47,X48,X49] : k3_xboole_0(X47,k3_xboole_0(X49,k2_xboole_0(X47,X48))) = k3_xboole_0(X49,X47) ),
    inference(superposition,[],[f43,f236])).

fof(f236,plain,(
    ! [X0,X1] : k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f194,f20])).

fof(f194,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f19,f13])).

fof(f43,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X5,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f17,f14])).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f15785,plain,(
    ! [X198,X202,X200,X199,X201] : k3_xboole_0(k2_xboole_0(k2_xboole_0(X198,X199),k3_xboole_0(X201,k2_xboole_0(X198,k3_xboole_0(X199,X200)))),X202) = k3_xboole_0(k2_xboole_0(X198,X199),k3_xboole_0(X202,k2_xboole_0(k2_xboole_0(X198,X199),X201))) ),
    inference(forward_demodulation,[],[f15429,f43])).

fof(f15429,plain,(
    ! [X198,X202,X200,X199,X201] : k3_xboole_0(k2_xboole_0(k2_xboole_0(X198,X199),k3_xboole_0(X201,k2_xboole_0(X198,k3_xboole_0(X199,X200)))),X202) = k3_xboole_0(k2_xboole_0(k2_xboole_0(X198,X199),X201),k3_xboole_0(k2_xboole_0(X198,X199),X202)) ),
    inference(superposition,[],[f213,f212])).

fof(f212,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,k3_xboole_0(X7,X8))) ),
    inference(superposition,[],[f16,f19])).

fof(f213,plain,(
    ! [X12,X10,X11,X9] : k3_xboole_0(k2_xboole_0(X9,X10),k3_xboole_0(k2_xboole_0(X9,X11),X12)) = k3_xboole_0(k2_xboole_0(X9,k3_xboole_0(X10,X11)),X12) ),
    inference(superposition,[],[f17,f19])).

fof(f9354,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k3_xboole_0(X4,X5)) = k2_xboole_0(X3,k3_xboole_0(X5,X4)) ),
    inference(superposition,[],[f208,f19])).

fof(f208,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_xboole_0(X3,X5),k2_xboole_0(X3,X4)) = k2_xboole_0(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f19,f14])).

fof(f16570,plain,(
    k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f16569,f14])).

fof(f16569,plain,(
    k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK2,sK1),sK0)) ),
    inference(forward_demodulation,[],[f16564,f7484])).

fof(f7484,plain,(
    ! [X125,X126,X124] : k2_xboole_0(k3_xboole_0(X124,X125),k3_xboole_0(X124,X126)) = k3_xboole_0(k2_xboole_0(X126,X125),X124) ),
    inference(forward_demodulation,[],[f7333,f6232])).

fof(f6232,plain,(
    ! [X8,X7,X9] : k3_xboole_0(k2_xboole_0(X8,X9),X7) = k3_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(X7,X9))) ),
    inference(superposition,[],[f812,f181])).

fof(f812,plain,(
    ! [X10,X8,X9] : k3_xboole_0(X10,X8) = k3_xboole_0(X8,k3_xboole_0(k2_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f43,f221])).

fof(f221,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f180,f16])).

fof(f180,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f19,f13])).

fof(f7333,plain,(
    ! [X125,X126,X124] : k2_xboole_0(k3_xboole_0(X124,X125),k3_xboole_0(X124,X126)) = k3_xboole_0(X124,k2_xboole_0(X126,k3_xboole_0(X124,X125))) ),
    inference(superposition,[],[f195,f106])).

fof(f106,plain,(
    ! [X10,X9] : k2_xboole_0(k3_xboole_0(X9,X10),X9) = X9 ),
    inference(superposition,[],[f77,f16])).

fof(f195,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k3_xboole_0(X4,X3)) = k3_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f19,f15])).

fof(f16564,plain,(
    k2_xboole_0(k3_xboole_0(sK1,sK2),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f16537,f59])).

fof(f16537,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,sK2)) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f16536,f14])).

fof(f16536,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f16535,f9354])).

fof(f16535,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k2_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k2_xboole_0(sK1,sK2),sK0)) ),
    inference(forward_demodulation,[],[f16534,f14943])).

fof(f14943,plain,(
    ! [X142,X140,X141,X139] : k2_xboole_0(k3_xboole_0(X139,X140),k3_xboole_0(k2_xboole_0(X139,X141),X142)) = k3_xboole_0(k2_xboole_0(X139,X141),k2_xboole_0(X142,k3_xboole_0(X139,X140))) ),
    inference(superposition,[],[f195,f124])).

fof(f124,plain,(
    ! [X6,X4,X5] : k2_xboole_0(X4,X6) = k2_xboole_0(k3_xboole_0(X4,X5),k2_xboole_0(X4,X6)) ),
    inference(superposition,[],[f18,f106])).

fof(f16534,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f16533,f10235])).

fof(f10235,plain,(
    ! [X134,X132,X133,X131] : k3_xboole_0(X134,k2_xboole_0(X131,k3_xboole_0(X132,X133))) = k3_xboole_0(X134,k2_xboole_0(X131,k3_xboole_0(X133,X132))) ),
    inference(forward_demodulation,[],[f9914,f19])).

fof(f9914,plain,(
    ! [X134,X132,X133,X131] : k3_xboole_0(X134,k3_xboole_0(k2_xboole_0(X131,X133),k2_xboole_0(X131,X132))) = k3_xboole_0(X134,k2_xboole_0(X131,k3_xboole_0(X132,X133))) ),
    inference(superposition,[],[f2245,f19])).

fof(f2245,plain,(
    ! [X12,X10,X11] : k3_xboole_0(X11,k3_xboole_0(X10,X12)) = k3_xboole_0(X11,k3_xboole_0(X12,X10)) ),
    inference(superposition,[],[f504,f43])).

fof(f504,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k3_xboole_0(X4,X5)) = k3_xboole_0(X4,k3_xboole_0(X3,X5)) ),
    inference(superposition,[],[f40,f17])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f17,f14])).

fof(f16533,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k3_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f16532,f14])).

fof(f16532,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)),k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f16217,f213])).

fof(f16217,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k2_xboole_0(sK0,sK2),k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f12,f15789])).

fof(f12,plain,(
    k2_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)),k3_xboole_0(sK2,sK0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)),k2_xboole_0(sK2,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) != k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_xboole_1)).

%------------------------------------------------------------------------------
