%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:52 EST 2020

% Result     : Theorem 25.69s
% Output     : Refutation 25.69s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 321 expanded)
%              Number of leaves         :   14 ( 103 expanded)
%              Depth                    :   22
%              Number of atoms          :  144 ( 432 expanded)
%              Number of equality atoms :   72 ( 277 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f54759,f101416])).

fof(f101416,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f101415])).

fof(f101415,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f101334,f35])).

fof(f35,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f101334,plain,
    ( r2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f54758,f101333])).

fof(f101333,plain,(
    ! [X391,X390,X392] : k4_xboole_0(k2_xboole_0(X390,X392),X391) = k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(X392,X391)) ),
    inference(forward_demodulation,[],[f101043,f69210])).

fof(f69210,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X1,X0),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X0),X2)) ),
    inference(forward_demodulation,[],[f69209,f56])).

fof(f56,plain,(
    ! [X2,X3] : k2_xboole_0(X3,X2) = k2_xboole_0(X3,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f55,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f69209,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X2)) ),
    inference(forward_demodulation,[],[f69208,f524])).

fof(f524,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X10,k2_xboole_0(X9,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X9,X11))) ),
    inference(forward_demodulation,[],[f481,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f481,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k2_xboole_0(X10,X9),X11) = k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11)) ),
    inference(superposition,[],[f32,f169])).

fof(f169,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f77,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f77,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f74,f25])).

fof(f74,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f25,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f26,f24])).

fof(f69208,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))),X2)) ),
    inference(forward_demodulation,[],[f69207,f17436])).

fof(f17436,plain,(
    ! [X61,X62,X60,X63] : k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X61,X62)),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X62,X61)),X63) ),
    inference(forward_demodulation,[],[f17435,f32])).

fof(f17435,plain,(
    ! [X61,X62,X60,X63] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X60,X61),X62),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X62,X61)),X63) ),
    inference(forward_demodulation,[],[f17296,f17269])).

fof(f17269,plain,(
    ! [X74,X72,X71,X73] : k4_xboole_0(k2_xboole_0(X74,k2_xboole_0(X71,X72)),X73) = k4_xboole_0(k2_xboole_0(X74,k2_xboole_0(X72,k2_xboole_0(X71,X73))),X73) ),
    inference(superposition,[],[f498,f478])).

fof(f478,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f32,f24])).

fof(f498,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k2_xboole_0(X14,X15),X16) = k4_xboole_0(k2_xboole_0(X14,k2_xboole_0(X15,X16)),X16) ),
    inference(superposition,[],[f26,f32])).

fof(f17296,plain,(
    ! [X61,X62,X60,X63] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X60,X61),X62),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X61,k2_xboole_0(X62,X63))),X63) ),
    inference(superposition,[],[f498,f32])).

fof(f69207,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X1)),X2)) ),
    inference(forward_demodulation,[],[f68593,f17432])).

fof(f17432,plain,(
    ! [X54,X52,X55,X53] : k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X52,X54)),X55) = k4_xboole_0(k2_xboole_0(X52,k2_xboole_0(X53,X54)),X55) ),
    inference(forward_demodulation,[],[f17431,f32])).

fof(f17431,plain,(
    ! [X54,X52,X55,X53] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X52,X54)),X55) ),
    inference(forward_demodulation,[],[f17430,f17268])).

fof(f17268,plain,(
    ! [X70,X68,X69,X67] : k4_xboole_0(k2_xboole_0(X70,k2_xboole_0(X67,X68)),X69) = k4_xboole_0(k2_xboole_0(X70,k2_xboole_0(X68,k2_xboole_0(X69,X67))),X69) ),
    inference(superposition,[],[f498,f3702])).

fof(f3702,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X24,X22)) ),
    inference(forward_demodulation,[],[f3701,f503])).

fof(f503,plain,(
    ! [X30,X31,X29] : k2_xboole_0(X31,k2_xboole_0(X29,X30)) = k2_xboole_0(X31,k2_xboole_0(X29,k2_xboole_0(X30,X31))) ),
    inference(superposition,[],[f56,f32])).

fof(f3701,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X22,X23))) ),
    inference(forward_demodulation,[],[f3598,f524])).

fof(f3598,plain,(
    ! [X24,X23,X22] : k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X22,k2_xboole_0(X24,k2_xboole_0(X22,X23)))) ),
    inference(superposition,[],[f478,f56])).

fof(f17430,plain,(
    ! [X54,X52,X55,X53] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X54,k2_xboole_0(X55,X52))),X55) ),
    inference(forward_demodulation,[],[f17294,f32])).

fof(f17294,plain,(
    ! [X54,X52,X55,X53] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(k2_xboole_0(X54,X55),X52)),X55) ),
    inference(superposition,[],[f498,f3702])).

fof(f68593,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X2)) ),
    inference(unit_resulting_resolution,[],[f512,f128,f54753])).

fof(f54753,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f54710])).

fof(f54710,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | k2_xboole_0(X2,X3) = X3 ) ),
    inference(resolution,[],[f1050,f9888])).

fof(f9888,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(k2_xboole_0(X0,X1),X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f65,plain,(
    ! [X2,X3] :
      ( r2_xboole_0(X2,k2_xboole_0(X3,X2))
      | k2_xboole_0(X3,X2) = X2 ) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f23,f24])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1050,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(k2_xboole_0(X2,X0),X1)
      | ~ r1_tarski(X2,X1)
      | k2_xboole_0(X2,X0) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f128,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X1,X0),X2)) ),
    inference(unit_resulting_resolution,[],[f85,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f85,plain,(
    ! [X8,X9] : r1_tarski(k2_xboole_0(X9,X8),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f41,f56])).

fof(f512,plain,(
    ! [X59,X57,X60,X58] : r1_tarski(k4_xboole_0(X59,X60),k4_xboole_0(k2_xboole_0(X57,k2_xboole_0(X58,X59)),X60)) ),
    inference(superposition,[],[f125,f32])).

fof(f125,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(unit_resulting_resolution,[],[f41,f33])).

fof(f101043,plain,(
    ! [X391,X390,X392] : k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(X392,X391)) = k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(k2_xboole_0(X390,X392),X391)) ),
    inference(superposition,[],[f12929,f20916])).

fof(f20916,plain,(
    ! [X187,X188,X186] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X187,X186),X188),X186) = k4_xboole_0(k2_xboole_0(X187,X188),X186) ),
    inference(forward_demodulation,[],[f20592,f51])).

fof(f20592,plain,(
    ! [X187,X188,X186] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X187,X186),X188),X186) = k4_xboole_0(k2_xboole_0(X186,k2_xboole_0(X187,X188)),X186) ),
    inference(superposition,[],[f51,f522])).

fof(f522,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f480,f32])).

fof(f480,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(k2_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f32,f25])).

fof(f12929,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f12928,f254])).

fof(f254,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f12928,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1)) ),
    inference(forward_demodulation,[],[f12684,f5711])).

fof(f5711,plain,(
    ! [X116,X117,X115] : k4_xboole_0(k2_xboole_0(X116,X117),X115) = k4_xboole_0(k2_xboole_0(X117,k2_xboole_0(X115,X116)),X115) ),
    inference(superposition,[],[f51,f487])).

fof(f487,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f32,f24])).

fof(f12684,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1)) ),
    inference(superposition,[],[f254,f26])).

fof(f54758,plain,
    ( r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54756])).

fof(f54756,plain,
    ( spl3_2
  <=> r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f54759,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f54555,f37,f54756])).

fof(f37,plain,
    ( spl3_1
  <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54555,plain,
    ( r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f125,f124,f39,f1050])).

fof(f39,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f124,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f23,f33])).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (5918)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (5922)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (5923)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (5922)Refutation not found, incomplete strategy% (5922)------------------------------
% 0.21/0.47  % (5922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5922)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5922)Memory used [KB]: 1535
% 0.21/0.47  % (5922)Time elapsed: 0.007 s
% 0.21/0.47  % (5922)------------------------------
% 0.21/0.47  % (5922)------------------------------
% 0.21/0.47  % (5914)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (5913)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (5911)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (5913)Refutation not found, incomplete strategy% (5913)------------------------------
% 0.21/0.49  % (5913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5913)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5913)Memory used [KB]: 1535
% 0.21/0.49  % (5913)Time elapsed: 0.076 s
% 0.21/0.49  % (5913)------------------------------
% 0.21/0.49  % (5913)------------------------------
% 0.21/0.49  % (5921)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5920)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (5921)Refutation not found, incomplete strategy% (5921)------------------------------
% 0.21/0.50  % (5921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5921)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5921)Memory used [KB]: 6012
% 0.21/0.50  % (5921)Time elapsed: 0.089 s
% 0.21/0.50  % (5921)------------------------------
% 0.21/0.50  % (5921)------------------------------
% 0.21/0.50  % (5912)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5912)Refutation not found, incomplete strategy% (5912)------------------------------
% 0.21/0.50  % (5912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5912)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5912)Memory used [KB]: 10618
% 0.21/0.50  % (5912)Time elapsed: 0.092 s
% 0.21/0.50  % (5912)------------------------------
% 0.21/0.50  % (5912)------------------------------
% 0.21/0.50  % (5910)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (5926)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (5919)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (5915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (5919)Refutation not found, incomplete strategy% (5919)------------------------------
% 0.21/0.50  % (5919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5919)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5919)Memory used [KB]: 6012
% 0.21/0.50  % (5919)Time elapsed: 0.107 s
% 0.21/0.50  % (5919)------------------------------
% 0.21/0.50  % (5919)------------------------------
% 0.21/0.51  % (5927)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (5917)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (5920)Refutation not found, incomplete strategy% (5920)------------------------------
% 0.21/0.51  % (5920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5920)Memory used [KB]: 10490
% 0.21/0.51  % (5920)Time elapsed: 0.101 s
% 0.21/0.51  % (5920)------------------------------
% 0.21/0.51  % (5920)------------------------------
% 0.21/0.52  % (5924)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (5924)Refutation not found, incomplete strategy% (5924)------------------------------
% 0.21/0.52  % (5924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5924)Memory used [KB]: 6012
% 0.21/0.52  % (5924)Time elapsed: 0.114 s
% 0.21/0.52  % (5924)------------------------------
% 0.21/0.52  % (5924)------------------------------
% 0.21/0.52  % (5925)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (5909)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (5909)Refutation not found, incomplete strategy% (5909)------------------------------
% 0.21/0.52  % (5909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5909)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5909)Memory used [KB]: 6140
% 0.21/0.52  % (5909)Time elapsed: 0.110 s
% 0.21/0.52  % (5909)------------------------------
% 0.21/0.52  % (5909)------------------------------
% 0.21/0.52  % (5929)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (5929)Refutation not found, incomplete strategy% (5929)------------------------------
% 0.21/0.52  % (5929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5929)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5929)Memory used [KB]: 10490
% 0.21/0.52  % (5929)Time elapsed: 0.116 s
% 0.21/0.52  % (5929)------------------------------
% 0.21/0.52  % (5929)------------------------------
% 0.21/0.52  % (5910)Refutation not found, incomplete strategy% (5910)------------------------------
% 0.21/0.52  % (5910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5910)Memory used [KB]: 10490
% 0.21/0.52  % (5910)Time elapsed: 0.116 s
% 0.21/0.52  % (5910)------------------------------
% 0.21/0.52  % (5910)------------------------------
% 0.21/0.52  % (5916)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (5928)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (5928)Refutation not found, incomplete strategy% (5928)------------------------------
% 0.21/0.53  % (5928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5928)Memory used [KB]: 6012
% 0.21/0.53  % (5928)Time elapsed: 0.108 s
% 0.21/0.53  % (5928)------------------------------
% 0.21/0.53  % (5928)------------------------------
% 4.61/0.95  % (5914)Time limit reached!
% 4.61/0.95  % (5914)------------------------------
% 4.61/0.95  % (5914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/0.95  % (5914)Termination reason: Time limit
% 4.61/0.95  % (5914)Termination phase: Saturation
% 4.61/0.95  
% 4.61/0.95  % (5914)Memory used [KB]: 18166
% 4.61/0.95  % (5914)Time elapsed: 0.500 s
% 4.61/0.95  % (5914)------------------------------
% 4.61/0.95  % (5914)------------------------------
% 4.61/1.00  % (5917)Time limit reached!
% 4.61/1.00  % (5917)------------------------------
% 4.61/1.00  % (5917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.61/1.00  % (5917)Termination reason: Time limit
% 4.61/1.00  % (5917)Termination phase: Saturation
% 4.61/1.00  
% 4.61/1.00  % (5917)Memory used [KB]: 15735
% 4.61/1.00  % (5917)Time elapsed: 0.600 s
% 4.61/1.00  % (5917)------------------------------
% 4.61/1.00  % (5917)------------------------------
% 7.04/1.30  % (5918)Time limit reached!
% 7.04/1.30  % (5918)------------------------------
% 7.04/1.30  % (5918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.04/1.30  % (5918)Termination reason: Time limit
% 7.04/1.30  % (5918)Termination phase: Saturation
% 7.04/1.30  
% 7.04/1.30  % (5918)Memory used [KB]: 34924
% 7.04/1.30  % (5918)Time elapsed: 0.900 s
% 7.04/1.30  % (5918)------------------------------
% 7.04/1.30  % (5918)------------------------------
% 8.97/1.51  % (5911)Time limit reached!
% 8.97/1.51  % (5911)------------------------------
% 8.97/1.51  % (5911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.97/1.51  % (5911)Termination reason: Time limit
% 8.97/1.51  % (5911)Termination phase: Saturation
% 8.97/1.51  
% 8.97/1.51  % (5911)Memory used [KB]: 42088
% 8.97/1.51  % (5911)Time elapsed: 1.100 s
% 8.97/1.51  % (5911)------------------------------
% 8.97/1.51  % (5911)------------------------------
% 12.67/2.11  % (5916)Time limit reached!
% 12.67/2.11  % (5916)------------------------------
% 12.67/2.11  % (5916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.67/2.11  % (5916)Termination reason: Time limit
% 12.67/2.11  % (5916)Termination phase: Saturation
% 12.67/2.11  
% 12.67/2.11  % (5916)Memory used [KB]: 23411
% 12.67/2.11  % (5916)Time elapsed: 1.700 s
% 12.67/2.11  % (5916)------------------------------
% 12.67/2.11  % (5916)------------------------------
% 25.69/4.71  % (5925)Refutation found. Thanks to Tanya!
% 25.69/4.71  % SZS status Theorem for theBenchmark
% 25.69/4.71  % SZS output start Proof for theBenchmark
% 25.69/4.71  fof(f101492,plain,(
% 25.69/4.71    $false),
% 25.69/4.71    inference(avatar_sat_refutation,[],[f40,f54759,f101416])).
% 25.69/4.71  fof(f101416,plain,(
% 25.69/4.71    ~spl3_2),
% 25.69/4.71    inference(avatar_contradiction_clause,[],[f101415])).
% 25.69/4.71  fof(f101415,plain,(
% 25.69/4.71    $false | ~spl3_2),
% 25.69/4.71    inference(subsumption_resolution,[],[f101334,f35])).
% 25.69/4.71  fof(f35,plain,(
% 25.69/4.71    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 25.69/4.71    inference(equality_resolution,[],[f29])).
% 25.69/4.71  fof(f29,plain,(
% 25.69/4.71    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f21])).
% 25.69/4.71  fof(f21,plain,(
% 25.69/4.71    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 25.69/4.71    inference(flattening,[],[f20])).
% 25.69/4.71  fof(f20,plain,(
% 25.69/4.71    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 25.69/4.71    inference(nnf_transformation,[],[f3])).
% 25.69/4.71  fof(f3,axiom,(
% 25.69/4.71    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 25.69/4.71  fof(f101334,plain,(
% 25.69/4.71    r2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK2),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) | ~spl3_2),
% 25.69/4.71    inference(backward_demodulation,[],[f54758,f101333])).
% 25.69/4.71  fof(f101333,plain,(
% 25.69/4.71    ( ! [X391,X390,X392] : (k4_xboole_0(k2_xboole_0(X390,X392),X391) = k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(X392,X391))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f101043,f69210])).
% 25.69/4.71  fof(f69210,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X1,X0),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,X0),X2))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f69209,f56])).
% 25.69/4.71  fof(f56,plain,(
% 25.69/4.71    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X3,k2_xboole_0(X2,X3))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f55,f25])).
% 25.69/4.71  fof(f25,plain,(
% 25.69/4.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 25.69/4.71    inference(cnf_transformation,[],[f5])).
% 25.69/4.71  fof(f5,axiom,(
% 25.69/4.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 25.69/4.71  fof(f55,plain,(
% 25.69/4.71    ( ! [X2,X3] : (k2_xboole_0(X3,k2_xboole_0(X2,X3)) = k2_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 25.69/4.71    inference(superposition,[],[f25,f26])).
% 25.69/4.71  fof(f26,plain,(
% 25.69/4.71    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f6])).
% 25.69/4.71  fof(f6,axiom,(
% 25.69/4.71    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 25.69/4.71  fof(f69209,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X0,X1)),X2))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f69208,f524])).
% 25.69/4.71  fof(f524,plain,(
% 25.69/4.71    ( ! [X10,X11,X9] : (k2_xboole_0(X10,k2_xboole_0(X9,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X9,X11)))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f481,f32])).
% 25.69/4.71  fof(f32,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 25.69/4.71    inference(cnf_transformation,[],[f8])).
% 25.69/4.71  fof(f8,axiom,(
% 25.69/4.71    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 25.69/4.71  fof(f481,plain,(
% 25.69/4.71    ( ! [X10,X11,X9] : (k2_xboole_0(k2_xboole_0(X10,X9),X11) = k2_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X9),X11))) )),
% 25.69/4.71    inference(superposition,[],[f32,f169])).
% 25.69/4.71  fof(f169,plain,(
% 25.69/4.71    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 25.69/4.71    inference(superposition,[],[f77,f24])).
% 25.69/4.71  fof(f24,plain,(
% 25.69/4.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f2])).
% 25.69/4.71  fof(f2,axiom,(
% 25.69/4.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 25.69/4.71  fof(f77,plain,(
% 25.69/4.71    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f74,f25])).
% 25.69/4.71  fof(f74,plain,(
% 25.69/4.71    ( ! [X6,X5] : (k2_xboole_0(X5,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 25.69/4.71    inference(superposition,[],[f25,f51])).
% 25.69/4.71  fof(f51,plain,(
% 25.69/4.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 25.69/4.71    inference(superposition,[],[f26,f24])).
% 25.69/4.71  fof(f69208,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))),X2))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f69207,f17436])).
% 25.69/4.71  fof(f17436,plain,(
% 25.69/4.71    ( ! [X61,X62,X60,X63] : (k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X61,X62)),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X62,X61)),X63)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f17435,f32])).
% 25.69/4.71  fof(f17435,plain,(
% 25.69/4.71    ( ! [X61,X62,X60,X63] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X60,X61),X62),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X62,X61)),X63)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f17296,f17269])).
% 25.69/4.71  fof(f17269,plain,(
% 25.69/4.71    ( ! [X74,X72,X71,X73] : (k4_xboole_0(k2_xboole_0(X74,k2_xboole_0(X71,X72)),X73) = k4_xboole_0(k2_xboole_0(X74,k2_xboole_0(X72,k2_xboole_0(X71,X73))),X73)) )),
% 25.69/4.71    inference(superposition,[],[f498,f478])).
% 25.69/4.71  fof(f478,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 25.69/4.71    inference(superposition,[],[f32,f24])).
% 25.69/4.71  fof(f498,plain,(
% 25.69/4.71    ( ! [X14,X15,X16] : (k4_xboole_0(k2_xboole_0(X14,X15),X16) = k4_xboole_0(k2_xboole_0(X14,k2_xboole_0(X15,X16)),X16)) )),
% 25.69/4.71    inference(superposition,[],[f26,f32])).
% 25.69/4.71  fof(f17296,plain,(
% 25.69/4.71    ( ! [X61,X62,X60,X63] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X60,X61),X62),X63) = k4_xboole_0(k2_xboole_0(X60,k2_xboole_0(X61,k2_xboole_0(X62,X63))),X63)) )),
% 25.69/4.71    inference(superposition,[],[f498,f32])).
% 25.69/4.71  fof(f69207,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X1)),X2))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f68593,f17432])).
% 25.69/4.71  fof(f17432,plain,(
% 25.69/4.71    ( ! [X54,X52,X55,X53] : (k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X52,X54)),X55) = k4_xboole_0(k2_xboole_0(X52,k2_xboole_0(X53,X54)),X55)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f17431,f32])).
% 25.69/4.71  fof(f17431,plain,(
% 25.69/4.71    ( ! [X54,X52,X55,X53] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X52,X54)),X55)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f17430,f17268])).
% 25.69/4.71  fof(f17268,plain,(
% 25.69/4.71    ( ! [X70,X68,X69,X67] : (k4_xboole_0(k2_xboole_0(X70,k2_xboole_0(X67,X68)),X69) = k4_xboole_0(k2_xboole_0(X70,k2_xboole_0(X68,k2_xboole_0(X69,X67))),X69)) )),
% 25.69/4.71    inference(superposition,[],[f498,f3702])).
% 25.69/4.71  fof(f3702,plain,(
% 25.69/4.71    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X24,X22))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f3701,f503])).
% 25.69/4.71  fof(f503,plain,(
% 25.69/4.71    ( ! [X30,X31,X29] : (k2_xboole_0(X31,k2_xboole_0(X29,X30)) = k2_xboole_0(X31,k2_xboole_0(X29,k2_xboole_0(X30,X31)))) )),
% 25.69/4.71    inference(superposition,[],[f56,f32])).
% 25.69/4.71  fof(f3701,plain,(
% 25.69/4.71    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X24,k2_xboole_0(X22,X23)))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f3598,f524])).
% 25.69/4.71  fof(f3598,plain,(
% 25.69/4.71    ( ! [X24,X23,X22] : (k2_xboole_0(k2_xboole_0(X22,X23),X24) = k2_xboole_0(X23,k2_xboole_0(X22,k2_xboole_0(X24,k2_xboole_0(X22,X23))))) )),
% 25.69/4.71    inference(superposition,[],[f478,f56])).
% 25.69/4.71  fof(f17430,plain,(
% 25.69/4.71    ( ! [X54,X52,X55,X53] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(X54,k2_xboole_0(X55,X52))),X55)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f17294,f32])).
% 25.69/4.71  fof(f17294,plain,(
% 25.69/4.71    ( ! [X54,X52,X55,X53] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X52,X53),X54),X55) = k4_xboole_0(k2_xboole_0(X53,k2_xboole_0(k2_xboole_0(X54,X55),X52)),X55)) )),
% 25.69/4.71    inference(superposition,[],[f498,f3702])).
% 25.69/4.71  fof(f68593,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X2) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)),X2))) )),
% 25.69/4.71    inference(unit_resulting_resolution,[],[f512,f128,f54753])).
% 25.69/4.71  fof(f54753,plain,(
% 25.69/4.71    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X3)) )),
% 25.69/4.71    inference(duplicate_literal_removal,[],[f54710])).
% 25.69/4.71  fof(f54710,plain,(
% 25.69/4.71    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | k2_xboole_0(X2,X3) = X3) )),
% 25.69/4.71    inference(resolution,[],[f1050,f9888])).
% 25.69/4.71  fof(f9888,plain,(
% 25.69/4.71    ( ! [X0,X1] : (~r2_xboole_0(k2_xboole_0(X0,X1),X1) | k2_xboole_0(X0,X1) = X1) )),
% 25.69/4.71    inference(resolution,[],[f65,f27])).
% 25.69/4.71  fof(f27,plain,(
% 25.69/4.71    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f14])).
% 25.69/4.71  fof(f14,plain,(
% 25.69/4.71    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 25.69/4.71    inference(ennf_transformation,[],[f1])).
% 25.69/4.71  fof(f1,axiom,(
% 25.69/4.71    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 25.69/4.71  fof(f65,plain,(
% 25.69/4.71    ( ! [X2,X3] : (r2_xboole_0(X2,k2_xboole_0(X3,X2)) | k2_xboole_0(X3,X2) = X2) )),
% 25.69/4.71    inference(resolution,[],[f30,f41])).
% 25.69/4.71  fof(f41,plain,(
% 25.69/4.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 25.69/4.71    inference(superposition,[],[f23,f24])).
% 25.69/4.71  fof(f23,plain,(
% 25.69/4.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 25.69/4.71    inference(cnf_transformation,[],[f9])).
% 25.69/4.71  fof(f9,axiom,(
% 25.69/4.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 25.69/4.71  fof(f30,plain,(
% 25.69/4.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f21])).
% 25.69/4.71  fof(f1050,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r2_xboole_0(k2_xboole_0(X2,X0),X1) | ~r1_tarski(X2,X1) | k2_xboole_0(X2,X0) = X1 | ~r1_tarski(X0,X1)) )),
% 25.69/4.71    inference(resolution,[],[f34,f30])).
% 25.69/4.71  fof(f34,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f17])).
% 25.69/4.71  fof(f17,plain,(
% 25.69/4.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 25.69/4.71    inference(flattening,[],[f16])).
% 25.69/4.71  fof(f16,plain,(
% 25.69/4.71    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 25.69/4.71    inference(ennf_transformation,[],[f10])).
% 25.69/4.71  fof(f10,axiom,(
% 25.69/4.71    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 25.69/4.71  fof(f128,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X2),k4_xboole_0(k2_xboole_0(X1,X0),X2))) )),
% 25.69/4.71    inference(unit_resulting_resolution,[],[f85,f33])).
% 25.69/4.71  fof(f33,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 25.69/4.71    inference(cnf_transformation,[],[f15])).
% 25.69/4.71  fof(f15,plain,(
% 25.69/4.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 25.69/4.71    inference(ennf_transformation,[],[f4])).
% 25.69/4.71  fof(f4,axiom,(
% 25.69/4.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 25.69/4.71  fof(f85,plain,(
% 25.69/4.71    ( ! [X8,X9] : (r1_tarski(k2_xboole_0(X9,X8),k2_xboole_0(X8,X9))) )),
% 25.69/4.71    inference(superposition,[],[f41,f56])).
% 25.69/4.71  fof(f512,plain,(
% 25.69/4.71    ( ! [X59,X57,X60,X58] : (r1_tarski(k4_xboole_0(X59,X60),k4_xboole_0(k2_xboole_0(X57,k2_xboole_0(X58,X59)),X60))) )),
% 25.69/4.71    inference(superposition,[],[f125,f32])).
% 25.69/4.71  fof(f125,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 25.69/4.71    inference(unit_resulting_resolution,[],[f41,f33])).
% 25.69/4.71  fof(f101043,plain,(
% 25.69/4.71    ( ! [X391,X390,X392] : (k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(X392,X391)) = k2_xboole_0(k4_xboole_0(X390,X391),k4_xboole_0(k2_xboole_0(X390,X392),X391))) )),
% 25.69/4.71    inference(superposition,[],[f12929,f20916])).
% 25.69/4.71  fof(f20916,plain,(
% 25.69/4.71    ( ! [X187,X188,X186] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X187,X186),X188),X186) = k4_xboole_0(k2_xboole_0(X187,X188),X186)) )),
% 25.69/4.71    inference(forward_demodulation,[],[f20592,f51])).
% 25.69/4.71  fof(f20592,plain,(
% 25.69/4.71    ( ! [X187,X188,X186] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X187,X186),X188),X186) = k4_xboole_0(k2_xboole_0(X186,k2_xboole_0(X187,X188)),X186)) )),
% 25.69/4.71    inference(superposition,[],[f51,f522])).
% 25.69/4.71  fof(f522,plain,(
% 25.69/4.71    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f480,f32])).
% 25.69/4.71  fof(f480,plain,(
% 25.69/4.71    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X7,X6),X8)) = k2_xboole_0(k2_xboole_0(X6,X7),X8)) )),
% 25.69/4.71    inference(superposition,[],[f32,f25])).
% 25.69/4.71  fof(f12929,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f12928,f254])).
% 25.69/4.71  fof(f254,plain,(
% 25.69/4.71    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 25.69/4.71    inference(superposition,[],[f25,f31])).
% 25.69/4.71  fof(f31,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 25.69/4.71    inference(cnf_transformation,[],[f7])).
% 25.69/4.71  fof(f7,axiom,(
% 25.69/4.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 25.69/4.71  fof(f12928,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X0),X1))) )),
% 25.69/4.71    inference(forward_demodulation,[],[f12684,f5711])).
% 25.69/4.71  fof(f5711,plain,(
% 25.69/4.71    ( ! [X116,X117,X115] : (k4_xboole_0(k2_xboole_0(X116,X117),X115) = k4_xboole_0(k2_xboole_0(X117,k2_xboole_0(X115,X116)),X115)) )),
% 25.69/4.71    inference(superposition,[],[f51,f487])).
% 25.69/4.71  fof(f487,plain,(
% 25.69/4.71    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7))) )),
% 25.69/4.71    inference(superposition,[],[f32,f24])).
% 25.69/4.71  fof(f12684,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X1))) )),
% 25.69/4.71    inference(superposition,[],[f254,f26])).
% 25.69/4.71  fof(f54758,plain,(
% 25.69/4.71    r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) | ~spl3_2),
% 25.69/4.71    inference(avatar_component_clause,[],[f54756])).
% 25.69/4.71  fof(f54756,plain,(
% 25.69/4.71    spl3_2 <=> r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 25.69/4.71    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 25.69/4.71  fof(f54759,plain,(
% 25.69/4.71    spl3_2 | spl3_1),
% 25.69/4.71    inference(avatar_split_clause,[],[f54555,f37,f54756])).
% 25.69/4.71  fof(f37,plain,(
% 25.69/4.71    spl3_1 <=> k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 25.69/4.71    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 25.69/4.71  fof(f54555,plain,(
% 25.69/4.71    r2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) | spl3_1),
% 25.69/4.71    inference(unit_resulting_resolution,[],[f125,f124,f39,f1050])).
% 25.69/4.71  fof(f39,plain,(
% 25.69/4.71    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_1),
% 25.69/4.71    inference(avatar_component_clause,[],[f37])).
% 25.69/4.71  fof(f124,plain,(
% 25.69/4.71    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1))) )),
% 25.69/4.71    inference(unit_resulting_resolution,[],[f23,f33])).
% 25.69/4.71  fof(f40,plain,(
% 25.69/4.71    ~spl3_1),
% 25.69/4.71    inference(avatar_split_clause,[],[f22,f37])).
% 25.69/4.71  fof(f22,plain,(
% 25.69/4.71    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 25.69/4.71    inference(cnf_transformation,[],[f19])).
% 25.69/4.71  fof(f19,plain,(
% 25.69/4.71    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 25.69/4.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f18])).
% 25.69/4.71  fof(f18,plain,(
% 25.69/4.71    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) => k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 25.69/4.71    introduced(choice_axiom,[])).
% 25.69/4.71  fof(f13,plain,(
% 25.69/4.71    ? [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 25.69/4.71    inference(ennf_transformation,[],[f12])).
% 25.69/4.71  fof(f12,negated_conjecture,(
% 25.69/4.71    ~! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 25.69/4.71    inference(negated_conjecture,[],[f11])).
% 25.69/4.71  fof(f11,conjecture,(
% 25.69/4.71    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 25.69/4.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 25.69/4.71  % SZS output end Proof for theBenchmark
% 25.69/4.71  % (5925)------------------------------
% 25.69/4.71  % (5925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.69/4.71  % (5925)Termination reason: Refutation
% 25.69/4.71  
% 25.69/4.71  % (5925)Memory used [KB]: 86224
% 25.69/4.71  % (5925)Time elapsed: 4.307 s
% 25.69/4.71  % (5925)------------------------------
% 25.69/4.71  % (5925)------------------------------
% 25.69/4.72  % (5908)Success in time 4.366 s
%------------------------------------------------------------------------------
