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
% DateTime   : Thu Dec  3 12:32:12 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   99 (17067 expanded)
%              Number of leaves         :   12 (5973 expanded)
%              Depth                    :   34
%              Number of atoms          :  112 (24834 expanded)
%              Number of equality atoms :   90 (15302 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1131,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1128])).

fof(f1128,plain,(
    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f909,f939])).

fof(f939,plain,(
    ! [X45] : k2_xboole_0(X45,k1_xboole_0) = X45 ),
    inference(forward_demodulation,[],[f924,f933])).

fof(f933,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X29)) = X29 ),
    inference(forward_demodulation,[],[f922,f851])).

fof(f851,plain,(
    ! [X62] : k4_xboole_0(X62,k1_xboole_0) = X62 ),
    inference(forward_demodulation,[],[f845,f829])).

fof(f829,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f44,f828])).

fof(f828,plain,(
    ! [X52] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X52) ),
    inference(forward_demodulation,[],[f827,f590])).

fof(f590,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f588,f119])).

fof(f119,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(forward_demodulation,[],[f116,f70])).

fof(f70,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f14])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f66,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f60,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f28,f28])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
    inference(superposition,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X0,X1),X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f588,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f329,f546])).

fof(f546,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f532,f70])).

fof(f532,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f523,f41])).

fof(f523,plain,(
    ! [X10,X11] : sP0(X11,k4_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f522,f46])).

fof(f522,plain,(
    ! [X10,X11] : sP0(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))),k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) ),
    inference(forward_demodulation,[],[f486,f45])).

fof(f486,plain,(
    ! [X10,X11] : sP0(X11,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X10)),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X10))) ),
    inference(superposition,[],[f372,f192])).

fof(f192,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f163,f70])).

fof(f163,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f70,f45])).

fof(f372,plain,(
    ! [X33,X31,X32] : sP0(X33,k4_xboole_0(X31,k4_xboole_0(X31,X32)),k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X32,X33)))) ),
    inference(superposition,[],[f50,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f33,f28,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f329,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f328,f70])).

fof(f328,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) ),
    inference(forward_demodulation,[],[f322,f49])).

fof(f322,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f42,f45])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f827,plain,(
    ! [X52] : k4_xboole_0(k1_xboole_0,X52) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X52),k1_xboole_0) ),
    inference(forward_demodulation,[],[f801,f590])).

fof(f801,plain,(
    ! [X52] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X52),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X52),k4_xboole_0(k1_xboole_0,X52)),k4_xboole_0(k1_xboole_0,X52)) ),
    inference(superposition,[],[f541,f661])).

fof(f661,plain,(
    ! [X22] : k4_xboole_0(k1_xboole_0,X22) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)) ),
    inference(backward_demodulation,[],[f103,f651])).

fof(f651,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f641,f49])).

fof(f641,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X15),X16) = X16 ),
    inference(forward_demodulation,[],[f630,f192])).

fof(f630,plain,(
    ! [X15,X16] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,X16)),X16) = X16 ),
    inference(superposition,[],[f589,f532])).

fof(f589,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = X6 ),
    inference(forward_demodulation,[],[f587,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f47,f45])).

fof(f587,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f334,f546])).

fof(f334,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) ),
    inference(forward_demodulation,[],[f333,f70])).

fof(f333,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X6,X7)))),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) ),
    inference(forward_demodulation,[],[f325,f49])).

fof(f325,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) ),
    inference(superposition,[],[f42,f70])).

fof(f103,plain,(
    ! [X22] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X22,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X22)) ),
    inference(forward_demodulation,[],[f96,f49])).

fof(f96,plain,(
    ! [X22] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)),k1_xboole_0),k4_xboole_0(k1_xboole_0,X22)) ),
    inference(superposition,[],[f44,f46])).

fof(f541,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f42,f532])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f845,plain,(
    ! [X62] : k4_xboole_0(X62,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X62,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f583,f828])).

fof(f583,plain,(
    ! [X62] : k4_xboole_0(X62,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X62,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X62,k1_xboole_0))) ),
    inference(superposition,[],[f44,f532])).

fof(f922,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k1_xboole_0) ),
    inference(backward_demodulation,[],[f602,f872])).

fof(f872,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f192,f854])).

fof(f854,plain,(
    ! [X41] : k1_xboole_0 = k4_xboole_0(X41,X41) ),
    inference(backward_demodulation,[],[f830,f851])).

fof(f830,plain,(
    ! [X41] : k1_xboole_0 = k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f654,f828])).

fof(f654,plain,(
    ! [X41] : k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X41) ),
    inference(backward_demodulation,[],[f207,f653])).

fof(f653,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f643,f49])).

fof(f643,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f641,f45])).

fof(f207,plain,(
    ! [X41] : k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(k1_xboole_0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X41)) ),
    inference(forward_demodulation,[],[f191,f49])).

fof(f191,plain,(
    ! [X41] : k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)),k1_xboole_0),k4_xboole_0(k1_xboole_0,X41)) ),
    inference(superposition,[],[f44,f70])).

fof(f602,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X28)) ),
    inference(forward_demodulation,[],[f568,f192])).

fof(f568,plain,(
    ! [X28,X29] : k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X29))) ),
    inference(superposition,[],[f70,f532])).

fof(f924,plain,(
    ! [X45,X44] : k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k1_xboole_0) = X45 ),
    inference(backward_demodulation,[],[f607,f872])).

fof(f607,plain,(
    ! [X45,X44] : k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k4_xboole_0(k4_xboole_0(X44,X45),X44)) = X45 ),
    inference(forward_demodulation,[],[f576,f192])).

fof(f576,plain,(
    ! [X45,X44] : k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45))) = X45 ),
    inference(superposition,[],[f119,f532])).

fof(f909,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f52,f871])).

fof(f871,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(backward_demodulation,[],[f558,f854])).

fof(f558,plain,(
    ! [X8,X7] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X8))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f45,f532])).

fof(f52,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1)))) ),
    inference(backward_demodulation,[],[f51,f49])).

fof(f51,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(backward_demodulation,[],[f43,f46])).

fof(f43,plain,(
    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1)) ),
    inference(definition_unfolding,[],[f24,f31,f28])).

fof(f24,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (8610)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (8602)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (8596)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (8610)Refutation not found, incomplete strategy% (8610)------------------------------
% 0.20/0.50  % (8610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (8592)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (8610)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (8610)Memory used [KB]: 10618
% 0.20/0.50  % (8610)Time elapsed: 0.056 s
% 0.20/0.50  % (8610)------------------------------
% 0.20/0.50  % (8610)------------------------------
% 0.20/0.50  % (8594)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (8590)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (8604)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (8596)Refutation not found, incomplete strategy% (8596)------------------------------
% 0.20/0.51  % (8596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (8596)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (8596)Memory used [KB]: 10618
% 0.20/0.51  % (8596)Time elapsed: 0.101 s
% 0.20/0.51  % (8596)------------------------------
% 0.20/0.51  % (8596)------------------------------
% 0.20/0.51  % (8601)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (8612)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (8608)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (8588)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (8588)Refutation not found, incomplete strategy% (8588)------------------------------
% 0.20/0.52  % (8588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8588)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8588)Memory used [KB]: 1663
% 0.20/0.52  % (8588)Time elapsed: 0.105 s
% 0.20/0.52  % (8588)------------------------------
% 0.20/0.52  % (8588)------------------------------
% 0.20/0.52  % (8600)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (8592)Refutation not found, incomplete strategy% (8592)------------------------------
% 0.20/0.52  % (8592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8592)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8592)Memory used [KB]: 6140
% 0.20/0.52  % (8592)Time elapsed: 0.120 s
% 0.20/0.52  % (8592)------------------------------
% 0.20/0.52  % (8592)------------------------------
% 0.20/0.53  % (8613)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (8614)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (8616)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (8591)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (8589)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (8615)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (8590)Refutation not found, incomplete strategy% (8590)------------------------------
% 0.20/0.53  % (8590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8590)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8590)Memory used [KB]: 10618
% 0.20/0.53  % (8590)Time elapsed: 0.118 s
% 0.20/0.53  % (8590)------------------------------
% 0.20/0.53  % (8590)------------------------------
% 0.20/0.53  % (8593)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (8599)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (8608)Refutation not found, incomplete strategy% (8608)------------------------------
% 0.20/0.53  % (8608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (8608)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (8608)Memory used [KB]: 10618
% 0.20/0.53  % (8608)Time elapsed: 0.133 s
% 0.20/0.53  % (8608)------------------------------
% 0.20/0.53  % (8608)------------------------------
% 0.20/0.53  % (8603)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (8605)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (8606)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8605)Refutation not found, incomplete strategy% (8605)------------------------------
% 0.20/0.54  % (8605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8605)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8605)Memory used [KB]: 10618
% 0.20/0.54  % (8605)Time elapsed: 0.130 s
% 0.20/0.54  % (8605)------------------------------
% 0.20/0.54  % (8605)------------------------------
% 0.20/0.54  % (8607)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (8597)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (8597)Refutation not found, incomplete strategy% (8597)------------------------------
% 0.20/0.54  % (8597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8597)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8597)Memory used [KB]: 10618
% 0.20/0.54  % (8597)Time elapsed: 0.141 s
% 0.20/0.54  % (8597)------------------------------
% 0.20/0.54  % (8597)------------------------------
% 0.20/0.54  % (8613)Refutation not found, incomplete strategy% (8613)------------------------------
% 0.20/0.54  % (8613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8613)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8613)Memory used [KB]: 6140
% 0.20/0.54  % (8613)Time elapsed: 0.139 s
% 0.20/0.54  % (8613)------------------------------
% 0.20/0.54  % (8613)------------------------------
% 0.20/0.54  % (8598)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (8598)Refutation not found, incomplete strategy% (8598)------------------------------
% 0.20/0.54  % (8598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (8598)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (8598)Memory used [KB]: 10618
% 0.20/0.54  % (8598)Time elapsed: 0.140 s
% 0.20/0.54  % (8598)------------------------------
% 0.20/0.54  % (8598)------------------------------
% 0.20/0.54  % (8617)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (8609)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (8609)Refutation not found, incomplete strategy% (8609)------------------------------
% 0.20/0.55  % (8609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (8609)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (8609)Memory used [KB]: 1663
% 0.20/0.55  % (8609)Time elapsed: 0.152 s
% 0.20/0.55  % (8609)------------------------------
% 0.20/0.55  % (8609)------------------------------
% 1.57/0.55  % (8611)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.57/0.55  % (8611)Refutation not found, incomplete strategy% (8611)------------------------------
% 1.57/0.55  % (8611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.55  % (8611)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.55  
% 1.57/0.55  % (8611)Memory used [KB]: 1663
% 1.57/0.55  % (8611)Time elapsed: 0.148 s
% 1.57/0.55  % (8611)------------------------------
% 1.57/0.55  % (8611)------------------------------
% 1.57/0.56  % (8595)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.72/0.59  % (8600)Refutation found. Thanks to Tanya!
% 1.72/0.59  % SZS status Theorem for theBenchmark
% 1.72/0.59  % SZS output start Proof for theBenchmark
% 1.72/0.59  fof(f1131,plain,(
% 1.72/0.59    $false),
% 1.72/0.59    inference(trivial_inequality_removal,[],[f1128])).
% 1.72/0.59  fof(f1128,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2)),
% 1.72/0.59    inference(superposition,[],[f909,f939])).
% 1.72/0.59  fof(f939,plain,(
% 1.72/0.59    ( ! [X45] : (k2_xboole_0(X45,k1_xboole_0) = X45) )),
% 1.72/0.59    inference(forward_demodulation,[],[f924,f933])).
% 1.72/0.59  fof(f933,plain,(
% 1.72/0.59    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X29)) = X29) )),
% 1.72/0.59    inference(forward_demodulation,[],[f922,f851])).
% 1.72/0.59  fof(f851,plain,(
% 1.72/0.59    ( ! [X62] : (k4_xboole_0(X62,k1_xboole_0) = X62) )),
% 1.72/0.59    inference(forward_demodulation,[],[f845,f829])).
% 1.72/0.59  fof(f829,plain,(
% 1.72/0.59    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 1.72/0.59    inference(backward_demodulation,[],[f44,f828])).
% 1.72/0.59  fof(f828,plain,(
% 1.72/0.59    ( ! [X52] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X52)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f827,f590])).
% 1.72/0.59  fof(f590,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.72/0.59    inference(forward_demodulation,[],[f588,f119])).
% 1.72/0.59  fof(f119,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 1.72/0.59    inference(forward_demodulation,[],[f116,f70])).
% 1.72/0.59  fof(f70,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.72/0.59    inference(resolution,[],[f67,f41])).
% 1.72/0.59  fof(f41,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.72/0.59    inference(cnf_transformation,[],[f23])).
% 1.72/0.59  fof(f23,plain,(
% 1.72/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.72/0.59    inference(nnf_transformation,[],[f15])).
% 1.72/0.59  fof(f15,plain,(
% 1.72/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.72/0.59    inference(definition_folding,[],[f2,f14])).
% 1.72/0.59  fof(f14,plain,(
% 1.72/0.59    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.72/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.72/0.59  fof(f2,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.72/0.59  fof(f67,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f66,f46])).
% 1.72/0.59  fof(f46,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f29,f28])).
% 1.72/0.59  fof(f28,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f6])).
% 1.72/0.59  fof(f6,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.72/0.59  fof(f29,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f5])).
% 1.72/0.59  fof(f5,axiom,(
% 1.72/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.72/0.59  fof(f66,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f60,f45])).
% 1.72/0.59  fof(f45,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f26,f28,f28])).
% 1.72/0.59  fof(f26,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f1])).
% 1.72/0.59  fof(f1,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.59  fof(f60,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sP0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) )),
% 1.72/0.59    inference(superposition,[],[f55,f45])).
% 1.72/0.59  fof(f55,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sP0(k4_xboole_0(X0,X1),X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.72/0.59    inference(superposition,[],[f50,f45])).
% 1.72/0.59  fof(f50,plain,(
% 1.72/0.59    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(equality_resolution,[],[f40])).
% 1.72/0.59  fof(f40,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.72/0.59    inference(cnf_transformation,[],[f23])).
% 1.72/0.59  fof(f116,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0) )),
% 1.72/0.59    inference(superposition,[],[f47,f45])).
% 1.72/0.59  fof(f47,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.72/0.59    inference(definition_unfolding,[],[f30,f28])).
% 1.72/0.59  fof(f30,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f8])).
% 1.72/0.59  fof(f8,axiom,(
% 1.72/0.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.72/0.59  fof(f588,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f329,f546])).
% 1.72/0.59  fof(f546,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6)))) )),
% 1.72/0.59    inference(superposition,[],[f532,f70])).
% 1.72/0.59  fof(f532,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.72/0.59    inference(resolution,[],[f523,f41])).
% 1.72/0.59  fof(f523,plain,(
% 1.72/0.59    ( ! [X10,X11] : (sP0(X11,k4_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f522,f46])).
% 1.72/0.59  fof(f522,plain,(
% 1.72/0.59    ( ! [X10,X11] : (sP0(X11,k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))),k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X10,X11))))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f486,f45])).
% 1.72/0.59  fof(f486,plain,(
% 1.72/0.59    ( ! [X10,X11] : (sP0(X11,k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X10)),k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(k4_xboole_0(X10,X11),X10)))) )),
% 1.72/0.59    inference(superposition,[],[f372,f192])).
% 1.72/0.59  fof(f192,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f163,f70])).
% 1.72/0.59  fof(f163,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 1.72/0.59    inference(superposition,[],[f70,f45])).
% 1.72/0.59  fof(f372,plain,(
% 1.72/0.59    ( ! [X33,X31,X32] : (sP0(X33,k4_xboole_0(X31,k4_xboole_0(X31,X32)),k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(X32,X33))))) )),
% 1.72/0.59    inference(superposition,[],[f50,f49])).
% 1.72/0.59  fof(f49,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.72/0.59    inference(definition_unfolding,[],[f33,f28,f28])).
% 1.72/0.59  fof(f33,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f7])).
% 1.72/0.59  fof(f7,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.72/0.59  fof(f329,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f328,f70])).
% 1.72/0.59  fof(f328,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f322,f49])).
% 1.72/0.59  fof(f322,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)))) )),
% 1.72/0.59    inference(superposition,[],[f42,f45])).
% 1.72/0.59  fof(f42,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f27,f31])).
% 1.72/0.59  fof(f31,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f3])).
% 1.72/0.59  fof(f3,axiom,(
% 1.72/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.72/0.59  fof(f27,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f10])).
% 1.72/0.59  fof(f10,axiom,(
% 1.72/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.72/0.59  fof(f827,plain,(
% 1.72/0.59    ( ! [X52] : (k4_xboole_0(k1_xboole_0,X52) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X52),k1_xboole_0)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f801,f590])).
% 1.72/0.59  fof(f801,plain,(
% 1.72/0.59    ( ! [X52] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X52),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X52),k4_xboole_0(k1_xboole_0,X52)),k4_xboole_0(k1_xboole_0,X52))) )),
% 1.72/0.59    inference(superposition,[],[f541,f661])).
% 1.72/0.59  fof(f661,plain,(
% 1.72/0.59    ( ! [X22] : (k4_xboole_0(k1_xboole_0,X22) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f103,f651])).
% 1.72/0.59  fof(f651,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(superposition,[],[f641,f49])).
% 1.72/0.59  fof(f641,plain,(
% 1.72/0.59    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),X15),X16) = X16) )),
% 1.72/0.59    inference(forward_demodulation,[],[f630,f192])).
% 1.72/0.59  fof(f630,plain,(
% 1.72/0.59    ( ! [X15,X16] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X15,X16),k4_xboole_0(X15,X16)),X16) = X16) )),
% 1.72/0.59    inference(superposition,[],[f589,f532])).
% 1.72/0.59  fof(f589,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = X6) )),
% 1.72/0.59    inference(forward_demodulation,[],[f587,f113])).
% 1.72/0.59  fof(f113,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 1.72/0.59    inference(superposition,[],[f47,f45])).
% 1.72/0.59  fof(f587,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f334,f546])).
% 1.72/0.59  fof(f334,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f333,f70])).
% 1.72/0.59  fof(f333,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X6,k4_xboole_0(X6,X7)))),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f325,f49])).
% 1.72/0.59  fof(f325,plain,(
% 1.72/0.59    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)),k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X7,k4_xboole_0(X7,X6))))) )),
% 1.72/0.59    inference(superposition,[],[f42,f70])).
% 1.72/0.59  fof(f103,plain,(
% 1.72/0.59    ( ! [X22] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X22,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X22))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f96,f49])).
% 1.72/0.59  fof(f96,plain,(
% 1.72/0.59    ( ! [X22] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X22)),k1_xboole_0),k4_xboole_0(k1_xboole_0,X22))) )),
% 1.72/0.59    inference(superposition,[],[f44,f46])).
% 1.72/0.59  fof(f541,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f42,f532])).
% 1.72/0.59  fof(f44,plain,(
% 1.72/0.59    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.72/0.59    inference(definition_unfolding,[],[f25,f31])).
% 1.72/0.59  fof(f25,plain,(
% 1.72/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f9])).
% 1.72/0.59  fof(f9,axiom,(
% 1.72/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.59  fof(f845,plain,(
% 1.72/0.59    ( ! [X62] : (k4_xboole_0(X62,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X62,k1_xboole_0),k1_xboole_0)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f583,f828])).
% 1.72/0.59  fof(f583,plain,(
% 1.72/0.59    ( ! [X62] : (k4_xboole_0(X62,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X62,k1_xboole_0),k4_xboole_0(k1_xboole_0,k4_xboole_0(X62,k1_xboole_0)))) )),
% 1.72/0.59    inference(superposition,[],[f44,f532])).
% 1.72/0.59  fof(f922,plain,(
% 1.72/0.59    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k1_xboole_0)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f602,f872])).
% 1.72/0.59  fof(f872,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f192,f854])).
% 1.72/0.59  fof(f854,plain,(
% 1.72/0.59    ( ! [X41] : (k1_xboole_0 = k4_xboole_0(X41,X41)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f830,f851])).
% 1.72/0.59  fof(f830,plain,(
% 1.72/0.59    ( ! [X41] : (k1_xboole_0 = k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f654,f828])).
% 1.72/0.59  fof(f654,plain,(
% 1.72/0.59    ( ! [X41] : (k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,X41)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f207,f653])).
% 1.72/0.59  fof(f653,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X0))),k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f643,f49])).
% 1.72/0.59  fof(f643,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(superposition,[],[f641,f45])).
% 1.72/0.59  fof(f207,plain,(
% 1.72/0.59    ( ! [X41] : (k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k4_xboole_0(k1_xboole_0,k1_xboole_0))),k4_xboole_0(k1_xboole_0,X41))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f191,f49])).
% 1.72/0.59  fof(f191,plain,(
% 1.72/0.59    ( ! [X41] : (k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X41,k4_xboole_0(X41,k1_xboole_0)),k1_xboole_0),k4_xboole_0(k1_xboole_0,X41))) )),
% 1.72/0.59    inference(superposition,[],[f44,f70])).
% 1.72/0.59  fof(f602,plain,(
% 1.72/0.59    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),X28))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f568,f192])).
% 1.72/0.59  fof(f568,plain,(
% 1.72/0.59    ( ! [X28,X29] : (k4_xboole_0(X29,k4_xboole_0(X28,X29)) = k4_xboole_0(X29,k4_xboole_0(k4_xboole_0(X28,X29),k4_xboole_0(X28,X29)))) )),
% 1.72/0.59    inference(superposition,[],[f70,f532])).
% 1.72/0.59  fof(f924,plain,(
% 1.72/0.59    ( ! [X45,X44] : (k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k1_xboole_0) = X45) )),
% 1.72/0.59    inference(backward_demodulation,[],[f607,f872])).
% 1.72/0.59  fof(f607,plain,(
% 1.72/0.59    ( ! [X45,X44] : (k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k4_xboole_0(k4_xboole_0(X44,X45),X44)) = X45) )),
% 1.72/0.59    inference(forward_demodulation,[],[f576,f192])).
% 1.72/0.59  fof(f576,plain,(
% 1.72/0.59    ( ! [X45,X44] : (k2_xboole_0(k4_xboole_0(X45,k4_xboole_0(X44,X45)),k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45))) = X45) )),
% 1.72/0.59    inference(superposition,[],[f119,f532])).
% 1.72/0.59  fof(f909,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.72/0.59    inference(backward_demodulation,[],[f52,f871])).
% 1.72/0.59  fof(f871,plain,(
% 1.72/0.59    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f558,f854])).
% 1.72/0.59  fof(f558,plain,(
% 1.72/0.59    ( ! [X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X7,X8))) = k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 1.72/0.59    inference(superposition,[],[f45,f532])).
% 1.72/0.59  fof(f52,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK2,sK1))))),
% 1.72/0.59    inference(backward_demodulation,[],[f51,f49])).
% 1.72/0.59  fof(f51,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 1.72/0.59    inference(backward_demodulation,[],[f43,f46])).
% 1.72/0.59  fof(f43,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK1))),
% 1.72/0.59    inference(definition_unfolding,[],[f24,f31,f28])).
% 1.72/0.59  fof(f24,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.72/0.59    inference(cnf_transformation,[],[f17])).
% 1.72/0.59  fof(f17,plain,(
% 1.72/0.59    k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.72/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f16])).
% 1.72/0.59  fof(f16,plain,(
% 1.72/0.59    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK1,sK2) != k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.72/0.59    introduced(choice_axiom,[])).
% 1.72/0.59  fof(f13,plain,(
% 1.72/0.59    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    inference(ennf_transformation,[],[f12])).
% 1.72/0.59  fof(f12,negated_conjecture,(
% 1.72/0.59    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    inference(negated_conjecture,[],[f11])).
% 1.72/0.59  fof(f11,conjecture,(
% 1.72/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.72/0.59  % SZS output end Proof for theBenchmark
% 1.72/0.59  % (8600)------------------------------
% 1.72/0.59  % (8600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (8600)Termination reason: Refutation
% 1.72/0.59  
% 1.72/0.59  % (8600)Memory used [KB]: 6908
% 1.72/0.59  % (8600)Time elapsed: 0.197 s
% 1.72/0.59  % (8600)------------------------------
% 1.72/0.59  % (8600)------------------------------
% 1.72/0.59  % (8587)Success in time 0.233 s
%------------------------------------------------------------------------------
