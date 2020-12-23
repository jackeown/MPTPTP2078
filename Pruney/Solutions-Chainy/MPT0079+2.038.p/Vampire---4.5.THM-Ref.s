%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 946 expanded)
%              Number of leaves         :   11 ( 279 expanded)
%              Depth                    :   28
%              Number of atoms          :  145 (1930 expanded)
%              Number of equality atoms :  116 (1186 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2010,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2002,f23])).

fof(f23,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2002,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f957,f1990])).

fof(f1990,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1989,f1611])).

fof(f1611,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1598,f956])).

fof(f956,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f923,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f923,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f36,f360])).

fof(f360,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f294,f22])).

fof(f22,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f294,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X3,X2)
      | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,X3)) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1598,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f1049,f1522])).

fof(f1522,plain,(
    sK3 = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f178,f1515])).

fof(f1515,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1514,f55])).

fof(f55,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f47,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f44,f24])).

fof(f44,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1514,plain,(
    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1513,f25])).

fof(f1513,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1510,f25])).

fof(f1510,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f28,f1494])).

fof(f1494,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1493,f1046])).

fof(f1046,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f367,f956])).

fof(f367,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f107,f360])).

fof(f107,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6) ),
    inference(forward_demodulation,[],[f99,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f29,f25])).

fof(f99,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f41,f28])).

fof(f1493,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1480,f1019])).

fof(f1019,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f34,f946])).

fof(f946,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f912,f24])).

fof(f912,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f359])).

fof(f359,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f294,f21])).

fof(f21,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1480,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f1040,f20])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f1040,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f34,f955])).

fof(f955,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f922,f24])).

fof(f922,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f36,f359])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f178,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f176,f86])).

fof(f86,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f75,f28])).

fof(f75,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f73,f47])).

fof(f73,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f28,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f55])).

fof(f176,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f49,f111])).

fof(f111,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f106,f28])).

fof(f106,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f41])).

fof(f49,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1) ),
    inference(forward_demodulation,[],[f46,f28])).

fof(f46,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f28,f29])).

fof(f1049,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f34,f956])).

fof(f1989,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1956,f41])).

fof(f1956,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f40,f1953])).

fof(f1953,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f1952,f47])).

fof(f1952,plain,(
    sK3 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1947,f1515])).

fof(f1947,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f28,f1920])).

fof(f1920,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f1312,f1061])).

fof(f1061,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f764,f1046])).

fof(f764,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f525,f729])).

fof(f729,plain,(
    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f499,f600])).

fof(f600,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f34,f576])).

fof(f576,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f515,f363])).

fof(f363,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f107,f359])).

fof(f515,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,sK2)) ),
    inference(forward_demodulation,[],[f504,f497])).

fof(f497,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f34,f481])).

fof(f481,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f467,f291])).

fof(f291,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f39,f21])).

fof(f467,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f396,f298])).

fof(f298,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f297,f55])).

fof(f297,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(forward_demodulation,[],[f296,f25])).

fof(f296,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f28,f291])).

fof(f396,plain,(
    ! [X30] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X30)) = k4_xboole_0(k1_xboole_0,X30) ),
    inference(superposition,[],[f34,f291])).

fof(f504,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X5)) ),
    inference(superposition,[],[f497,f28])).

fof(f499,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f497,f20])).

fof(f525,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(backward_demodulation,[],[f72,f499])).

fof(f72,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f54,f62])).

fof(f54,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f29,f53])).

fof(f53,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f52,f20])).

fof(f52,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f51,f25])).

fof(f51,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f50,f28])).

fof(f50,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f28,f40])).

fof(f1312,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f1009,f25])).

fof(f1009,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f34,f958])).

fof(f958,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f925,f24])).

fof(f925,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f36,f292])).

fof(f292,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f39,f22])).

fof(f40,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f29,f20])).

fof(f957,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f924,f24])).

fof(f924,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f36,f291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (6003)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.56  % (6007)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.57  % (6031)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.64/0.57  % (6024)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.64/0.57  % (6027)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.64/0.57  % (6012)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.64/0.58  % (6011)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.64/0.58  % (6015)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.64/0.58  % (6009)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.64/0.58  % (6006)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.64/0.59  % (6005)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.64/0.59  % (6002)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.64/0.60  % (6028)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.64/0.61  % (6019)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.64/0.61  % (6020)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.64/0.62  % (6004)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.64/0.62  % (6000)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.64/0.62  % (6010)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.64/0.63  % (6029)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.64/0.63  % (6001)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.64/0.64  % (6025)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.64  % (6022)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.64/0.64  % (6016)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.64/0.64  % (6016)Refutation not found, incomplete strategy% (6016)------------------------------
% 1.64/0.64  % (6016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.64  % (6016)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.64  
% 1.64/0.64  % (6016)Memory used [KB]: 6140
% 1.64/0.64  % (6016)Time elapsed: 0.002 s
% 1.64/0.64  % (6016)------------------------------
% 1.64/0.64  % (6016)------------------------------
% 1.64/0.64  % (6013)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.22/0.65  % (6030)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.22/0.66  % (6018)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.22/0.66  % (6021)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.22/0.66  % (6026)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.22/0.67  % (6003)Refutation found. Thanks to Tanya!
% 2.22/0.67  % SZS status Theorem for theBenchmark
% 2.22/0.67  % (6017)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.22/0.67  % (6014)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.46/0.68  % (6018)Refutation not found, incomplete strategy% (6018)------------------------------
% 2.46/0.68  % (6018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.46/0.68  % (6018)Termination reason: Refutation not found, incomplete strategy
% 2.46/0.68  
% 2.46/0.68  % (6018)Memory used [KB]: 10618
% 2.46/0.68  % (6018)Time elapsed: 0.246 s
% 2.46/0.68  % (6018)------------------------------
% 2.46/0.68  % (6018)------------------------------
% 2.46/0.68  % SZS output start Proof for theBenchmark
% 2.46/0.68  fof(f2010,plain,(
% 2.46/0.68    $false),
% 2.46/0.68    inference(subsumption_resolution,[],[f2002,f23])).
% 2.46/0.68  fof(f23,plain,(
% 2.46/0.68    sK1 != sK2),
% 2.46/0.68    inference(cnf_transformation,[],[f18])).
% 2.46/0.68  fof(f18,plain,(
% 2.46/0.68    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.46/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).
% 2.46/0.68  fof(f17,plain,(
% 2.46/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.46/0.68    introduced(choice_axiom,[])).
% 2.46/0.68  fof(f15,plain,(
% 2.46/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.46/0.68    inference(flattening,[],[f14])).
% 2.46/0.68  fof(f14,plain,(
% 2.46/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.46/0.68    inference(ennf_transformation,[],[f13])).
% 2.46/0.68  fof(f13,negated_conjecture,(
% 2.46/0.68    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.46/0.68    inference(negated_conjecture,[],[f12])).
% 2.46/0.68  fof(f12,conjecture,(
% 2.46/0.68    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.46/0.68  fof(f2002,plain,(
% 2.46/0.68    sK1 = sK2),
% 2.46/0.68    inference(backward_demodulation,[],[f957,f1990])).
% 2.46/0.68  fof(f1990,plain,(
% 2.46/0.68    sK1 = k4_xboole_0(sK2,sK0)),
% 2.46/0.68    inference(forward_demodulation,[],[f1989,f1611])).
% 2.46/0.68  fof(f1611,plain,(
% 2.46/0.68    sK1 = k4_xboole_0(sK1,sK0)),
% 2.46/0.68    inference(forward_demodulation,[],[f1598,f956])).
% 2.46/0.68  fof(f956,plain,(
% 2.46/0.68    sK1 = k4_xboole_0(sK1,sK3)),
% 2.46/0.68    inference(forward_demodulation,[],[f923,f24])).
% 2.46/0.68  fof(f24,plain,(
% 2.46/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.46/0.68    inference(cnf_transformation,[],[f5])).
% 2.46/0.68  fof(f5,axiom,(
% 2.46/0.68    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.46/0.68  fof(f923,plain,(
% 2.46/0.68    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.46/0.68    inference(superposition,[],[f36,f360])).
% 2.46/0.68  fof(f360,plain,(
% 2.46/0.68    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.46/0.68    inference(resolution,[],[f294,f22])).
% 2.46/0.68  fof(f22,plain,(
% 2.46/0.68    r1_xboole_0(sK3,sK1)),
% 2.46/0.68    inference(cnf_transformation,[],[f18])).
% 2.46/0.68  fof(f294,plain,(
% 2.46/0.68    ( ! [X2,X3] : (~r1_xboole_0(X3,X2) | k1_xboole_0 = k4_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.46/0.68    inference(resolution,[],[f39,f31])).
% 2.46/0.68  fof(f31,plain,(
% 2.46/0.68    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f16])).
% 2.46/0.68  fof(f16,plain,(
% 2.46/0.68    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.46/0.68    inference(ennf_transformation,[],[f3])).
% 2.46/0.68  fof(f3,axiom,(
% 2.46/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.46/0.68  fof(f39,plain,(
% 2.46/0.68    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.46/0.68    inference(definition_unfolding,[],[f32,f26])).
% 2.46/0.68  fof(f26,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.46/0.68    inference(cnf_transformation,[],[f9])).
% 2.46/0.68  fof(f9,axiom,(
% 2.46/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.46/0.68  fof(f32,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f19])).
% 2.46/0.68  fof(f19,plain,(
% 2.46/0.68    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.46/0.68    inference(nnf_transformation,[],[f2])).
% 2.46/0.68  fof(f2,axiom,(
% 2.46/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.46/0.68  fof(f36,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.46/0.68    inference(definition_unfolding,[],[f27,f26])).
% 2.46/0.68  fof(f27,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.46/0.68    inference(cnf_transformation,[],[f8])).
% 2.46/0.68  fof(f8,axiom,(
% 2.46/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.46/0.68  fof(f1598,plain,(
% 2.46/0.68    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK0)),
% 2.46/0.68    inference(superposition,[],[f1049,f1522])).
% 2.46/0.68  fof(f1522,plain,(
% 2.46/0.68    sK3 = k2_xboole_0(sK3,sK0)),
% 2.46/0.68    inference(superposition,[],[f178,f1515])).
% 2.46/0.68  fof(f1515,plain,(
% 2.46/0.68    sK3 = k2_xboole_0(sK0,sK3)),
% 2.46/0.68    inference(forward_demodulation,[],[f1514,f55])).
% 2.46/0.68  fof(f55,plain,(
% 2.46/0.68    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.46/0.68    inference(superposition,[],[f47,f25])).
% 2.46/0.68  fof(f25,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f1])).
% 2.46/0.68  fof(f1,axiom,(
% 2.46/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.46/0.68  fof(f47,plain,(
% 2.46/0.68    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.46/0.68    inference(forward_demodulation,[],[f44,f24])).
% 2.46/0.68  fof(f44,plain,(
% 2.46/0.68    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.46/0.68    inference(superposition,[],[f29,f24])).
% 2.46/0.68  fof(f29,plain,(
% 2.46/0.68    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.46/0.68    inference(cnf_transformation,[],[f6])).
% 2.46/0.68  fof(f6,axiom,(
% 2.46/0.68    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.46/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.46/0.68  fof(f1514,plain,(
% 2.46/0.68    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3)),
% 2.46/0.68    inference(forward_demodulation,[],[f1513,f25])).
% 2.46/0.68  fof(f1513,plain,(
% 2.46/0.68    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.46/0.68    inference(forward_demodulation,[],[f1510,f25])).
% 2.46/0.68  fof(f1510,plain,(
% 2.46/0.68    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0)),
% 2.46/0.68    inference(superposition,[],[f28,f1494])).
% 2.46/0.68  fof(f1494,plain,(
% 2.46/0.68    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.46/0.68    inference(forward_demodulation,[],[f1493,f1046])).
% 2.46/0.68  fof(f1046,plain,(
% 2.46/0.68    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 2.46/0.68    inference(backward_demodulation,[],[f367,f956])).
% 2.46/0.69  fof(f367,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 2.46/0.69    inference(superposition,[],[f107,f360])).
% 2.46/0.69  fof(f107,plain,(
% 2.46/0.69    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k4_xboole_0(X7,X6),X6)) )),
% 2.46/0.69    inference(forward_demodulation,[],[f99,f41])).
% 2.46/0.69  fof(f41,plain,(
% 2.46/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 2.46/0.69    inference(superposition,[],[f29,f25])).
% 2.46/0.69  fof(f99,plain,(
% 2.46/0.69    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,X6),X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 2.46/0.69    inference(superposition,[],[f41,f28])).
% 2.46/0.69  fof(f1493,plain,(
% 2.46/0.69    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(sK0,sK3)),
% 2.46/0.69    inference(forward_demodulation,[],[f1480,f1019])).
% 2.46/0.69  fof(f1019,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 2.46/0.69    inference(superposition,[],[f34,f946])).
% 2.46/0.69  fof(f946,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 2.46/0.69    inference(forward_demodulation,[],[f912,f24])).
% 2.46/0.69  fof(f912,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))),
% 2.46/0.69    inference(superposition,[],[f36,f359])).
% 2.46/0.69  fof(f359,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.46/0.69    inference(resolution,[],[f294,f21])).
% 2.46/0.69  fof(f21,plain,(
% 2.46/0.69    r1_xboole_0(sK2,sK0)),
% 2.46/0.69    inference(cnf_transformation,[],[f18])).
% 2.46/0.69  fof(f34,plain,(
% 2.46/0.69    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.46/0.69    inference(cnf_transformation,[],[f7])).
% 2.46/0.69  fof(f7,axiom,(
% 2.46/0.69    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.46/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.46/0.69  fof(f1480,plain,(
% 2.46/0.69    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)),
% 2.46/0.69    inference(superposition,[],[f1040,f20])).
% 2.46/0.69  fof(f20,plain,(
% 2.46/0.69    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.46/0.69    inference(cnf_transformation,[],[f18])).
% 2.46/0.69  fof(f1040,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 2.46/0.69    inference(superposition,[],[f34,f955])).
% 2.46/0.69  fof(f955,plain,(
% 2.46/0.69    sK0 = k4_xboole_0(sK0,sK2)),
% 2.46/0.69    inference(forward_demodulation,[],[f922,f24])).
% 2.46/0.69  fof(f922,plain,(
% 2.46/0.69    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.46/0.69    inference(superposition,[],[f36,f359])).
% 2.46/0.69  fof(f28,plain,(
% 2.46/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.46/0.69    inference(cnf_transformation,[],[f4])).
% 2.46/0.69  fof(f4,axiom,(
% 2.46/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.46/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.46/0.69  fof(f178,plain,(
% 2.46/0.69    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 2.46/0.69    inference(forward_demodulation,[],[f176,f86])).
% 2.46/0.69  fof(f86,plain,(
% 2.46/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.46/0.69    inference(superposition,[],[f75,f28])).
% 2.46/0.69  fof(f75,plain,(
% 2.46/0.69    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.46/0.69    inference(forward_demodulation,[],[f73,f47])).
% 2.46/0.69  fof(f73,plain,(
% 2.46/0.69    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 2.46/0.69    inference(superposition,[],[f28,f62])).
% 2.46/0.69  fof(f62,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 2.46/0.69    inference(superposition,[],[f29,f55])).
% 2.46/0.69  fof(f176,plain,(
% 2.46/0.69    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k2_xboole_0(X1,X2))) )),
% 2.46/0.69    inference(superposition,[],[f49,f111])).
% 2.46/0.69  fof(f111,plain,(
% 2.46/0.69    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.46/0.69    inference(forward_demodulation,[],[f106,f28])).
% 2.46/0.69  fof(f106,plain,(
% 2.46/0.69    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.46/0.69    inference(superposition,[],[f28,f41])).
% 2.46/0.69  fof(f49,plain,(
% 2.46/0.69    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,X1)) )),
% 2.46/0.69    inference(forward_demodulation,[],[f46,f28])).
% 2.46/0.69  fof(f46,plain,(
% 2.46/0.69    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 2.46/0.69    inference(superposition,[],[f28,f29])).
% 2.46/0.69  fof(f1049,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 2.46/0.69    inference(superposition,[],[f34,f956])).
% 2.46/0.69  fof(f1989,plain,(
% 2.46/0.69    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 2.46/0.69    inference(forward_demodulation,[],[f1956,f41])).
% 2.46/0.69  fof(f1956,plain,(
% 2.46/0.69    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 2.46/0.69    inference(backward_demodulation,[],[f40,f1953])).
% 2.46/0.69  fof(f1953,plain,(
% 2.46/0.69    sK0 = sK3),
% 2.46/0.69    inference(forward_demodulation,[],[f1952,f47])).
% 2.46/0.69  fof(f1952,plain,(
% 2.46/0.69    sK3 = k2_xboole_0(sK0,k1_xboole_0)),
% 2.46/0.69    inference(forward_demodulation,[],[f1947,f1515])).
% 2.46/0.69  fof(f1947,plain,(
% 2.46/0.69    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.46/0.69    inference(superposition,[],[f28,f1920])).
% 2.46/0.69  fof(f1920,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 2.46/0.69    inference(superposition,[],[f1312,f1061])).
% 2.46/0.69  fof(f1061,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(backward_demodulation,[],[f764,f1046])).
% 2.46/0.69  fof(f764,plain,(
% 2.46/0.69    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK1)),
% 2.46/0.69    inference(backward_demodulation,[],[f525,f729])).
% 2.46/0.69  fof(f729,plain,(
% 2.46/0.69    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(k1_xboole_0,sK1)),
% 2.46/0.69    inference(backward_demodulation,[],[f499,f600])).
% 2.46/0.69  fof(f600,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,X0))) )),
% 2.46/0.69    inference(superposition,[],[f34,f576])).
% 2.46/0.69  fof(f576,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 2.46/0.69    inference(superposition,[],[f515,f363])).
% 2.46/0.69  fof(f363,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 2.46/0.69    inference(superposition,[],[f107,f359])).
% 2.46/0.69  fof(f515,plain,(
% 2.46/0.69    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,sK2))) )),
% 2.46/0.69    inference(forward_demodulation,[],[f504,f497])).
% 2.46/0.69  fof(f497,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X0))) )),
% 2.46/0.69    inference(superposition,[],[f34,f481])).
% 2.46/0.69  fof(f481,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 2.46/0.69    inference(forward_demodulation,[],[f467,f291])).
% 2.46/0.69  fof(f291,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.46/0.69    inference(resolution,[],[f39,f21])).
% 2.46/0.69  fof(f467,plain,(
% 2.46/0.69    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2)),
% 2.46/0.69    inference(superposition,[],[f396,f298])).
% 2.46/0.69  fof(f298,plain,(
% 2.46/0.69    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.46/0.69    inference(forward_demodulation,[],[f297,f55])).
% 2.46/0.69  fof(f297,plain,(
% 2.46/0.69    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 2.46/0.69    inference(forward_demodulation,[],[f296,f25])).
% 2.46/0.69  fof(f296,plain,(
% 2.46/0.69    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 2.46/0.69    inference(superposition,[],[f28,f291])).
% 2.46/0.69  fof(f396,plain,(
% 2.46/0.69    ( ! [X30] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X30)) = k4_xboole_0(k1_xboole_0,X30)) )),
% 2.46/0.69    inference(superposition,[],[f34,f291])).
% 2.46/0.69  fof(f504,plain,(
% 2.46/0.69    ( ! [X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,sK2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK2,X5))) )),
% 2.46/0.69    inference(superposition,[],[f497,f28])).
% 2.46/0.69  fof(f499,plain,(
% 2.46/0.69    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 2.46/0.69    inference(superposition,[],[f497,f20])).
% 2.46/0.69  fof(f525,plain,(
% 2.46/0.69    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK3)),
% 2.46/0.69    inference(backward_demodulation,[],[f72,f499])).
% 2.46/0.69  fof(f72,plain,(
% 2.46/0.69    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(backward_demodulation,[],[f54,f62])).
% 2.46/0.69  fof(f54,plain,(
% 2.46/0.69    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(superposition,[],[f29,f53])).
% 2.46/0.69  fof(f53,plain,(
% 2.46/0.69    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(forward_demodulation,[],[f52,f20])).
% 2.46/0.69  fof(f52,plain,(
% 2.46/0.69    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(forward_demodulation,[],[f51,f25])).
% 2.46/0.69  fof(f51,plain,(
% 2.46/0.69    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.46/0.69    inference(forward_demodulation,[],[f50,f28])).
% 2.46/0.69  fof(f50,plain,(
% 2.46/0.69    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 2.46/0.69    inference(superposition,[],[f28,f40])).
% 2.46/0.69  fof(f1312,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 2.46/0.69    inference(superposition,[],[f1009,f25])).
% 2.46/0.69  fof(f1009,plain,(
% 2.46/0.69    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 2.46/0.69    inference(superposition,[],[f34,f958])).
% 2.46/0.69  fof(f958,plain,(
% 2.46/0.69    sK3 = k4_xboole_0(sK3,sK1)),
% 2.46/0.69    inference(forward_demodulation,[],[f925,f24])).
% 2.46/0.69  fof(f925,plain,(
% 2.46/0.69    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.46/0.69    inference(superposition,[],[f36,f292])).
% 2.46/0.69  fof(f292,plain,(
% 2.46/0.69    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.46/0.69    inference(resolution,[],[f39,f22])).
% 2.46/0.69  fof(f40,plain,(
% 2.46/0.69    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.46/0.69    inference(superposition,[],[f29,f20])).
% 2.46/0.69  fof(f957,plain,(
% 2.46/0.69    sK2 = k4_xboole_0(sK2,sK0)),
% 2.46/0.69    inference(forward_demodulation,[],[f924,f24])).
% 2.46/0.69  fof(f924,plain,(
% 2.46/0.69    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.46/0.69    inference(superposition,[],[f36,f291])).
% 2.46/0.69  % SZS output end Proof for theBenchmark
% 2.46/0.69  % (6003)------------------------------
% 2.46/0.69  % (6003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.46/0.69  % (6003)Termination reason: Refutation
% 2.46/0.69  
% 2.46/0.69  % (6003)Memory used [KB]: 11897
% 2.46/0.69  % (6003)Time elapsed: 0.242 s
% 2.46/0.69  % (6003)------------------------------
% 2.46/0.69  % (6003)------------------------------
% 2.46/0.70  % (5994)Success in time 0.331 s
%------------------------------------------------------------------------------
