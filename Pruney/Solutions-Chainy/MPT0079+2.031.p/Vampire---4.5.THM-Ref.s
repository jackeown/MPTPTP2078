%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 660 expanded)
%              Number of leaves         :   17 ( 186 expanded)
%              Depth                    :   32
%              Number of atoms          :  131 (1035 expanded)
%              Number of equality atoms :  102 ( 743 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3560,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3559,f28])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f3559,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f2632,f3513])).

fof(f3513,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f2981,f2565])).

fof(f2565,plain,(
    sK3 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2564,f2016])).

fof(f2016,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f1952,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1952,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f46,f511])).

fof(f511,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2564,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2528,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2528,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f75,f2481])).

fof(f2481,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2480,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2480,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f2479,f111])).

fof(f111,plain,(
    ! [X6,X7] : k2_xboole_0(X7,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,X6) ),
    inference(forward_demodulation,[],[f97,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,(
    ! [X6,X7] : k2_xboole_0(X7,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f37,f36])).

fof(f2479,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2478,f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2478,plain,(
    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2477,f326])).

fof(f326,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f306,f114])).

fof(f114,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f113,f25])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f113,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f112,f33])).

fof(f112,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f98,f37])).

fof(f98,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f37,f77])).

fof(f77,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f36,f25])).

fof(f306,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f111,f25])).

fof(f2477,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2)) ),
    inference(forward_demodulation,[],[f2466,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2466,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK2) ),
    inference(superposition,[],[f37,f2177])).

fof(f2177,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2150,f73])).

fof(f73,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f32,f25])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2150,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f2050,f1547])).

fof(f1547,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f43,f328])).

fof(f328,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f308,f108])).

fof(f108,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f94,f31])).

fof(f94,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1) ),
    inference(superposition,[],[f37,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f45,f30])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f308,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f111,f114])).

fof(f2050,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f42,f1998])).

fof(f1998,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f1951,f30])).

fof(f1951,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f46,f510])).

fof(f510,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f75,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f36,f33])).

fof(f2981,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f2980,f2360])).

fof(f2360,plain,(
    ! [X37,X38] : k2_xboole_0(k4_xboole_0(X37,X38),X37) = X37 ),
    inference(superposition,[],[f214,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f214,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f2980,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f2863,f30])).

fof(f2863,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f44,f34])).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f2632,plain,(
    sK2 = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f2543,f2631])).

fof(f2631,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f2610,f1998])).

fof(f2610,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f2050,f2605])).

fof(f2605,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f2594,f31])).

fof(f2594,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f37,f2593])).

fof(f2593,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(resolution,[],[f2588,f41])).

fof(f2588,plain,(
    r1_tarski(sK3,sK0) ),
    inference(superposition,[],[f2040,f2565])).

fof(f2040,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f2039,f2037])).

fof(f2037,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f2036,f47])).

fof(f2036,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f1955,f33])).

fof(f1955,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f37,f46])).

fof(f2039,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f1957,f33])).

fof(f1957,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5)) ),
    inference(superposition,[],[f104,f46])).

fof(f104,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(X9,X8),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f56,f37])).

fof(f56,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f32,f33])).

fof(f2543,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f77,f2522])).

fof(f2522,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f36,f2481])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:23:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (8085)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (8068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8076)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (8093)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (8067)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (8064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (8077)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8091)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (8090)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (8065)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8074)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (8066)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8082)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (8089)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (8082)Refutation not found, incomplete strategy% (8082)------------------------------
% 0.21/0.53  % (8082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8082)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (8082)Memory used [KB]: 10618
% 0.21/0.53  % (8082)Time elapsed: 0.119 s
% 0.21/0.53  % (8082)------------------------------
% 0.21/0.53  % (8082)------------------------------
% 0.21/0.54  % (8094)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8071)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (8092)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8072)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8088)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (8083)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (8081)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (8086)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (8084)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8075)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (8078)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (8073)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (8080)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (8080)Refutation not found, incomplete strategy% (8080)------------------------------
% 0.21/0.56  % (8080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8080)Memory used [KB]: 6140
% 0.21/0.56  % (8080)Time elapsed: 0.002 s
% 0.21/0.56  % (8080)------------------------------
% 0.21/0.56  % (8080)------------------------------
% 0.21/0.58  % (8087)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.58  % (8079)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.59  % (8070)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 2.19/0.68  % (8096)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.19/0.68  % (8097)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.70  % (8071)Refutation found. Thanks to Tanya!
% 2.19/0.70  % SZS status Theorem for theBenchmark
% 2.19/0.70  % SZS output start Proof for theBenchmark
% 2.19/0.70  fof(f3560,plain,(
% 2.19/0.70    $false),
% 2.19/0.70    inference(subsumption_resolution,[],[f3559,f28])).
% 2.19/0.70  fof(f28,plain,(
% 2.19/0.70    sK1 != sK2),
% 2.19/0.70    inference(cnf_transformation,[],[f22])).
% 2.19/0.70  fof(f22,plain,(
% 2.19/0.70    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.19/0.70    inference(flattening,[],[f21])).
% 2.19/0.70  fof(f21,plain,(
% 2.19/0.70    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.19/0.70    inference(ennf_transformation,[],[f18])).
% 2.19/0.70  fof(f18,negated_conjecture,(
% 2.19/0.70    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.19/0.70    inference(negated_conjecture,[],[f17])).
% 2.19/0.70  fof(f17,conjecture,(
% 2.19/0.70    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.19/0.70  fof(f3559,plain,(
% 2.19/0.70    sK1 = sK2),
% 2.19/0.70    inference(backward_demodulation,[],[f2632,f3513])).
% 2.19/0.70  fof(f3513,plain,(
% 2.19/0.70    sK1 = k4_xboole_0(sK1,sK3)),
% 2.19/0.70    inference(superposition,[],[f2981,f2565])).
% 2.19/0.70  fof(f2565,plain,(
% 2.19/0.70    sK3 = k4_xboole_0(sK0,sK1)),
% 2.19/0.70    inference(forward_demodulation,[],[f2564,f2016])).
% 2.19/0.70  fof(f2016,plain,(
% 2.19/0.70    sK3 = k4_xboole_0(sK3,sK1)),
% 2.19/0.70    inference(forward_demodulation,[],[f1952,f30])).
% 2.19/0.70  fof(f30,plain,(
% 2.19/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.70    inference(cnf_transformation,[],[f7])).
% 2.19/0.70  fof(f7,axiom,(
% 2.19/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.19/0.70  fof(f1952,plain,(
% 2.19/0.70    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.19/0.70    inference(superposition,[],[f46,f511])).
% 2.19/0.70  fof(f511,plain,(
% 2.19/0.70    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.19/0.70    inference(resolution,[],[f48,f27])).
% 2.19/0.70  fof(f27,plain,(
% 2.19/0.70    r1_xboole_0(sK3,sK1)),
% 2.19/0.70    inference(cnf_transformation,[],[f22])).
% 2.19/0.70  fof(f48,plain,(
% 2.19/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.70    inference(definition_unfolding,[],[f40,f34])).
% 2.19/0.70  fof(f34,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/0.70    inference(cnf_transformation,[],[f11])).
% 2.19/0.70  fof(f11,axiom,(
% 2.19/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.19/0.70  fof(f40,plain,(
% 2.19/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.19/0.70    inference(cnf_transformation,[],[f23])).
% 2.19/0.70  fof(f23,plain,(
% 2.19/0.70    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.19/0.70    inference(ennf_transformation,[],[f20])).
% 2.19/0.70  fof(f20,plain,(
% 2.19/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.19/0.70    inference(unused_predicate_definition_removal,[],[f2])).
% 2.19/0.70  fof(f2,axiom,(
% 2.19/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.19/0.70  fof(f46,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.19/0.70    inference(definition_unfolding,[],[f35,f34])).
% 2.19/0.70  fof(f35,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/0.70    inference(cnf_transformation,[],[f10])).
% 2.19/0.70  fof(f10,axiom,(
% 2.19/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.19/0.70  fof(f2564,plain,(
% 2.19/0.70    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK0,sK1)),
% 2.19/0.70    inference(forward_demodulation,[],[f2528,f36])).
% 2.19/0.70  fof(f36,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.19/0.70    inference(cnf_transformation,[],[f8])).
% 2.19/0.70  fof(f8,axiom,(
% 2.19/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.19/0.70  fof(f2528,plain,(
% 2.19/0.70    k4_xboole_0(sK3,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 2.19/0.70    inference(superposition,[],[f75,f2481])).
% 2.19/0.70  fof(f2481,plain,(
% 2.19/0.70    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 2.19/0.70    inference(forward_demodulation,[],[f2480,f33])).
% 2.19/0.70  fof(f33,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.19/0.70    inference(cnf_transformation,[],[f1])).
% 2.19/0.70  fof(f1,axiom,(
% 2.19/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.19/0.70  fof(f2480,plain,(
% 2.19/0.70    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3)),
% 2.19/0.70    inference(forward_demodulation,[],[f2479,f111])).
% 2.19/0.70  fof(f111,plain,(
% 2.19/0.70    ( ! [X6,X7] : (k2_xboole_0(X7,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,X6)) )),
% 2.19/0.70    inference(forward_demodulation,[],[f97,f37])).
% 2.19/0.70  fof(f37,plain,(
% 2.19/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/0.70    inference(cnf_transformation,[],[f6])).
% 2.19/0.70  fof(f6,axiom,(
% 2.19/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.19/0.70  fof(f97,plain,(
% 2.19/0.70    ( ! [X6,X7] : (k2_xboole_0(X7,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 2.19/0.70    inference(superposition,[],[f37,f36])).
% 2.19/0.70  fof(f2479,plain,(
% 2.19/0.70    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 2.19/0.70    inference(forward_demodulation,[],[f2478,f31])).
% 2.19/0.70  fof(f31,plain,(
% 2.19/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/0.70    inference(cnf_transformation,[],[f4])).
% 2.19/0.70  fof(f4,axiom,(
% 2.19/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.19/0.70  fof(f2478,plain,(
% 2.19/0.70    k2_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0)),
% 2.19/0.70    inference(forward_demodulation,[],[f2477,f326])).
% 2.19/0.70  fof(f326,plain,(
% 2.19/0.70    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 2.19/0.70    inference(forward_demodulation,[],[f306,f114])).
% 2.19/0.70  fof(f114,plain,(
% 2.19/0.70    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.19/0.70    inference(forward_demodulation,[],[f113,f25])).
% 2.19/0.70  fof(f25,plain,(
% 2.19/0.70    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.19/0.70    inference(cnf_transformation,[],[f22])).
% 2.19/0.70  fof(f113,plain,(
% 2.19/0.70    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.19/0.70    inference(forward_demodulation,[],[f112,f33])).
% 2.19/0.70  fof(f112,plain,(
% 2.19/0.70    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.19/0.70    inference(forward_demodulation,[],[f98,f37])).
% 2.19/0.70  fof(f98,plain,(
% 2.19/0.70    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 2.19/0.70    inference(superposition,[],[f37,f77])).
% 2.19/0.70  fof(f77,plain,(
% 2.19/0.70    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.19/0.70    inference(superposition,[],[f36,f25])).
% 2.19/0.70  fof(f306,plain,(
% 2.19/0.70    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.19/0.70    inference(superposition,[],[f111,f25])).
% 2.19/0.70  fof(f2477,plain,(
% 2.19/0.70    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK2))),
% 2.19/0.70    inference(forward_demodulation,[],[f2466,f43])).
% 2.19/0.70  fof(f43,plain,(
% 2.19/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.19/0.70    inference(cnf_transformation,[],[f12])).
% 2.19/0.70  fof(f12,axiom,(
% 2.19/0.70    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.19/0.70  fof(f2466,plain,(
% 2.19/0.70    k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK2)),
% 2.19/0.70    inference(superposition,[],[f37,f2177])).
% 2.19/0.70  fof(f2177,plain,(
% 2.19/0.70    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 2.19/0.70    inference(forward_demodulation,[],[f2150,f73])).
% 2.19/0.71  fof(f73,plain,(
% 2.19/0.71    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.19/0.71    inference(resolution,[],[f41,f52])).
% 2.19/0.71  fof(f52,plain,(
% 2.19/0.71    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 2.19/0.71    inference(superposition,[],[f32,f25])).
% 2.19/0.71  fof(f32,plain,(
% 2.19/0.71    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f16])).
% 2.19/0.71  fof(f16,axiom,(
% 2.19/0.71    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.19/0.71  fof(f41,plain,(
% 2.19/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f24])).
% 2.19/0.71  fof(f24,plain,(
% 2.19/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 2.19/0.71    inference(ennf_transformation,[],[f19])).
% 2.19/0.71  fof(f19,plain,(
% 2.19/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 2.19/0.71    inference(unused_predicate_definition_removal,[],[f3])).
% 2.19/0.71  fof(f3,axiom,(
% 2.19/0.71    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.19/0.71  fof(f2150,plain,(
% 2.19/0.71    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK3))),
% 2.19/0.71    inference(superposition,[],[f2050,f1547])).
% 2.19/0.71  fof(f1547,plain,(
% 2.19/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 2.19/0.71    inference(superposition,[],[f43,f328])).
% 2.19/0.71  fof(f328,plain,(
% 2.19/0.71    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.19/0.71    inference(forward_demodulation,[],[f308,f108])).
% 2.19/0.71  fof(f108,plain,(
% 2.19/0.71    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 2.19/0.71    inference(forward_demodulation,[],[f94,f31])).
% 2.19/0.71  fof(f94,plain,(
% 2.19/0.71    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,X1)) )),
% 2.19/0.71    inference(superposition,[],[f37,f50])).
% 2.19/0.71  fof(f50,plain,(
% 2.19/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.19/0.71    inference(backward_demodulation,[],[f45,f30])).
% 2.19/0.71  fof(f45,plain,(
% 2.19/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.19/0.71    inference(definition_unfolding,[],[f29,f34])).
% 2.19/0.71  fof(f29,plain,(
% 2.19/0.71    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.19/0.71    inference(cnf_transformation,[],[f5])).
% 2.19/0.71  fof(f5,axiom,(
% 2.19/0.71    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.19/0.71  fof(f308,plain,(
% 2.19/0.71    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.19/0.71    inference(superposition,[],[f111,f114])).
% 2.19/0.71  fof(f2050,plain,(
% 2.19/0.71    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 2.19/0.71    inference(superposition,[],[f42,f1998])).
% 2.19/0.71  fof(f1998,plain,(
% 2.19/0.71    sK2 = k4_xboole_0(sK2,sK0)),
% 2.19/0.71    inference(forward_demodulation,[],[f1951,f30])).
% 2.19/0.71  fof(f1951,plain,(
% 2.19/0.71    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.19/0.71    inference(superposition,[],[f46,f510])).
% 2.19/0.71  fof(f510,plain,(
% 2.19/0.71    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.19/0.71    inference(resolution,[],[f48,f26])).
% 2.19/0.71  fof(f26,plain,(
% 2.19/0.71    r1_xboole_0(sK2,sK0)),
% 2.19/0.71    inference(cnf_transformation,[],[f22])).
% 2.19/0.71  fof(f42,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f9])).
% 2.19/0.71  fof(f9,axiom,(
% 2.19/0.71    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.19/0.71  fof(f75,plain,(
% 2.19/0.71    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 2.19/0.71    inference(superposition,[],[f36,f33])).
% 2.19/0.71  fof(f2981,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.19/0.71    inference(forward_demodulation,[],[f2980,f2360])).
% 2.19/0.71  fof(f2360,plain,(
% 2.19/0.71    ( ! [X37,X38] : (k2_xboole_0(k4_xboole_0(X37,X38),X37) = X37) )),
% 2.19/0.71    inference(superposition,[],[f214,f47])).
% 2.19/0.71  fof(f47,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.19/0.71    inference(definition_unfolding,[],[f39,f34])).
% 2.19/0.71  fof(f39,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.19/0.71    inference(cnf_transformation,[],[f13])).
% 2.19/0.71  fof(f13,axiom,(
% 2.19/0.71    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.19/0.71  fof(f214,plain,(
% 2.19/0.71    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.19/0.71    inference(superposition,[],[f38,f33])).
% 2.19/0.71  fof(f38,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f15])).
% 2.19/0.71  fof(f15,axiom,(
% 2.19/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.19/0.71  fof(f2980,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 2.19/0.71    inference(forward_demodulation,[],[f2863,f30])).
% 2.19/0.71  fof(f2863,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 2.19/0.71    inference(superposition,[],[f49,f50])).
% 2.19/0.71  fof(f49,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.19/0.71    inference(definition_unfolding,[],[f44,f34])).
% 2.19/0.71  fof(f44,plain,(
% 2.19/0.71    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.19/0.71    inference(cnf_transformation,[],[f14])).
% 2.19/0.71  fof(f14,axiom,(
% 2.19/0.71    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.19/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.19/0.71  fof(f2632,plain,(
% 2.19/0.71    sK2 = k4_xboole_0(sK1,sK3)),
% 2.19/0.71    inference(backward_demodulation,[],[f2543,f2631])).
% 2.19/0.71  fof(f2631,plain,(
% 2.19/0.71    sK2 = k4_xboole_0(sK2,sK3)),
% 2.19/0.71    inference(forward_demodulation,[],[f2610,f1998])).
% 2.19/0.71  fof(f2610,plain,(
% 2.19/0.71    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK0)),
% 2.19/0.71    inference(superposition,[],[f2050,f2605])).
% 2.19/0.71  fof(f2605,plain,(
% 2.19/0.71    sK0 = k2_xboole_0(sK0,sK3)),
% 2.19/0.71    inference(forward_demodulation,[],[f2594,f31])).
% 2.19/0.71  fof(f2594,plain,(
% 2.19/0.71    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.19/0.71    inference(superposition,[],[f37,f2593])).
% 2.19/0.71  fof(f2593,plain,(
% 2.19/0.71    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 2.19/0.71    inference(resolution,[],[f2588,f41])).
% 2.19/0.71  fof(f2588,plain,(
% 2.19/0.71    r1_tarski(sK3,sK0)),
% 2.19/0.71    inference(superposition,[],[f2040,f2565])).
% 2.19/0.71  fof(f2040,plain,(
% 2.19/0.71    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X5,X6),X5)) )),
% 2.19/0.71    inference(forward_demodulation,[],[f2039,f2037])).
% 2.19/0.71  fof(f2037,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.19/0.71    inference(forward_demodulation,[],[f2036,f47])).
% 2.19/0.71  fof(f2036,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.19/0.71    inference(forward_demodulation,[],[f1955,f33])).
% 2.19/0.71  fof(f1955,plain,(
% 2.19/0.71    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.19/0.71    inference(superposition,[],[f37,f46])).
% 2.19/0.71  fof(f2039,plain,(
% 2.19/0.71    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X6))))) )),
% 2.19/0.71    inference(forward_demodulation,[],[f1957,f33])).
% 2.19/0.71  fof(f1957,plain,(
% 2.19/0.71    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X5,X6),k2_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),X5))) )),
% 2.19/0.71    inference(superposition,[],[f104,f46])).
% 2.19/0.71  fof(f104,plain,(
% 2.19/0.71    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(X9,X8),k2_xboole_0(X8,X9))) )),
% 2.19/0.71    inference(superposition,[],[f56,f37])).
% 2.19/0.71  fof(f56,plain,(
% 2.19/0.71    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 2.19/0.71    inference(superposition,[],[f32,f33])).
% 2.19/0.71  fof(f2543,plain,(
% 2.19/0.71    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK1,sK3)),
% 2.19/0.71    inference(backward_demodulation,[],[f77,f2522])).
% 2.19/0.71  fof(f2522,plain,(
% 2.19/0.71    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 2.19/0.71    inference(superposition,[],[f36,f2481])).
% 2.19/0.71  % SZS output end Proof for theBenchmark
% 2.19/0.71  % (8071)------------------------------
% 2.19/0.71  % (8071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.71  % (8071)Termination reason: Refutation
% 2.19/0.71  
% 2.19/0.71  % (8071)Memory used [KB]: 8059
% 2.19/0.71  % (8071)Time elapsed: 0.274 s
% 2.19/0.71  % (8071)------------------------------
% 2.19/0.71  % (8071)------------------------------
% 2.19/0.71  % (8062)Success in time 0.347 s
%------------------------------------------------------------------------------
