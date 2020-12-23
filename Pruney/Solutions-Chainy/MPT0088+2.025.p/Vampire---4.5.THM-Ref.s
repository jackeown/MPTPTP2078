%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 5.32s
% Output     : Refutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 508 expanded)
%              Number of leaves         :    9 ( 174 expanded)
%              Depth                    :   22
%              Number of atoms          :   94 ( 600 expanded)
%              Number of equality atoms :   53 ( 447 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10802,plain,(
    $false ),
    inference(resolution,[],[f10801,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f10801,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f10783,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f10783,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f10419,f3751])).

fof(f3751,plain,(
    ! [X57] : k4_xboole_0(sK0,X57) = k4_xboole_0(k4_xboole_0(sK0,X57),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f147,f3645])).

fof(f3645,plain,(
    ! [X9] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X9)) ),
    inference(forward_demodulation,[],[f3556,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3556,plain,(
    ! [X9] : k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X9)) ),
    inference(superposition,[],[f28,f213])).

fof(f213,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) ),
    inference(forward_demodulation,[],[f212,f102])).

fof(f102,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f88,f19])).

fof(f88,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f28,f49])).

fof(f49,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f212,plain,(
    ! [X12] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k1_xboole_0,X12) ),
    inference(forward_demodulation,[],[f179,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f46,f19])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f30,f32])).

fof(f179,plain,(
    ! [X12] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X12) ),
    inference(superposition,[],[f31,f157])).

fof(f157,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f147,f104])).

fof(f104,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f89,f19])).

fof(f89,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f28,f53])).

fof(f53,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f21,f21])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f147,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f135,f19])).

fof(f135,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f28,f48])).

fof(f48,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f23,f20])).

fof(f10419,plain,(
    ! [X17,X15,X16] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k4_xboole_0(X17,X15)),X17) ),
    inference(superposition,[],[f10311,f147])).

fof(f10311,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),X3) ),
    inference(forward_demodulation,[],[f10310,f19])).

fof(f10310,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),k4_xboole_0(X3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f10228,f54])).

fof(f10228,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),k4_xboole_0(X3,k4_xboole_0(X2,X2))) ),
    inference(superposition,[],[f2673,f197])).

fof(f197,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24)))) = X24 ),
    inference(superposition,[],[f147,f31])).

fof(f2673,plain,(
    ! [X45,X46,X44] : r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X45,X46)),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X45,X46)))))) ),
    inference(backward_demodulation,[],[f1559,f2659])).

fof(f2659,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X18)))) ),
    inference(forward_demodulation,[],[f2658,f19])).

fof(f2658,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X18,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f2386,f2508])).

fof(f2508,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X9))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9))))))) ),
    inference(forward_demodulation,[],[f2507,f2505])).

fof(f2505,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f2504,f19])).

fof(f2504,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X5))) ),
    inference(forward_demodulation,[],[f2503,f54])).

fof(f2503,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X4,X4)),X5))) ),
    inference(forward_demodulation,[],[f2341,f19])).

fof(f2341,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))),X5))) ),
    inference(superposition,[],[f217,f54])).

fof(f217,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X15,X16))))))) ),
    inference(forward_demodulation,[],[f216,f31])).

fof(f216,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))))) ),
    inference(forward_demodulation,[],[f215,f31])).

fof(f215,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) ),
    inference(forward_demodulation,[],[f214,f31])).

fof(f214,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))))),X16) ),
    inference(forward_demodulation,[],[f180,f31])).

fof(f180,plain,(
    ! [X14,X15,X13,X16] : k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16) ),
    inference(superposition,[],[f31,f31])).

fof(f2507,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X9))))))))) ),
    inference(forward_demodulation,[],[f2506,f31])).

fof(f2506,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9))))))) ),
    inference(forward_demodulation,[],[f2342,f217])).

fof(f2342,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7)))),X9))) ),
    inference(superposition,[],[f217,f28])).

fof(f2386,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X18,k1_xboole_0))))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))))) ),
    inference(superposition,[],[f217,f19])).

fof(f1559,plain,(
    ! [X45,X46,X44] : r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X45,X46)),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46)))))))) ),
    inference(forward_demodulation,[],[f1390,f28])).

fof(f1390,plain,(
    ! [X45,X46,X44] : r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46)))),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46)))))))) ),
    inference(superposition,[],[f191,f226])).

fof(f226,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))))))))) ),
    inference(forward_demodulation,[],[f225,f31])).

fof(f225,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9))))))) ),
    inference(forward_demodulation,[],[f188,f31])).

fof(f188,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9))))) ),
    inference(superposition,[],[f31,f28])).

fof(f191,plain,(
    ! [X4,X2,X3] : r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4) ),
    inference(superposition,[],[f20,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (29990)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (29982)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (29988)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (29992)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (29989)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (29981)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (29984)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (29991)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (29978)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (29983)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (29986)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (29980)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (29993)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.53  % (29995)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (29979)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (29987)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.54  % (29994)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (29985)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 5.32/1.03  % (29979)Refutation found. Thanks to Tanya!
% 5.32/1.03  % SZS status Theorem for theBenchmark
% 5.32/1.03  % SZS output start Proof for theBenchmark
% 5.32/1.03  fof(f10802,plain,(
% 5.32/1.03    $false),
% 5.32/1.03    inference(resolution,[],[f10801,f18])).
% 5.32/1.03  fof(f18,plain,(
% 5.32/1.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 5.32/1.03    inference(cnf_transformation,[],[f15])).
% 5.32/1.03  fof(f15,plain,(
% 5.32/1.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 5.32/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 5.32/1.03  fof(f14,plain,(
% 5.32/1.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 5.32/1.03    introduced(choice_axiom,[])).
% 5.32/1.03  fof(f11,plain,(
% 5.32/1.03    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 5.32/1.03    inference(ennf_transformation,[],[f10])).
% 5.32/1.03  fof(f10,negated_conjecture,(
% 5.32/1.03    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 5.32/1.03    inference(negated_conjecture,[],[f9])).
% 5.32/1.03  fof(f9,conjecture,(
% 5.32/1.03    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 5.32/1.03  fof(f10801,plain,(
% 5.32/1.03    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 5.32/1.03    inference(resolution,[],[f10783,f23])).
% 5.32/1.03  fof(f23,plain,(
% 5.32/1.03    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 5.32/1.03    inference(cnf_transformation,[],[f12])).
% 5.32/1.03  fof(f12,plain,(
% 5.32/1.03    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 5.32/1.03    inference(ennf_transformation,[],[f2])).
% 5.32/1.03  fof(f2,axiom,(
% 5.32/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 5.32/1.03  fof(f10783,plain,(
% 5.32/1.03    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 5.32/1.03    inference(superposition,[],[f10419,f3751])).
% 5.32/1.03  fof(f3751,plain,(
% 5.32/1.03    ( ! [X57] : (k4_xboole_0(sK0,X57) = k4_xboole_0(k4_xboole_0(sK0,X57),k4_xboole_0(sK1,sK2))) )),
% 5.32/1.03    inference(superposition,[],[f147,f3645])).
% 5.32/1.03  fof(f3645,plain,(
% 5.32/1.03    ( ! [X9] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X9))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f3556,f19])).
% 5.32/1.03  fof(f19,plain,(
% 5.32/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.32/1.03    inference(cnf_transformation,[],[f3])).
% 5.32/1.03  fof(f3,axiom,(
% 5.32/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 5.32/1.03  fof(f3556,plain,(
% 5.32/1.03    ( ! [X9] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X9))) )),
% 5.32/1.03    inference(superposition,[],[f28,f213])).
% 5.32/1.03  fof(f213,plain,(
% 5.32/1.03    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12)))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f212,f102])).
% 5.32/1.03  fof(f102,plain,(
% 5.32/1.03    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 5.32/1.03    inference(forward_demodulation,[],[f88,f19])).
% 5.32/1.03  fof(f88,plain,(
% 5.32/1.03    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X2)) )),
% 5.32/1.03    inference(superposition,[],[f28,f49])).
% 5.32/1.03  fof(f49,plain,(
% 5.32/1.03    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 5.32/1.03    inference(resolution,[],[f30,f35])).
% 5.32/1.03  fof(f35,plain,(
% 5.32/1.03    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 5.32/1.03    inference(resolution,[],[f23,f32])).
% 5.32/1.03  fof(f32,plain,(
% 5.32/1.03    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 5.32/1.03    inference(superposition,[],[f20,f19])).
% 5.32/1.03  fof(f20,plain,(
% 5.32/1.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 5.32/1.03    inference(cnf_transformation,[],[f7])).
% 5.32/1.03  fof(f7,axiom,(
% 5.32/1.03    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 5.32/1.03  fof(f30,plain,(
% 5.32/1.03    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.32/1.03    inference(definition_unfolding,[],[f24,f21])).
% 5.32/1.03  fof(f21,plain,(
% 5.32/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.32/1.03    inference(cnf_transformation,[],[f5])).
% 5.32/1.03  fof(f5,axiom,(
% 5.32/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.32/1.03  fof(f24,plain,(
% 5.32/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.32/1.03    inference(cnf_transformation,[],[f16])).
% 5.32/1.03  fof(f16,plain,(
% 5.32/1.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.32/1.03    inference(nnf_transformation,[],[f1])).
% 5.32/1.03  fof(f1,axiom,(
% 5.32/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.32/1.03  fof(f212,plain,(
% 5.32/1.03    ( ! [X12] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k1_xboole_0,X12)) )),
% 5.32/1.03    inference(forward_demodulation,[],[f179,f54])).
% 5.32/1.03  fof(f54,plain,(
% 5.32/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 5.32/1.03    inference(forward_demodulation,[],[f46,f19])).
% 5.32/1.03  fof(f46,plain,(
% 5.32/1.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 5.32/1.03    inference(resolution,[],[f30,f32])).
% 5.32/1.03  fof(f179,plain,(
% 5.32/1.03    ( ! [X12] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X12)) )),
% 5.32/1.03    inference(superposition,[],[f31,f157])).
% 5.32/1.03  fof(f157,plain,(
% 5.32/1.03    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 5.32/1.03    inference(superposition,[],[f147,f104])).
% 5.32/1.03  fof(f104,plain,(
% 5.32/1.03    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 5.32/1.03    inference(forward_demodulation,[],[f89,f19])).
% 5.32/1.03  fof(f89,plain,(
% 5.32/1.03    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 5.32/1.03    inference(superposition,[],[f28,f53])).
% 5.32/1.03  fof(f53,plain,(
% 5.32/1.03    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 5.32/1.03    inference(resolution,[],[f30,f17])).
% 5.32/1.03  fof(f17,plain,(
% 5.32/1.03    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 5.32/1.03    inference(cnf_transformation,[],[f15])).
% 5.32/1.03  fof(f31,plain,(
% 5.32/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 5.32/1.03    inference(definition_unfolding,[],[f26,f21,f21])).
% 5.32/1.03  fof(f26,plain,(
% 5.32/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.32/1.03    inference(cnf_transformation,[],[f6])).
% 5.32/1.03  fof(f6,axiom,(
% 5.32/1.03    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.32/1.03  fof(f28,plain,(
% 5.32/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 5.32/1.03    inference(definition_unfolding,[],[f22,f21])).
% 5.32/1.03  fof(f22,plain,(
% 5.32/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 5.32/1.03    inference(cnf_transformation,[],[f4])).
% 5.32/1.03  fof(f4,axiom,(
% 5.32/1.03    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 5.32/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 5.32/1.03  fof(f147,plain,(
% 5.32/1.03    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) )),
% 5.32/1.03    inference(forward_demodulation,[],[f135,f19])).
% 5.32/1.03  fof(f135,plain,(
% 5.32/1.03    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 5.32/1.03    inference(superposition,[],[f28,f48])).
% 5.32/1.03  fof(f48,plain,(
% 5.32/1.03    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 5.32/1.03    inference(resolution,[],[f30,f34])).
% 5.32/1.03  fof(f34,plain,(
% 5.32/1.03    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 5.32/1.03    inference(resolution,[],[f23,f20])).
% 5.32/1.03  fof(f10419,plain,(
% 5.32/1.03    ( ! [X17,X15,X16] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X16,X15),k4_xboole_0(X17,X15)),X17)) )),
% 5.32/1.03    inference(superposition,[],[f10311,f147])).
% 5.32/1.03  fof(f10311,plain,(
% 5.32/1.03    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),X3)) )),
% 5.32/1.03    inference(forward_demodulation,[],[f10310,f19])).
% 5.32/1.03  fof(f10310,plain,(
% 5.32/1.03    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),k4_xboole_0(X3,k1_xboole_0))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f10228,f54])).
% 5.32/1.03  fof(f10228,plain,(
% 5.32/1.03    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X4,X2))),k4_xboole_0(X3,k4_xboole_0(X2,X2)))) )),
% 5.32/1.03    inference(superposition,[],[f2673,f197])).
% 5.32/1.03  fof(f197,plain,(
% 5.32/1.03    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24)))) = X24) )),
% 5.32/1.03    inference(superposition,[],[f147,f31])).
% 5.32/1.03  fof(f2673,plain,(
% 5.32/1.03    ( ! [X45,X46,X44] : (r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X45,X46)),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X45,X46))))))) )),
% 5.32/1.03    inference(backward_demodulation,[],[f1559,f2659])).
% 5.32/1.03  fof(f2659,plain,(
% 5.32/1.03    ( ! [X17,X18,X16] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,X18))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2658,f19])).
% 5.32/1.03  fof(f2658,plain,(
% 5.32/1.03    ( ! [X17,X18,X16] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18)))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X18,k1_xboole_0)))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2386,f2508])).
% 5.32/1.03  fof(f2508,plain,(
% 5.32/1.03    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X9))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9)))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2507,f2505])).
% 5.32/1.03  fof(f2505,plain,(
% 5.32/1.03    ( ! [X4,X5,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2504,f19])).
% 5.32/1.03  fof(f2504,plain,(
% 5.32/1.03    ( ! [X4,X5,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X5)))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2503,f54])).
% 5.32/1.03  fof(f2503,plain,(
% 5.32/1.03    ( ! [X4,X5,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X4,X4)),X5)))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2341,f19])).
% 5.32/1.03  fof(f2341,plain,(
% 5.32/1.03    ( ! [X4,X5,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,X5))))))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))),X5)))) )),
% 5.32/1.03    inference(superposition,[],[f217,f54])).
% 5.32/1.03  fof(f217,plain,(
% 5.32/1.03    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X15,X16)))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f216,f31])).
% 5.32/1.03  fof(f216,plain,(
% 5.32/1.03    ( ! [X14,X15,X13,X16] : (k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16)))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f215,f31])).
% 5.32/1.03  fof(f215,plain,(
% 5.32/1.03    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16)))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f214,f31])).
% 5.32/1.03  fof(f214,plain,(
% 5.32/1.03    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))))),X16)) )),
% 5.32/1.03    inference(forward_demodulation,[],[f180,f31])).
% 5.32/1.03  fof(f180,plain,(
% 5.32/1.03    ( ! [X14,X15,X13,X16] : (k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,k4_xboole_0(X14,X15)))),X16)) )),
% 5.32/1.03    inference(superposition,[],[f31,f31])).
% 5.32/1.03  fof(f2507,plain,(
% 5.32/1.03    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X7,X9)))))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2506,f31])).
% 5.32/1.03  fof(f2506,plain,(
% 5.32/1.03    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X7,X9)))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f2342,f217])).
% 5.32/1.03  fof(f2342,plain,(
% 5.32/1.03    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),X9))))))) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X6,X7)))),X9)))) )),
% 5.32/1.03    inference(superposition,[],[f217,f28])).
% 5.32/1.03  fof(f2386,plain,(
% 5.32/1.03    ( ! [X17,X18,X16] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X18,k1_xboole_0))))))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X16,X18))))))) )),
% 5.32/1.03    inference(superposition,[],[f217,f19])).
% 5.32/1.03  fof(f1559,plain,(
% 5.32/1.03    ( ! [X45,X46,X44] : (r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X45,X46)),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46))))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f1390,f28])).
% 5.32/1.03  fof(f1390,plain,(
% 5.32/1.03    ( ! [X45,X46,X44] : (r1_xboole_0(k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46)))),k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,k4_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46))))))))) )),
% 5.32/1.03    inference(superposition,[],[f191,f226])).
% 5.32/1.03  fof(f226,plain,(
% 5.32/1.03    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9))) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,X9)))))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f225,f31])).
% 5.32/1.03  fof(f225,plain,(
% 5.32/1.03    ( ! [X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)))))))) )),
% 5.32/1.03    inference(forward_demodulation,[],[f188,f31])).
% 5.32/1.03  fof(f188,plain,(
% 5.32/1.03    ( ! [X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X8,k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X8)),X9)))))) )),
% 5.32/1.03    inference(superposition,[],[f31,f28])).
% 5.32/1.03  fof(f191,plain,(
% 5.32/1.03    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4))),X4)) )),
% 5.32/1.03    inference(superposition,[],[f20,f31])).
% 5.32/1.03  % SZS output end Proof for theBenchmark
% 5.32/1.03  % (29979)------------------------------
% 5.32/1.03  % (29979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.32/1.03  % (29979)Termination reason: Refutation
% 5.32/1.03  
% 5.32/1.03  % (29979)Memory used [KB]: 7164
% 5.32/1.03  % (29979)Time elapsed: 0.612 s
% 5.32/1.03  % (29979)------------------------------
% 5.32/1.03  % (29979)------------------------------
% 5.32/1.04  % (29977)Success in time 0.677 s
%------------------------------------------------------------------------------
