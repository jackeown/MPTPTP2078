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
% DateTime   : Thu Dec  3 12:32:23 EST 2020

% Result     : Theorem 38.64s
% Output     : Refutation 38.64s
% Verified   : 
% Statistics : Number of formulae       :  162 (75240 expanded)
%              Number of leaves         :   13 (24504 expanded)
%              Depth                    :   43
%              Number of atoms          :  167 (80780 expanded)
%              Number of equality atoms :  166 (80779 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48743,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48742,f29213])).

fof(f29213,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12)) ),
    inference(forward_demodulation,[],[f29063,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k4_xboole_0(k1_xboole_0,X0) != X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f28,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f67,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f63,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f63,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(superposition,[],[f49,f33])).

fof(f49,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f35,f21])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f29063,plain,(
    ! [X12,X13] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X12,X13))) = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12)) ),
    inference(superposition,[],[f36,f28469])).

fof(f28469,plain,(
    ! [X206,X207] : k5_xboole_0(X207,X206) = k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) ),
    inference(forward_demodulation,[],[f28468,f283])).

fof(f283,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f260,f114])).

fof(f114,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f35,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f98,f72])).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f36,f21])).

fof(f260,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f157,f155])).

fof(f155,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f149,f21])).

fof(f149,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f33,f112])).

fof(f157,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f155])).

fof(f28468,plain,(
    ! [X206,X207] : k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X207,X206)) ),
    inference(forward_demodulation,[],[f28220,f72])).

fof(f28220,plain,(
    ! [X206,X207] : k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X206,X207)),k5_xboole_0(X207,X206)) ),
    inference(superposition,[],[f23512,f1942])).

fof(f1942,plain,(
    ! [X0,X1] : k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f711,f155])).

fof(f711,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f300,f342])).

fof(f342,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f328,f114])).

fof(f328,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f285,f156])).

fof(f156,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f155,f29])).

fof(f285,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f157,f283])).

fof(f300,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) = X14 ),
    inference(forward_demodulation,[],[f269,f283])).

fof(f269,plain,(
    ! [X14,X12,X13] : k5_xboole_0(k1_xboole_0,X14) = k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) ),
    inference(superposition,[],[f157,f29])).

fof(f23512,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f23002,f2025])).

fof(f2025,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24)) ),
    inference(forward_demodulation,[],[f1971,f29])).

fof(f1971,plain,(
    ! [X24,X23,X25] : k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24) ),
    inference(superposition,[],[f711,f342])).

fof(f23002,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f300,f22739])).

fof(f22739,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = X7 ),
    inference(forward_demodulation,[],[f22738,f1132])).

fof(f1132,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,X17)) = X17 ),
    inference(forward_demodulation,[],[f1131,f114])).

fof(f1131,plain,(
    ! [X17,X16] : k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f1111,f112])).

fof(f1111,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k4_xboole_0(X16,X17)) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f104,f1063])).

fof(f1063,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f1023,f114])).

fof(f1023,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f112])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f32,f24])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f33,f36])).

fof(f22738,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f22737,f2965])).

fof(f2965,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) = k4_xboole_0(X7,X5) ),
    inference(backward_demodulation,[],[f1065,f2919])).

fof(f2919,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X4,X2) ),
    inference(superposition,[],[f40,f373])).

fof(f373,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(superposition,[],[f352,f33])).

fof(f352,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f342,f285])).

fof(f1065,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) ),
    inference(forward_demodulation,[],[f1025,f880])).

fof(f880,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f369,f33])).

fof(f369,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f361,f29])).

fof(f361,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f29,f342])).

fof(f1025,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) ),
    inference(superposition,[],[f40,f36])).

fof(f22737,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) ),
    inference(forward_demodulation,[],[f22436,f21])).

fof(f22436,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) = k4_xboole_0(k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),k1_xboole_0) ),
    inference(superposition,[],[f36,f18092])).

fof(f18092,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4))),X4) ),
    inference(superposition,[],[f2965,f112])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48742,plain,(
    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f48741,f29213])).

fof(f48741,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f406,f48740])).

fof(f48740,plain,(
    ! [X267,X268] : k5_xboole_0(X267,X268) = k4_xboole_0(k5_xboole_0(X268,k4_xboole_0(X267,X268)),k4_xboole_0(X268,k4_xboole_0(X268,X267))) ),
    inference(forward_demodulation,[],[f48448,f48622])).

fof(f48622,plain,(
    ! [X41,X42] : k4_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(X42,k5_xboole_0(X41,X42)) ),
    inference(forward_demodulation,[],[f48621,f138])).

fof(f138,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f48621,plain,(
    ! [X41,X42] : k5_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(X42,k5_xboole_0(X41,X42)) ),
    inference(forward_demodulation,[],[f48367,f45608])).

fof(f45608,plain,(
    ! [X111,X112] : k4_xboole_0(X112,X111) = k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) ),
    inference(forward_demodulation,[],[f45604,f114])).

fof(f45604,plain,(
    ! [X111,X112] : k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k1_xboole_0) ),
    inference(backward_demodulation,[],[f33325,f45338])).

fof(f45338,plain,(
    ! [X118,X117] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X117,X118),k5_xboole_0(X117,X118)) ),
    inference(superposition,[],[f45226,f353])).

fof(f353,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f342,f342])).

fof(f45226,plain,(
    ! [X31,X32] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32) ),
    inference(forward_demodulation,[],[f45039,f72])).

fof(f45039,plain,(
    ! [X31,X32] : k4_xboole_0(k1_xboole_0,X32) = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32) ),
    inference(superposition,[],[f2963,f23310])).

fof(f23310,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(backward_demodulation,[],[f22631,f23014])).

fof(f23014,plain,(
    ! [X33,X32] : k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32)) ),
    inference(superposition,[],[f927,f22739])).

fof(f927,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12))) ),
    inference(forward_demodulation,[],[f900,f29])).

fof(f900,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12)) ),
    inference(superposition,[],[f369,f360])).

fof(f360,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f285,f342])).

fof(f22631,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22630,f13581])).

fof(f13581,plain,(
    ! [X101,X99,X100] : k5_xboole_0(k4_xboole_0(X99,X100),k4_xboole_0(X99,k4_xboole_0(X100,X101))) = k4_xboole_0(X99,k5_xboole_0(k4_xboole_0(X100,X101),k4_xboole_0(X99,X100))) ),
    inference(forward_demodulation,[],[f13503,f1430])).

fof(f1430,plain,(
    ! [X35,X33,X36,X34] : k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X34,X35)),k4_xboole_0(X33,X34)) = k4_xboole_0(X36,k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34))) ),
    inference(superposition,[],[f40,f1076])).

fof(f1076,plain,(
    ! [X26,X27,X25] : k4_xboole_0(X27,X25) = k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) ),
    inference(forward_demodulation,[],[f1032,f114])).

fof(f1032,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) = k4_xboole_0(X27,k5_xboole_0(X25,k1_xboole_0)) ),
    inference(superposition,[],[f40,f459])).

fof(f459,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f458,f155])).

fof(f458,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f438,f134])).

fof(f134,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f37,f36])).

fof(f438,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f104,f36])).

fof(f13503,plain,(
    ! [X101,X99,X100] : k4_xboole_0(k4_xboole_0(X99,k4_xboole_0(X100,X101)),k4_xboole_0(X99,X100)) = k5_xboole_0(k4_xboole_0(X99,X100),k4_xboole_0(X99,k4_xboole_0(X100,X101))) ),
    inference(superposition,[],[f390,f2919])).

fof(f390,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f353,f33])).

fof(f22630,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22629,f883])).

fof(f883,plain,(
    ! [X19,X17,X18] : k5_xboole_0(X19,k4_xboole_0(X17,X18)) = k5_xboole_0(X17,k5_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,X18)))) ),
    inference(superposition,[],[f369,f138])).

fof(f22629,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9))))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22628,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f22628,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f22390,f3054])).

fof(f3054,plain,(
    ! [X64,X65,X63] : k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(X65,k5_xboole_0(X64,X63)) ),
    inference(forward_demodulation,[],[f3000,f114])).

fof(f3000,plain,(
    ! [X64,X65,X63] : k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(k5_xboole_0(X65,k1_xboole_0),k5_xboole_0(X64,X63)) ),
    inference(superposition,[],[f379,f2087])).

fof(f2087,plain,(
    ! [X26,X25] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X25,X26),k5_xboole_0(X26,X25)) ),
    inference(superposition,[],[f342,f1942])).

fof(f379,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f352,f29])).

fof(f22390,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f18092,f37])).

fof(f2963,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,X14) ),
    inference(backward_demodulation,[],[f1071,f2919])).

fof(f1071,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X14,X15)),X14) ),
    inference(forward_demodulation,[],[f1070,f1065])).

fof(f1070,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f1069,f880])).

fof(f1069,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f1028,f360])).

fof(f1028,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f40,f134])).

fof(f33325,plain,(
    ! [X111,X112] : k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k4_xboole_0(k4_xboole_0(X111,X112),k5_xboole_0(X111,X112))) ),
    inference(superposition,[],[f26323,f23512])).

fof(f26323,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15)) ),
    inference(superposition,[],[f688,f23006])).

fof(f23006,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k5_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) ),
    inference(superposition,[],[f395,f22739])).

fof(f395,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),k5_xboole_0(X9,X10)) = X11 ),
    inference(superposition,[],[f353,f29])).

fof(f688,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4 ),
    inference(superposition,[],[f300,f360])).

fof(f48367,plain,(
    ! [X41,X42] : k4_xboole_0(X42,k5_xboole_0(X41,X42)) = k5_xboole_0(X42,k4_xboole_0(k5_xboole_0(X41,X42),k4_xboole_0(X41,X42))) ),
    inference(superposition,[],[f104,f45739])).

fof(f45739,plain,(
    ! [X33,X34] : k4_xboole_0(X34,X33) = k4_xboole_0(k5_xboole_0(X34,X33),X33) ),
    inference(backward_demodulation,[],[f28152,f45738])).

fof(f45738,plain,(
    ! [X241,X242] : k4_xboole_0(X242,X241) = k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) ),
    inference(forward_demodulation,[],[f45737,f134])).

fof(f45737,plain,(
    ! [X241,X242] : k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k4_xboole_0(X242,k4_xboole_0(X241,k4_xboole_0(X241,X242))) ),
    inference(forward_demodulation,[],[f45736,f23309])).

fof(f23309,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(X15,X14))) ),
    inference(backward_demodulation,[],[f18272,f23014])).

fof(f18272,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15)))) ),
    inference(forward_demodulation,[],[f18271,f13581])).

fof(f18271,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14)))) ),
    inference(forward_demodulation,[],[f18270,f883])).

fof(f18270,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X14)))))) ),
    inference(forward_demodulation,[],[f18269,f38])).

fof(f18269,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14)))) ),
    inference(forward_demodulation,[],[f18057,f3054])).

fof(f18057,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14),k4_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f2965,f37])).

fof(f45736,plain,(
    ! [X241,X242] : k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k4_xboole_0(X242,k4_xboole_0(X241,k5_xboole_0(X242,X241))) ),
    inference(forward_demodulation,[],[f45464,f283])).

fof(f45464,plain,(
    ! [X241,X242] : k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X242,k4_xboole_0(X241,k5_xboole_0(X242,X241)))) ),
    inference(superposition,[],[f23014,f45226])).

fof(f28152,plain,(
    ! [X33,X34] : k4_xboole_0(k5_xboole_0(X34,X33),X33) = k5_xboole_0(k4_xboole_0(X33,k5_xboole_0(X34,X33)),X34) ),
    inference(superposition,[],[f23512,f342])).

fof(f48448,plain,(
    ! [X267,X268] : k5_xboole_0(X267,X268) = k4_xboole_0(k5_xboole_0(X268,k4_xboole_0(X267,X268)),k4_xboole_0(X268,k5_xboole_0(X267,X268))) ),
    inference(superposition,[],[f28459,f45739])).

fof(f28459,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = X106 ),
    inference(forward_demodulation,[],[f28458,f114])).

fof(f28458,plain,(
    ! [X105,X106] : k5_xboole_0(X106,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) ),
    inference(forward_demodulation,[],[f28457,f459])).

fof(f28457,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(X106,k4_xboole_0(k4_xboole_0(X105,X106),X105)) ),
    inference(forward_demodulation,[],[f28456,f360])).

fof(f28456,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106) ),
    inference(forward_demodulation,[],[f28455,f1535])).

fof(f1535,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(X27,X26),X28) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) ),
    inference(forward_demodulation,[],[f1534,f114])).

fof(f1534,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1508,f112])).

fof(f1508,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k4_xboole_0(X26,X26)) ),
    inference(superposition,[],[f104,f1387])).

fof(f1387,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X18,X17),X19)) = X17 ),
    inference(superposition,[],[f1076,f1132])).

fof(f28455,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106),X106) ),
    inference(forward_demodulation,[],[f28182,f40])).

fof(f28182,plain,(
    ! [X105,X106] : k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,k4_xboole_0(X106,X105))),X106) ),
    inference(superposition,[],[f23512,f23549])).

fof(f23549,plain,(
    ! [X35,X36] : k5_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(X35,k4_xboole_0(X36,X35))) = X36 ),
    inference(superposition,[],[f353,f23002])).

fof(f406,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f28])).

fof(f34,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f24,f25])).

fof(f20,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (14656)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (14645)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.57  % (14648)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (14648)Refutation not found, incomplete strategy% (14648)------------------------------
% 0.22/0.57  % (14648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14637)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (14653)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (14640)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (14647)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (14653)Refutation not found, incomplete strategy% (14653)------------------------------
% 0.22/0.58  % (14653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (14641)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (14653)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (14653)Memory used [KB]: 10618
% 0.22/0.59  % (14653)Time elapsed: 0.148 s
% 0.22/0.59  % (14653)------------------------------
% 0.22/0.59  % (14653)------------------------------
% 0.22/0.59  % (14632)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (14636)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.59  % (14660)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.59  % (14634)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.60  % (14648)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (14648)Memory used [KB]: 10618
% 0.22/0.60  % (14648)Time elapsed: 0.139 s
% 0.22/0.60  % (14648)------------------------------
% 0.22/0.60  % (14648)------------------------------
% 0.22/0.60  % (14635)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.60  % (14646)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (14633)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (14633)Refutation not found, incomplete strategy% (14633)------------------------------
% 0.22/0.60  % (14633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (14633)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (14633)Memory used [KB]: 10618
% 0.22/0.60  % (14633)Time elapsed: 0.167 s
% 0.22/0.60  % (14633)------------------------------
% 0.22/0.60  % (14633)------------------------------
% 1.87/0.60  % (14639)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.87/0.61  % (14639)Refutation not found, incomplete strategy% (14639)------------------------------
% 1.87/0.61  % (14639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (14639)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (14639)Memory used [KB]: 10618
% 1.87/0.61  % (14639)Time elapsed: 0.179 s
% 1.87/0.61  % (14639)------------------------------
% 1.87/0.61  % (14639)------------------------------
% 1.87/0.61  % (14658)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.87/0.61  % (14654)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.87/0.61  % (14651)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.87/0.61  % (14654)Refutation not found, incomplete strategy% (14654)------------------------------
% 1.87/0.61  % (14654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (14654)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (14654)Memory used [KB]: 1663
% 1.87/0.61  % (14654)Time elapsed: 0.130 s
% 1.87/0.61  % (14654)------------------------------
% 1.87/0.61  % (14654)------------------------------
% 1.87/0.61  % (14651)Refutation not found, incomplete strategy% (14651)------------------------------
% 1.87/0.61  % (14651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (14651)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (14651)Memory used [KB]: 10618
% 1.87/0.61  % (14651)Time elapsed: 0.180 s
% 1.87/0.61  % (14651)------------------------------
% 1.87/0.61  % (14651)------------------------------
% 1.87/0.61  % (14652)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.87/0.61  % (14652)Refutation not found, incomplete strategy% (14652)------------------------------
% 1.87/0.61  % (14652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (14657)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.87/0.61  % (14649)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.87/0.61  % (14650)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.61  % (14659)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.87/0.62  % (14655)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.62  % (14631)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.87/0.62  % (14642)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.87/0.62  % (14631)Refutation not found, incomplete strategy% (14631)------------------------------
% 1.87/0.62  % (14631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.62  % (14631)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.62  
% 1.87/0.62  % (14631)Memory used [KB]: 1663
% 1.87/0.62  % (14631)Time elapsed: 0.186 s
% 1.87/0.62  % (14631)------------------------------
% 1.87/0.62  % (14631)------------------------------
% 2.03/0.62  % (14638)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.03/0.62  % (14652)Termination reason: Refutation not found, incomplete strategy
% 2.03/0.63  % (14644)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.03/0.63  
% 2.03/0.63  % (14652)Memory used [KB]: 1663
% 2.03/0.63  % (14652)Time elapsed: 0.182 s
% 2.03/0.63  % (14652)------------------------------
% 2.03/0.63  % (14652)------------------------------
% 2.03/0.63  % (14643)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.93/0.80  % (14686)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.93/0.81  % (14688)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.93/0.84  % (14685)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.93/0.85  % (14636)Time limit reached!
% 2.93/0.85  % (14636)------------------------------
% 2.93/0.85  % (14636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.85  % (14636)Termination reason: Time limit
% 2.93/0.85  % (14636)Termination phase: Saturation
% 2.93/0.85  
% 2.93/0.85  % (14636)Memory used [KB]: 7931
% 2.93/0.85  % (14636)Time elapsed: 0.400 s
% 2.93/0.85  % (14636)------------------------------
% 2.93/0.85  % (14636)------------------------------
% 3.38/0.86  % (14687)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.38/0.86  % (14685)Refutation not found, incomplete strategy% (14685)------------------------------
% 3.38/0.86  % (14685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.38/0.86  % (14685)Termination reason: Refutation not found, incomplete strategy
% 3.38/0.86  
% 3.38/0.86  % (14685)Memory used [KB]: 6140
% 3.38/0.86  % (14685)Time elapsed: 0.206 s
% 3.38/0.86  % (14685)------------------------------
% 3.38/0.86  % (14685)------------------------------
% 3.38/0.86  % (14690)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.38/0.87  % (14689)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.56/0.89  % (14692)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.87/0.93  % (14643)Time limit reached!
% 3.87/0.93  % (14643)------------------------------
% 3.87/0.93  % (14643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.93  % (14643)Termination reason: Time limit
% 3.87/0.93  % (14643)Termination phase: Saturation
% 3.87/0.93  
% 3.87/0.93  % (14643)Memory used [KB]: 8571
% 3.87/0.93  % (14643)Time elapsed: 0.500 s
% 3.87/0.93  % (14643)------------------------------
% 3.87/0.93  % (14643)------------------------------
% 3.97/0.95  % (14691)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.97/0.98  % (14632)Time limit reached!
% 3.97/0.98  % (14632)------------------------------
% 3.97/0.98  % (14632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.98  % (14632)Termination reason: Time limit
% 3.97/0.98  % (14632)Termination phase: Saturation
% 3.97/0.98  
% 3.97/0.98  % (14632)Memory used [KB]: 7164
% 3.97/0.98  % (14632)Time elapsed: 0.508 s
% 3.97/0.98  % (14632)------------------------------
% 3.97/0.98  % (14632)------------------------------
% 3.97/0.98  % (14641)Time limit reached!
% 3.97/0.98  % (14641)------------------------------
% 3.97/0.98  % (14641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.00  % (14641)Termination reason: Time limit
% 3.97/1.00  % (14641)Termination phase: Saturation
% 3.97/1.00  
% 3.97/1.00  % (14641)Memory used [KB]: 22387
% 3.97/1.00  % (14641)Time elapsed: 0.500 s
% 3.97/1.00  % (14641)------------------------------
% 3.97/1.00  % (14641)------------------------------
% 4.35/1.04  % (14647)Time limit reached!
% 4.35/1.04  % (14647)------------------------------
% 4.35/1.04  % (14647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.04  % (14647)Termination reason: Time limit
% 4.35/1.04  % (14647)Termination phase: Saturation
% 4.35/1.04  
% 4.35/1.04  % (14647)Memory used [KB]: 16119
% 4.35/1.04  % (14647)Time elapsed: 0.600 s
% 4.35/1.04  % (14647)------------------------------
% 4.35/1.04  % (14647)------------------------------
% 4.35/1.05  % (14694)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.35/1.05  % (14693)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.35/1.06  % (14659)Time limit reached!
% 4.35/1.06  % (14659)------------------------------
% 4.35/1.06  % (14659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/1.07  % (14659)Termination reason: Time limit
% 4.35/1.07  
% 4.35/1.07  % (14659)Memory used [KB]: 7803
% 4.35/1.07  % (14659)Time elapsed: 0.635 s
% 4.35/1.07  % (14659)------------------------------
% 4.35/1.07  % (14659)------------------------------
% 4.64/1.07  % (14688)Time limit reached!
% 4.64/1.07  % (14688)------------------------------
% 4.64/1.07  % (14688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.07  % (14688)Termination reason: Time limit
% 4.64/1.07  
% 4.64/1.07  % (14688)Memory used [KB]: 7291
% 4.64/1.07  % (14688)Time elapsed: 0.403 s
% 4.64/1.07  % (14688)------------------------------
% 4.64/1.07  % (14688)------------------------------
% 4.64/1.09  % (14638)Time limit reached!
% 4.64/1.09  % (14638)------------------------------
% 4.64/1.09  % (14638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.09  % (14695)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.64/1.09  % (14695)Refutation not found, incomplete strategy% (14695)------------------------------
% 4.64/1.09  % (14695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.09  % (14695)Termination reason: Refutation not found, incomplete strategy
% 4.64/1.09  
% 4.64/1.09  % (14695)Memory used [KB]: 6140
% 4.64/1.09  % (14695)Time elapsed: 0.126 s
% 4.64/1.09  % (14695)------------------------------
% 4.64/1.09  % (14695)------------------------------
% 4.64/1.10  % (14689)Time limit reached!
% 4.64/1.10  % (14689)------------------------------
% 4.64/1.10  % (14689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.10  % (14696)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.64/1.10  % (14696)Refutation not found, incomplete strategy% (14696)------------------------------
% 4.64/1.10  % (14696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.10  % (14696)Termination reason: Refutation not found, incomplete strategy
% 4.64/1.10  
% 4.64/1.10  % (14696)Memory used [KB]: 1663
% 4.64/1.10  % (14696)Time elapsed: 0.101 s
% 4.64/1.10  % (14696)------------------------------
% 4.64/1.10  % (14696)------------------------------
% 4.64/1.10  % (14638)Termination reason: Time limit
% 4.64/1.10  % (14638)Termination phase: Saturation
% 4.64/1.10  
% 4.64/1.10  % (14638)Memory used [KB]: 9978
% 4.64/1.10  % (14638)Time elapsed: 0.600 s
% 4.64/1.10  % (14638)------------------------------
% 4.64/1.10  % (14638)------------------------------
% 4.64/1.11  % (14689)Termination reason: Time limit
% 4.64/1.11  
% 4.64/1.11  % (14689)Memory used [KB]: 12537
% 4.64/1.11  % (14689)Time elapsed: 0.423 s
% 4.64/1.11  % (14689)------------------------------
% 4.64/1.11  % (14689)------------------------------
% 4.64/1.13  % (14697)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 6.17/1.16  % (14710)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.17/1.17  % (14710)Refutation not found, incomplete strategy% (14710)------------------------------
% 6.17/1.17  % (14710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.17/1.17  % (14710)Termination reason: Refutation not found, incomplete strategy
% 6.17/1.17  
% 6.17/1.17  % (14710)Memory used [KB]: 1663
% 6.17/1.17  % (14710)Time elapsed: 0.098 s
% 6.17/1.17  % (14710)------------------------------
% 6.17/1.17  % (14710)------------------------------
% 6.43/1.19  % (14726)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.43/1.20  % (14726)Refutation not found, incomplete strategy% (14726)------------------------------
% 6.43/1.20  % (14726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.43/1.20  % (14726)Termination reason: Refutation not found, incomplete strategy
% 6.43/1.20  
% 6.43/1.20  % (14726)Memory used [KB]: 6140
% 6.43/1.20  % (14726)Time elapsed: 0.077 s
% 6.43/1.20  % (14726)------------------------------
% 6.43/1.20  % (14726)------------------------------
% 6.43/1.20  % (14724)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.43/1.22  % (14737)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.43/1.22  % (14745)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.80/1.23  % (14742)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.80/1.24  % (14743)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.92/1.30  % (14769)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.43/1.34  % (14789)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.66/1.51  % (14737)Time limit reached!
% 8.66/1.51  % (14737)------------------------------
% 8.66/1.51  % (14737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.66/1.52  % (14737)Termination reason: Time limit
% 8.66/1.52  % (14737)Termination phase: Saturation
% 8.66/1.52  
% 8.66/1.52  % (14737)Memory used [KB]: 4221
% 8.66/1.53  % (14737)Time elapsed: 0.400 s
% 8.66/1.53  % (14737)------------------------------
% 8.66/1.53  % (14737)------------------------------
% 8.66/1.53  % (14697)Time limit reached!
% 8.66/1.53  % (14697)------------------------------
% 8.66/1.53  % (14697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.05/1.54  % (14745)Time limit reached!
% 9.05/1.54  % (14745)------------------------------
% 9.05/1.54  % (14745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.05/1.54  % (14745)Termination reason: Time limit
% 9.05/1.54  
% 9.05/1.54  % (14745)Memory used [KB]: 3582
% 9.05/1.54  % (14745)Time elapsed: 0.408 s
% 9.05/1.54  % (14745)------------------------------
% 9.05/1.54  % (14745)------------------------------
% 9.05/1.54  % (14697)Termination reason: Time limit
% 9.05/1.54  % (14697)Termination phase: Saturation
% 9.05/1.54  
% 9.05/1.54  % (14697)Memory used [KB]: 5756
% 9.05/1.54  % (14697)Time elapsed: 0.500 s
% 9.05/1.54  % (14697)------------------------------
% 9.05/1.54  % (14697)------------------------------
% 9.61/1.66  % (14899)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.61/1.67  % (14911)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 10.32/1.70  % (14909)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.32/1.74  % (14655)Time limit reached!
% 10.32/1.74  % (14655)------------------------------
% 10.32/1.74  % (14655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.32/1.75  % (14655)Termination reason: Time limit
% 10.32/1.75  
% 10.32/1.75  % (14655)Memory used [KB]: 16630
% 10.32/1.75  % (14655)Time elapsed: 1.311 s
% 10.32/1.75  % (14655)------------------------------
% 10.32/1.75  % (14655)------------------------------
% 11.62/1.86  % (14940)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 11.62/1.88  % (14940)Refutation not found, incomplete strategy% (14940)------------------------------
% 11.62/1.88  % (14940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.62/1.88  % (14940)Termination reason: Refutation not found, incomplete strategy
% 11.62/1.88  
% 11.62/1.88  % (14940)Memory used [KB]: 6140
% 11.62/1.88  % (14940)Time elapsed: 0.092 s
% 11.62/1.88  % (14940)------------------------------
% 11.62/1.88  % (14940)------------------------------
% 11.62/1.90  % (14691)Time limit reached!
% 11.62/1.90  % (14691)------------------------------
% 11.62/1.90  % (14691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.90  % (14691)Termination reason: Time limit
% 12.14/1.90  % (14691)Termination phase: Saturation
% 12.14/1.90  
% 12.14/1.90  % (14691)Memory used [KB]: 13176
% 12.14/1.90  % (14691)Time elapsed: 1.200 s
% 12.14/1.90  % (14691)------------------------------
% 12.14/1.90  % (14691)------------------------------
% 12.14/1.91  % (14657)Time limit reached!
% 12.14/1.91  % (14657)------------------------------
% 12.14/1.91  % (14657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.91  % (14657)Termination reason: Time limit
% 12.14/1.91  % (14657)Termination phase: Saturation
% 12.14/1.91  
% 12.14/1.91  % (14657)Memory used [KB]: 118718
% 12.14/1.91  % (14657)Time elapsed: 1.200 s
% 12.14/1.91  % (14657)------------------------------
% 12.14/1.91  % (14657)------------------------------
% 12.14/1.94  % (14658)Time limit reached!
% 12.14/1.94  % (14658)------------------------------
% 12.14/1.94  % (14658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.95  % (14658)Termination reason: Time limit
% 12.14/1.95  
% 12.14/1.95  % (14658)Memory used [KB]: 16502
% 12.14/1.95  % (14658)Time elapsed: 1.510 s
% 12.14/1.95  % (14658)------------------------------
% 12.14/1.95  % (14658)------------------------------
% 12.62/1.99  % (14941)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.62/1.99  % (14911)Time limit reached!
% 12.62/1.99  % (14911)------------------------------
% 12.62/1.99  % (14911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.62/2.01  % (14911)Termination reason: Time limit
% 12.62/2.01  % (14911)Termination phase: Saturation
% 12.62/2.01  
% 12.62/2.01  % (14911)Memory used [KB]: 11129
% 12.62/2.01  % (14911)Time elapsed: 0.400 s
% 12.62/2.01  % (14911)------------------------------
% 12.62/2.01  % (14911)------------------------------
% 12.62/2.03  % (14642)Time limit reached!
% 12.62/2.03  % (14642)------------------------------
% 12.62/2.03  % (14642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.62/2.03  % (14642)Termination reason: Time limit
% 12.62/2.03  
% 12.62/2.03  % (14642)Memory used [KB]: 22899
% 12.62/2.03  % (14642)Time elapsed: 1.603 s
% 12.62/2.03  % (14642)------------------------------
% 12.62/2.03  % (14642)------------------------------
% 12.62/2.05  % (14942)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.62/2.05  % (14942)Refutation not found, incomplete strategy% (14942)------------------------------
% 12.62/2.05  % (14942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.34/2.06  % (14942)Termination reason: Refutation not found, incomplete strategy
% 13.34/2.06  
% 13.34/2.06  % (14942)Memory used [KB]: 10618
% 13.34/2.06  % (14942)Time elapsed: 0.105 s
% 13.34/2.06  % (14942)------------------------------
% 13.34/2.06  % (14942)------------------------------
% 13.66/2.12  % (14646)Time limit reached!
% 13.66/2.12  % (14646)------------------------------
% 13.66/2.12  % (14646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.66/2.12  % (14646)Termination reason: Time limit
% 13.66/2.12  % (14646)Termination phase: Saturation
% 13.66/2.12  
% 13.66/2.12  % (14646)Memory used [KB]: 184602
% 13.66/2.12  % (14646)Time elapsed: 1.300 s
% 13.66/2.12  % (14646)------------------------------
% 13.66/2.12  % (14646)------------------------------
% 14.67/2.24  % (14645)Time limit reached!
% 14.67/2.24  % (14645)------------------------------
% 14.67/2.24  % (14645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.67/2.24  % (14645)Termination reason: Time limit
% 14.67/2.24  % (14645)Termination phase: Saturation
% 14.67/2.24  
% 14.67/2.24  % (14645)Memory used [KB]: 21108
% 14.67/2.24  % (14645)Time elapsed: 1.800 s
% 14.67/2.24  % (14645)------------------------------
% 14.67/2.24  % (14645)------------------------------
% 15.13/2.36  % (14635)Time limit reached!
% 15.13/2.36  % (14635)------------------------------
% 15.13/2.36  % (14635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.13/2.36  % (14635)Termination reason: Time limit
% 15.13/2.36  
% 15.13/2.36  % (14635)Memory used [KB]: 139443
% 15.13/2.36  % (14635)Time elapsed: 1.855 s
% 15.13/2.36  % (14635)------------------------------
% 15.13/2.36  % (14635)------------------------------
% 15.90/2.37  % (14941)Time limit reached!
% 15.90/2.37  % (14941)------------------------------
% 15.90/2.37  % (14941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.90/2.37  % (14687)Time limit reached!
% 15.90/2.37  % (14687)------------------------------
% 15.90/2.37  % (14687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.90/2.37  % (14687)Termination reason: Time limit
% 15.90/2.37  % (14687)Termination phase: Saturation
% 15.90/2.37  
% 15.90/2.37  % (14687)Memory used [KB]: 25969
% 15.90/2.37  % (14687)Time elapsed: 1.700 s
% 15.90/2.37  % (14687)------------------------------
% 15.90/2.37  % (14687)------------------------------
% 15.90/2.39  % (14941)Termination reason: Time limit
% 15.90/2.39  % (14941)Termination phase: Saturation
% 15.90/2.39  
% 15.90/2.39  % (14941)Memory used [KB]: 31598
% 15.90/2.39  % (14941)Time elapsed: 0.400 s
% 15.90/2.39  % (14941)------------------------------
% 15.90/2.39  % (14941)------------------------------
% 16.39/2.42  % (14743)Time limit reached!
% 16.39/2.42  % (14743)------------------------------
% 16.39/2.42  % (14743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.39/2.42  % (14743)Termination reason: Time limit
% 16.39/2.42  % (14743)Termination phase: Saturation
% 16.39/2.42  
% 16.39/2.42  % (14743)Memory used [KB]: 18549
% 16.39/2.42  % (14743)Time elapsed: 1.300 s
% 16.39/2.42  % (14743)------------------------------
% 16.39/2.42  % (14743)------------------------------
% 16.43/2.44  % (14637)Time limit reached!
% 16.43/2.44  % (14637)------------------------------
% 16.43/2.44  % (14637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.43/2.44  % (14637)Termination reason: Time limit
% 16.43/2.44  
% 16.43/2.44  % (14637)Memory used [KB]: 27888
% 16.43/2.44  % (14637)Time elapsed: 2.011 s
% 16.43/2.44  % (14637)------------------------------
% 16.43/2.44  % (14637)------------------------------
% 17.02/2.52  % (14649)Time limit reached!
% 17.02/2.52  % (14649)------------------------------
% 17.02/2.52  % (14649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.02/2.52  % (14649)Termination reason: Time limit
% 17.02/2.52  
% 17.02/2.52  % (14649)Memory used [KB]: 37099
% 17.02/2.52  % (14649)Time elapsed: 2.084 s
% 17.02/2.52  % (14649)------------------------------
% 17.02/2.52  % (14649)------------------------------
% 20.07/2.89  % (14693)Time limit reached!
% 20.07/2.89  % (14693)------------------------------
% 20.07/2.89  % (14693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.07/2.89  % (14693)Termination reason: Time limit
% 20.07/2.89  
% 20.07/2.89  % (14693)Memory used [KB]: 125626
% 20.07/2.89  % (14693)Time elapsed: 1.910 s
% 20.07/2.89  % (14693)------------------------------
% 20.07/2.89  % (14693)------------------------------
% 21.15/3.03  % (14650)Time limit reached!
% 21.15/3.03  % (14650)------------------------------
% 21.15/3.03  % (14650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.15/3.03  % (14650)Termination reason: Time limit
% 21.15/3.03  % (14650)Termination phase: Saturation
% 21.15/3.03  
% 21.15/3.03  % (14650)Memory used [KB]: 73943
% 21.15/3.03  % (14650)Time elapsed: 2.600 s
% 21.15/3.03  % (14650)------------------------------
% 21.15/3.03  % (14650)------------------------------
% 24.43/3.44  % (14644)Time limit reached!
% 24.43/3.44  % (14644)------------------------------
% 24.43/3.44  % (14644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.43/3.44  % (14644)Termination reason: Time limit
% 24.43/3.44  
% 24.43/3.44  % (14644)Memory used [KB]: 16247
% 24.43/3.44  % (14644)Time elapsed: 3.015 s
% 24.43/3.44  % (14644)------------------------------
% 24.43/3.44  % (14644)------------------------------
% 24.91/3.52  % (14686)Time limit reached!
% 24.91/3.52  % (14686)------------------------------
% 24.91/3.52  % (14686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.91/3.52  % (14686)Termination reason: Time limit
% 24.91/3.52  % (14686)Termination phase: Saturation
% 24.91/3.52  
% 24.91/3.52  % (14686)Memory used [KB]: 41577
% 24.91/3.52  % (14686)Time elapsed: 2.800 s
% 24.91/3.52  % (14686)------------------------------
% 24.91/3.52  % (14686)------------------------------
% 31.61/4.33  % (14660)Time limit reached!
% 31.61/4.33  % (14660)------------------------------
% 31.61/4.33  % (14660)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.61/4.33  % (14660)Termination reason: Time limit
% 31.61/4.33  % (14660)Termination phase: Saturation
% 31.61/4.33  
% 31.61/4.33  % (14660)Memory used [KB]: 75606
% 31.61/4.33  % (14660)Time elapsed: 3.900 s
% 31.61/4.33  % (14660)------------------------------
% 31.61/4.33  % (14660)------------------------------
% 33.92/4.62  % (14724)Time limit reached!
% 33.92/4.62  % (14724)------------------------------
% 33.92/4.62  % (14724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.92/4.62  % (14724)Termination reason: Time limit
% 33.92/4.62  % (14724)Termination phase: Saturation
% 33.92/4.62  
% 33.92/4.62  % (14724)Memory used [KB]: 84689
% 33.92/4.62  % (14724)Time elapsed: 3.500 s
% 33.92/4.62  % (14724)------------------------------
% 33.92/4.62  % (14724)------------------------------
% 38.64/5.21  % (14692)Refutation found. Thanks to Tanya!
% 38.64/5.21  % SZS status Theorem for theBenchmark
% 38.64/5.21  % SZS output start Proof for theBenchmark
% 38.64/5.21  fof(f48743,plain,(
% 38.64/5.21    $false),
% 38.64/5.21    inference(subsumption_resolution,[],[f48742,f29213])).
% 38.64/5.21  fof(f29213,plain,(
% 38.64/5.21    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f29063,f72])).
% 38.64/5.21  fof(f72,plain,(
% 38.64/5.21    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 38.64/5.21    inference(unit_resulting_resolution,[],[f67,f43])).
% 38.64/5.21  fof(f43,plain,(
% 38.64/5.21    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) != X0 | k1_xboole_0 = X0) )),
% 38.64/5.21    inference(superposition,[],[f28,f21])).
% 38.64/5.21  fof(f21,plain,(
% 38.64/5.21    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 38.64/5.21    inference(cnf_transformation,[],[f6])).
% 38.64/5.21  fof(f6,axiom,(
% 38.64/5.21    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 38.64/5.21  fof(f28,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 38.64/5.21    inference(cnf_transformation,[],[f17])).
% 38.64/5.21  fof(f17,plain,(
% 38.64/5.21    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 38.64/5.21    inference(ennf_transformation,[],[f5])).
% 38.64/5.21  fof(f5,axiom,(
% 38.64/5.21    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 38.64/5.21  fof(f67,plain,(
% 38.64/5.21    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 38.64/5.21    inference(superposition,[],[f63,f33])).
% 38.64/5.21  fof(f33,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 38.64/5.21    inference(definition_unfolding,[],[f26,f25])).
% 38.64/5.21  fof(f25,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f9])).
% 38.64/5.21  fof(f9,axiom,(
% 38.64/5.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 38.64/5.21  fof(f26,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f3])).
% 38.64/5.21  fof(f3,axiom,(
% 38.64/5.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 38.64/5.21  fof(f63,plain,(
% 38.64/5.21    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 38.64/5.21    inference(superposition,[],[f49,f33])).
% 38.64/5.21  fof(f49,plain,(
% 38.64/5.21    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X2))) )),
% 38.64/5.21    inference(superposition,[],[f29,f42])).
% 38.64/5.21  fof(f42,plain,(
% 38.64/5.21    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 38.64/5.21    inference(superposition,[],[f35,f21])).
% 38.64/5.21  fof(f35,plain,(
% 38.64/5.21    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 38.64/5.21    inference(definition_unfolding,[],[f22,f24])).
% 38.64/5.21  fof(f24,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f12])).
% 38.64/5.21  fof(f12,axiom,(
% 38.64/5.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 38.64/5.21  fof(f22,plain,(
% 38.64/5.21    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 38.64/5.21    inference(cnf_transformation,[],[f15])).
% 38.64/5.21  fof(f15,plain,(
% 38.64/5.21    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 38.64/5.21    inference(rectify,[],[f2])).
% 38.64/5.21  fof(f2,axiom,(
% 38.64/5.21    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 38.64/5.21  fof(f29,plain,(
% 38.64/5.21    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f11])).
% 38.64/5.21  fof(f11,axiom,(
% 38.64/5.21    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 38.64/5.21  fof(f29063,plain,(
% 38.64/5.21    ( ! [X12,X13] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X12,X13))) = k4_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X13,X12))) )),
% 38.64/5.21    inference(superposition,[],[f36,f28469])).
% 38.64/5.21  fof(f28469,plain,(
% 38.64/5.21    ( ! [X206,X207] : (k5_xboole_0(X207,X206) = k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28468,f283])).
% 38.64/5.21  fof(f283,plain,(
% 38.64/5.21    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 38.64/5.21    inference(forward_demodulation,[],[f260,f114])).
% 38.64/5.21  fof(f114,plain,(
% 38.64/5.21    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 38.64/5.21    inference(backward_demodulation,[],[f35,f112])).
% 38.64/5.21  fof(f112,plain,(
% 38.64/5.21    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f98,f72])).
% 38.64/5.21  fof(f98,plain,(
% 38.64/5.21    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 38.64/5.21    inference(superposition,[],[f36,f21])).
% 38.64/5.21  fof(f260,plain,(
% 38.64/5.21    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 38.64/5.21    inference(superposition,[],[f157,f155])).
% 38.64/5.21  fof(f155,plain,(
% 38.64/5.21    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f149,f21])).
% 38.64/5.21  fof(f149,plain,(
% 38.64/5.21    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 38.64/5.21    inference(superposition,[],[f33,f112])).
% 38.64/5.21  fof(f157,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 38.64/5.21    inference(superposition,[],[f29,f155])).
% 38.64/5.21  fof(f28468,plain,(
% 38.64/5.21    ( ! [X206,X207] : (k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X207,X206))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28220,f72])).
% 38.64/5.21  fof(f28220,plain,(
% 38.64/5.21    ( ! [X206,X207] : (k4_xboole_0(k5_xboole_0(X206,X207),k1_xboole_0) = k5_xboole_0(k4_xboole_0(k1_xboole_0,k5_xboole_0(X206,X207)),k5_xboole_0(X207,X206))) )),
% 38.64/5.21    inference(superposition,[],[f23512,f1942])).
% 38.64/5.21  fof(f1942,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) )),
% 38.64/5.21    inference(superposition,[],[f711,f155])).
% 38.64/5.21  fof(f711,plain,(
% 38.64/5.21    ( ! [X24,X23,X25] : (k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24))) )),
% 38.64/5.21    inference(superposition,[],[f300,f342])).
% 38.64/5.21  fof(f342,plain,(
% 38.64/5.21    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 38.64/5.21    inference(forward_demodulation,[],[f328,f114])).
% 38.64/5.21  fof(f328,plain,(
% 38.64/5.21    ( ! [X4,X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4))) )),
% 38.64/5.21    inference(superposition,[],[f285,f156])).
% 38.64/5.21  fof(f156,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 38.64/5.21    inference(superposition,[],[f155,f29])).
% 38.64/5.21  fof(f285,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 38.64/5.21    inference(backward_demodulation,[],[f157,f283])).
% 38.64/5.21  fof(f300,plain,(
% 38.64/5.21    ( ! [X14,X12,X13] : (k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14))) = X14) )),
% 38.64/5.21    inference(forward_demodulation,[],[f269,f283])).
% 38.64/5.21  fof(f269,plain,(
% 38.64/5.21    ( ! [X14,X12,X13] : (k5_xboole_0(k1_xboole_0,X14) = k5_xboole_0(k5_xboole_0(X12,X13),k5_xboole_0(X12,k5_xboole_0(X13,X14)))) )),
% 38.64/5.21    inference(superposition,[],[f157,f29])).
% 38.64/5.21  fof(f23512,plain,(
% 38.64/5.21    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(k4_xboole_0(X6,X5),k5_xboole_0(X6,X5))) )),
% 38.64/5.21    inference(superposition,[],[f23002,f2025])).
% 38.64/5.21  fof(f2025,plain,(
% 38.64/5.21    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(X23,k5_xboole_0(X25,X24))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1971,f29])).
% 38.64/5.21  fof(f1971,plain,(
% 38.64/5.21    ( ! [X24,X23,X25] : (k5_xboole_0(k5_xboole_0(X24,X23),X25) = k5_xboole_0(k5_xboole_0(X23,X25),X24)) )),
% 38.64/5.21    inference(superposition,[],[f711,f342])).
% 38.64/5.21  fof(f23002,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 38.64/5.21    inference(superposition,[],[f300,f22739])).
% 38.64/5.21  fof(f22739,plain,(
% 38.64/5.21    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = X7) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22738,f1132])).
% 38.64/5.21  fof(f1132,plain,(
% 38.64/5.21    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,X17)) = X17) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1131,f114])).
% 38.64/5.21  fof(f1131,plain,(
% 38.64/5.21    ( ! [X17,X16] : (k5_xboole_0(X17,k1_xboole_0) = k4_xboole_0(X17,k4_xboole_0(X16,X17))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1111,f112])).
% 38.64/5.21  fof(f1111,plain,(
% 38.64/5.21    ( ! [X17,X16] : (k4_xboole_0(X17,k4_xboole_0(X16,X17)) = k5_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,X17),k4_xboole_0(X16,X17)))) )),
% 38.64/5.21    inference(superposition,[],[f104,f1063])).
% 38.64/5.21  fof(f1063,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1023,f114])).
% 38.64/5.21  fof(f1023,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) )),
% 38.64/5.21    inference(superposition,[],[f40,f112])).
% 38.64/5.21  fof(f40,plain,(
% 38.64/5.21    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 38.64/5.21    inference(definition_unfolding,[],[f32,f24])).
% 38.64/5.21  fof(f32,plain,(
% 38.64/5.21    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f7])).
% 38.64/5.21  fof(f7,axiom,(
% 38.64/5.21    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 38.64/5.21  fof(f104,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 38.64/5.21    inference(superposition,[],[f33,f36])).
% 38.64/5.21  fof(f22738,plain,(
% 38.64/5.21    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22737,f2965])).
% 38.64/5.21  fof(f2965,plain,(
% 38.64/5.21    ( ! [X6,X7,X5] : (k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5)))) = k4_xboole_0(X7,X5)) )),
% 38.64/5.21    inference(backward_demodulation,[],[f1065,f2919])).
% 38.64/5.21  fof(f2919,plain,(
% 38.64/5.21    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X2,X3)),X2) = k4_xboole_0(X4,X2)) )),
% 38.64/5.21    inference(superposition,[],[f40,f373])).
% 38.64/5.21  fof(f373,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1) )),
% 38.64/5.21    inference(superposition,[],[f352,f33])).
% 38.64/5.21  fof(f352,plain,(
% 38.64/5.21    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 38.64/5.21    inference(superposition,[],[f342,f285])).
% 38.64/5.21  fof(f1065,plain,(
% 38.64/5.21    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,X5))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1025,f880])).
% 38.64/5.21  fof(f880,plain,(
% 38.64/5.21    ( ! [X10,X8,X9] : (k5_xboole_0(X10,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k5_xboole_0(X8,k5_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 38.64/5.21    inference(superposition,[],[f369,f33])).
% 38.64/5.21  fof(f369,plain,(
% 38.64/5.21    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f361,f29])).
% 38.64/5.21  fof(f361,plain,(
% 38.64/5.21    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 38.64/5.21    inference(superposition,[],[f29,f342])).
% 38.64/5.21  fof(f1025,plain,(
% 38.64/5.21    ( ! [X6,X7,X5] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X5,X6)),X5) = k4_xboole_0(X7,k5_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))))) )),
% 38.64/5.21    inference(superposition,[],[f40,f36])).
% 38.64/5.21  fof(f22737,plain,(
% 38.64/5.21    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) = k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22436,f21])).
% 38.64/5.21  fof(f22436,plain,(
% 38.64/5.21    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))))) = k4_xboole_0(k5_xboole_0(X6,k5_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))),k1_xboole_0)) )),
% 38.64/5.21    inference(superposition,[],[f36,f18092])).
% 38.64/5.21  fof(f18092,plain,(
% 38.64/5.21    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X4,X3),k4_xboole_0(X3,X4))),X4)) )),
% 38.64/5.21    inference(superposition,[],[f2965,f112])).
% 38.64/5.21  fof(f36,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 38.64/5.21    inference(definition_unfolding,[],[f23,f25,f25])).
% 38.64/5.21  fof(f23,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 38.64/5.21    inference(cnf_transformation,[],[f1])).
% 38.64/5.21  fof(f1,axiom,(
% 38.64/5.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 38.64/5.21  fof(f48742,plain,(
% 38.64/5.21    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0))),
% 38.64/5.21    inference(forward_demodulation,[],[f48741,f29213])).
% 38.64/5.21  fof(f48741,plain,(
% 38.64/5.21    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK0)) != k4_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK0,sK1))),
% 38.64/5.21    inference(backward_demodulation,[],[f406,f48740])).
% 38.64/5.21  fof(f48740,plain,(
% 38.64/5.21    ( ! [X267,X268] : (k5_xboole_0(X267,X268) = k4_xboole_0(k5_xboole_0(X268,k4_xboole_0(X267,X268)),k4_xboole_0(X268,k4_xboole_0(X268,X267)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f48448,f48622])).
% 38.64/5.21  fof(f48622,plain,(
% 38.64/5.21    ( ! [X41,X42] : (k4_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(X42,k5_xboole_0(X41,X42))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f48621,f138])).
% 38.64/5.21  fof(f138,plain,(
% 38.64/5.21    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 38.64/5.21    inference(superposition,[],[f33,f37])).
% 38.64/5.21  fof(f37,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 38.64/5.21    inference(definition_unfolding,[],[f27,f25])).
% 38.64/5.21  fof(f27,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 38.64/5.21    inference(cnf_transformation,[],[f8])).
% 38.64/5.21  fof(f8,axiom,(
% 38.64/5.21    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 38.64/5.21  fof(f48621,plain,(
% 38.64/5.21    ( ! [X41,X42] : (k5_xboole_0(X42,k4_xboole_0(X42,X41)) = k4_xboole_0(X42,k5_xboole_0(X41,X42))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f48367,f45608])).
% 38.64/5.21  fof(f45608,plain,(
% 38.64/5.21    ( ! [X111,X112] : (k4_xboole_0(X112,X111) = k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f45604,f114])).
% 38.64/5.21  fof(f45604,plain,(
% 38.64/5.21    ( ! [X111,X112] : (k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k1_xboole_0)) )),
% 38.64/5.21    inference(backward_demodulation,[],[f33325,f45338])).
% 38.64/5.21  fof(f45338,plain,(
% 38.64/5.21    ( ! [X118,X117] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X117,X118),k5_xboole_0(X117,X118))) )),
% 38.64/5.21    inference(superposition,[],[f45226,f353])).
% 38.64/5.21  fof(f353,plain,(
% 38.64/5.21    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 38.64/5.21    inference(superposition,[],[f342,f342])).
% 38.64/5.21  fof(f45226,plain,(
% 38.64/5.21    ( ! [X31,X32] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f45039,f72])).
% 38.64/5.21  fof(f45039,plain,(
% 38.64/5.21    ( ! [X31,X32] : (k4_xboole_0(k1_xboole_0,X32) = k4_xboole_0(k4_xboole_0(X31,k5_xboole_0(X32,X31)),X32)) )),
% 38.64/5.21    inference(superposition,[],[f2963,f23310])).
% 38.64/5.21  fof(f23310,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(X10,X9)),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(backward_demodulation,[],[f22631,f23014])).
% 38.64/5.21  fof(f23014,plain,(
% 38.64/5.21    ( ! [X33,X32] : (k5_xboole_0(X32,X33) = k5_xboole_0(k4_xboole_0(X32,X33),k4_xboole_0(X33,X32))) )),
% 38.64/5.21    inference(superposition,[],[f927,f22739])).
% 38.64/5.21  fof(f927,plain,(
% 38.64/5.21    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(X13,k5_xboole_0(X14,X12)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f900,f29])).
% 38.64/5.21  fof(f900,plain,(
% 38.64/5.21    ( ! [X14,X12,X13] : (k5_xboole_0(X12,X14) = k5_xboole_0(X13,k5_xboole_0(k5_xboole_0(X13,X14),X12))) )),
% 38.64/5.21    inference(superposition,[],[f369,f360])).
% 38.64/5.21  fof(f360,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 38.64/5.21    inference(superposition,[],[f285,f342])).
% 38.64/5.21  fof(f22631,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22630,f13581])).
% 38.64/5.21  fof(f13581,plain,(
% 38.64/5.21    ( ! [X101,X99,X100] : (k5_xboole_0(k4_xboole_0(X99,X100),k4_xboole_0(X99,k4_xboole_0(X100,X101))) = k4_xboole_0(X99,k5_xboole_0(k4_xboole_0(X100,X101),k4_xboole_0(X99,X100)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f13503,f1430])).
% 38.64/5.21  fof(f1430,plain,(
% 38.64/5.21    ( ! [X35,X33,X36,X34] : (k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X34,X35)),k4_xboole_0(X33,X34)) = k4_xboole_0(X36,k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34)))) )),
% 38.64/5.21    inference(superposition,[],[f40,f1076])).
% 38.64/5.21  fof(f1076,plain,(
% 38.64/5.21    ( ! [X26,X27,X25] : (k4_xboole_0(X27,X25) = k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1032,f114])).
% 38.64/5.21  fof(f1032,plain,(
% 38.64/5.21    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X27,X25),k4_xboole_0(X25,X26)) = k4_xboole_0(X27,k5_xboole_0(X25,k1_xboole_0))) )),
% 38.64/5.21    inference(superposition,[],[f40,f459])).
% 38.64/5.21  fof(f459,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f458,f155])).
% 38.64/5.21  fof(f458,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f438,f134])).
% 38.64/5.21  fof(f134,plain,(
% 38.64/5.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 38.64/5.21    inference(superposition,[],[f37,f36])).
% 38.64/5.21  fof(f438,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 38.64/5.21    inference(superposition,[],[f104,f36])).
% 38.64/5.21  fof(f13503,plain,(
% 38.64/5.21    ( ! [X101,X99,X100] : (k4_xboole_0(k4_xboole_0(X99,k4_xboole_0(X100,X101)),k4_xboole_0(X99,X100)) = k5_xboole_0(k4_xboole_0(X99,X100),k4_xboole_0(X99,k4_xboole_0(X100,X101)))) )),
% 38.64/5.21    inference(superposition,[],[f390,f2919])).
% 38.64/5.21  fof(f390,plain,(
% 38.64/5.21    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 38.64/5.21    inference(superposition,[],[f353,f33])).
% 38.64/5.21  fof(f22630,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X10,X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22629,f883])).
% 38.64/5.21  fof(f883,plain,(
% 38.64/5.21    ( ! [X19,X17,X18] : (k5_xboole_0(X19,k4_xboole_0(X17,X18)) = k5_xboole_0(X17,k5_xboole_0(X19,k4_xboole_0(X17,k4_xboole_0(X17,X18))))) )),
% 38.64/5.21    inference(superposition,[],[f369,f138])).
% 38.64/5.21  fof(f22629,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,X9))))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22628,f38])).
% 38.64/5.21  fof(f38,plain,(
% 38.64/5.21    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 38.64/5.21    inference(definition_unfolding,[],[f30,f25,f25])).
% 38.64/5.21  fof(f30,plain,(
% 38.64/5.21    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 38.64/5.21    inference(cnf_transformation,[],[f10])).
% 38.64/5.21  fof(f10,axiom,(
% 38.64/5.21    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 38.64/5.21  fof(f22628,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f22390,f3054])).
% 38.64/5.21  fof(f3054,plain,(
% 38.64/5.21    ( ! [X64,X65,X63] : (k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(X65,k5_xboole_0(X64,X63))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f3000,f114])).
% 38.64/5.21  fof(f3000,plain,(
% 38.64/5.21    ( ! [X64,X65,X63] : (k5_xboole_0(X65,k5_xboole_0(X63,X64)) = k5_xboole_0(k5_xboole_0(X65,k1_xboole_0),k5_xboole_0(X64,X63))) )),
% 38.64/5.21    inference(superposition,[],[f379,f2087])).
% 38.64/5.21  fof(f2087,plain,(
% 38.64/5.21    ( ! [X26,X25] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X25,X26),k5_xboole_0(X26,X25))) )),
% 38.64/5.21    inference(superposition,[],[f342,f1942])).
% 38.64/5.21  fof(f379,plain,(
% 38.64/5.21    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11)) )),
% 38.64/5.21    inference(superposition,[],[f352,f29])).
% 38.64/5.21  fof(f22390,plain,(
% 38.64/5.21    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),X9),k4_xboole_0(X9,X10))),k4_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 38.64/5.21    inference(superposition,[],[f18092,f37])).
% 38.64/5.21  fof(f2963,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,X14)) )),
% 38.64/5.21    inference(backward_demodulation,[],[f1071,f2919])).
% 38.64/5.21  fof(f1071,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X14,X15)),X14)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1070,f1065])).
% 38.64/5.21  fof(f1070,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X14))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1069,f880])).
% 38.64/5.21  fof(f1069,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,k4_xboole_0(X15,X14))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1028,f360])).
% 38.64/5.21  fof(f1028,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X15,k4_xboole_0(X15,X14))),X14) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),k4_xboole_0(X14,X15)))) )),
% 38.64/5.21    inference(superposition,[],[f40,f134])).
% 38.64/5.21  fof(f33325,plain,(
% 38.64/5.21    ( ! [X111,X112] : (k4_xboole_0(k5_xboole_0(X111,X112),k4_xboole_0(X111,X112)) = k5_xboole_0(k4_xboole_0(X112,X111),k4_xboole_0(k4_xboole_0(X111,X112),k5_xboole_0(X111,X112)))) )),
% 38.64/5.21    inference(superposition,[],[f26323,f23512])).
% 38.64/5.21  fof(f26323,plain,(
% 38.64/5.21    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k5_xboole_0(X16,X15),k4_xboole_0(X16,X15))) )),
% 38.64/5.21    inference(superposition,[],[f688,f23006])).
% 38.64/5.21  fof(f23006,plain,(
% 38.64/5.21    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k5_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8)))) )),
% 38.64/5.21    inference(superposition,[],[f395,f22739])).
% 38.64/5.21  fof(f395,plain,(
% 38.64/5.21    ( ! [X10,X11,X9] : (k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),k5_xboole_0(X9,X10)) = X11) )),
% 38.64/5.21    inference(superposition,[],[f353,f29])).
% 38.64/5.21  fof(f688,plain,(
% 38.64/5.21    ( ! [X4,X2,X3] : (k5_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k5_xboole_0(X3,X4))) = X4) )),
% 38.64/5.21    inference(superposition,[],[f300,f360])).
% 38.64/5.21  fof(f48367,plain,(
% 38.64/5.21    ( ! [X41,X42] : (k4_xboole_0(X42,k5_xboole_0(X41,X42)) = k5_xboole_0(X42,k4_xboole_0(k5_xboole_0(X41,X42),k4_xboole_0(X41,X42)))) )),
% 38.64/5.21    inference(superposition,[],[f104,f45739])).
% 38.64/5.21  fof(f45739,plain,(
% 38.64/5.21    ( ! [X33,X34] : (k4_xboole_0(X34,X33) = k4_xboole_0(k5_xboole_0(X34,X33),X33)) )),
% 38.64/5.21    inference(backward_demodulation,[],[f28152,f45738])).
% 38.64/5.21  fof(f45738,plain,(
% 38.64/5.21    ( ! [X241,X242] : (k4_xboole_0(X242,X241) = k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f45737,f134])).
% 38.64/5.21  fof(f45737,plain,(
% 38.64/5.21    ( ! [X241,X242] : (k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k4_xboole_0(X242,k4_xboole_0(X241,k4_xboole_0(X241,X242)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f45736,f23309])).
% 38.64/5.21  fof(f23309,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(X15,X14)))) )),
% 38.64/5.21    inference(backward_demodulation,[],[f18272,f23014])).
% 38.64/5.21  fof(f18272,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k4_xboole_0(X14,k5_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X15))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f18271,f13581])).
% 38.64/5.21  fof(f18271,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X14))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f18270,f883])).
% 38.64/5.21  fof(f18270,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X14))))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f18269,f38])).
% 38.64/5.21  fof(f18269,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14))))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f18057,f3054])).
% 38.64/5.21  fof(f18057,plain,(
% 38.64/5.21    ( ! [X14,X15,X16] : (k4_xboole_0(X16,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(X16,k5_xboole_0(X14,k5_xboole_0(k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X14),k4_xboole_0(X14,X15))))) )),
% 38.64/5.21    inference(superposition,[],[f2965,f37])).
% 38.64/5.21  fof(f45736,plain,(
% 38.64/5.21    ( ! [X241,X242] : (k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k4_xboole_0(X242,k4_xboole_0(X241,k5_xboole_0(X242,X241)))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f45464,f283])).
% 38.64/5.21  fof(f45464,plain,(
% 38.64/5.21    ( ! [X241,X242] : (k5_xboole_0(k4_xboole_0(X241,k5_xboole_0(X242,X241)),X242) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X242,k4_xboole_0(X241,k5_xboole_0(X242,X241))))) )),
% 38.64/5.21    inference(superposition,[],[f23014,f45226])).
% 38.64/5.21  fof(f28152,plain,(
% 38.64/5.21    ( ! [X33,X34] : (k4_xboole_0(k5_xboole_0(X34,X33),X33) = k5_xboole_0(k4_xboole_0(X33,k5_xboole_0(X34,X33)),X34)) )),
% 38.64/5.21    inference(superposition,[],[f23512,f342])).
% 38.64/5.21  fof(f48448,plain,(
% 38.64/5.21    ( ! [X267,X268] : (k5_xboole_0(X267,X268) = k4_xboole_0(k5_xboole_0(X268,k4_xboole_0(X267,X268)),k4_xboole_0(X268,k5_xboole_0(X267,X268)))) )),
% 38.64/5.21    inference(superposition,[],[f28459,f45739])).
% 38.64/5.21  fof(f28459,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = X106) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28458,f114])).
% 38.64/5.21  fof(f28458,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k5_xboole_0(X106,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28457,f459])).
% 38.64/5.21  fof(f28457,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(X106,k4_xboole_0(k4_xboole_0(X105,X106),X105))) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28456,f360])).
% 38.64/5.21  fof(f28456,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28455,f1535])).
% 38.64/5.21  fof(f1535,plain,(
% 38.64/5.21    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(X27,X26),X28) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1534,f114])).
% 38.64/5.21  fof(f1534,plain,(
% 38.64/5.21    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k1_xboole_0)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f1508,f112])).
% 38.64/5.21  fof(f1508,plain,(
% 38.64/5.21    ( ! [X28,X26,X27] : (k4_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),X26) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X27,X26),X28),k4_xboole_0(X26,X26))) )),
% 38.64/5.21    inference(superposition,[],[f104,f1387])).
% 38.64/5.21  fof(f1387,plain,(
% 38.64/5.21    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X18,X17),X19)) = X17) )),
% 38.64/5.21    inference(superposition,[],[f1076,f1132])).
% 38.64/5.21  fof(f28455,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),X105),X106),X106)) )),
% 38.64/5.21    inference(forward_demodulation,[],[f28182,f40])).
% 38.64/5.21  fof(f28182,plain,(
% 38.64/5.21    ( ! [X105,X106] : (k4_xboole_0(k5_xboole_0(X105,k4_xboole_0(X106,X105)),k4_xboole_0(X105,X106)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X105,X106),k5_xboole_0(X105,k4_xboole_0(X106,X105))),X106)) )),
% 38.64/5.21    inference(superposition,[],[f23512,f23549])).
% 38.64/5.21  fof(f23549,plain,(
% 38.64/5.21    ( ! [X35,X36] : (k5_xboole_0(k4_xboole_0(X35,X36),k5_xboole_0(X35,k4_xboole_0(X36,X35))) = X36) )),
% 38.64/5.21    inference(superposition,[],[f353,f23002])).
% 38.64/5.21  fof(f406,plain,(
% 38.64/5.21    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))),
% 38.64/5.21    inference(unit_resulting_resolution,[],[f34,f28])).
% 38.64/5.21  fof(f34,plain,(
% 38.64/5.21    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 38.64/5.21    inference(definition_unfolding,[],[f20,f24,f25])).
% 38.64/5.21  fof(f20,plain,(
% 38.64/5.21    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 38.64/5.21    inference(cnf_transformation,[],[f19])).
% 38.64/5.21  fof(f19,plain,(
% 38.64/5.21    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 38.64/5.21    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 38.64/5.21  fof(f18,plain,(
% 38.64/5.21    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 38.64/5.21    introduced(choice_axiom,[])).
% 38.64/5.21  fof(f16,plain,(
% 38.64/5.21    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 38.64/5.21    inference(ennf_transformation,[],[f14])).
% 38.64/5.21  fof(f14,negated_conjecture,(
% 38.64/5.21    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 38.64/5.21    inference(negated_conjecture,[],[f13])).
% 38.64/5.21  fof(f13,conjecture,(
% 38.64/5.21    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 38.64/5.21    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 38.64/5.21  % SZS output end Proof for theBenchmark
% 38.64/5.21  % (14692)------------------------------
% 38.64/5.21  % (14692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.64/5.21  % (14692)Termination reason: Refutation
% 38.64/5.21  
% 38.64/5.21  % (14692)Memory used [KB]: 79828
% 38.64/5.21  % (14692)Time elapsed: 4.504 s
% 38.64/5.21  % (14692)------------------------------
% 38.64/5.21  % (14692)------------------------------
% 38.64/5.22  % (14630)Success in time 4.855 s
%------------------------------------------------------------------------------
