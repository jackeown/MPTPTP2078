%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:33 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 480 expanded)
%              Number of leaves         :   11 ( 160 expanded)
%              Depth                    :   26
%              Number of atoms          :  106 ( 599 expanded)
%              Number of equality atoms :   62 ( 411 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3257,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3255,f18])).

fof(f18,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f3255,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f3225,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f3225,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(trivial_inequality_removal,[],[f3207])).

fof(f3207,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f31,f3198])).

fof(f3198,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f3196,f427])).

fof(f427,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(forward_demodulation,[],[f351,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f22,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f351,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(superposition,[],[f34,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f28,f22,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f3196,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(resolution,[],[f3148,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3148,plain,(
    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f2595,f753])).

fof(f753,plain,(
    ! [X6] : k4_xboole_0(sK0,X6) = k4_xboole_0(sK0,k4_xboole_0(X6,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f727,f30])).

fof(f727,plain,(
    ! [X6] : k4_xboole_0(sK0,k4_xboole_0(X6,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X6))) ),
    inference(superposition,[],[f30,f462])).

fof(f462,plain,(
    ! [X24] : k4_xboole_0(sK0,k4_xboole_0(sK0,X24)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f461,f439])).

fof(f439,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X7,X9)) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7)))) ),
    inference(forward_demodulation,[],[f438,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f438,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7)))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f357,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f29,f20])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f22])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f357,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7)))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k4_xboole_0(X7,X7)) ),
    inference(superposition,[],[f34,f125])).

fof(f125,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f106,f20])).

fof(f106,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f30,f51])).

fof(f51,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f461,plain,(
    ! [X24] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f363,f33])).

fof(f363,plain,(
    ! [X24] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X24)),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f34,f131])).

fof(f131,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f109,f20])).

fof(f109,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f30,f55])).

fof(f55,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2595,plain,(
    ! [X4,X5] : r1_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(X4,X5))))) ),
    inference(forward_demodulation,[],[f2594,f521])).

fof(f521,plain,(
    ! [X13] : k4_xboole_0(sK0,X13) = k4_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f125,f333])).

fof(f333,plain,(
    ! [X2] : k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X2)) ),
    inference(forward_demodulation,[],[f314,f20])).

fof(f314,plain,(
    ! [X2] : k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f30,f220])).

fof(f220,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) ),
    inference(forward_demodulation,[],[f219,f128])).

fof(f128,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f107,f20])).

fof(f107,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f30,f52])).

fof(f52,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3)) ),
    inference(resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f21,f35])).

fof(f219,plain,(
    ! [X12] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k1_xboole_0,X12) ),
    inference(forward_demodulation,[],[f184,f35])).

fof(f184,plain,(
    ! [X12] : k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X12) ),
    inference(superposition,[],[f33,f129])).

fof(f129,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f108,f20])).

fof(f108,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f30,f54])).

fof(f54,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(resolution,[],[f24,f17])).

fof(f2594,plain,(
    ! [X4,X5] : r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(X4,X5))))) ),
    inference(forward_demodulation,[],[f2593,f390])).

fof(f390,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6))))) ),
    inference(forward_demodulation,[],[f389,f33])).

fof(f389,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6))))) ),
    inference(forward_demodulation,[],[f388,f188])).

fof(f388,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6))))) ),
    inference(forward_demodulation,[],[f342,f33])).

fof(f342,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6))) = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,X6))) ),
    inference(superposition,[],[f34,f30])).

fof(f2593,plain,(
    ! [X4,X5] : r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,X5))))))) ),
    inference(forward_demodulation,[],[f2567,f33])).

fof(f2567,plain,(
    ! [X4,X5] : r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X4)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,X5))))) ),
    inference(superposition,[],[f2090,f34])).

fof(f2090,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,sK2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK0,X2)))) ),
    inference(resolution,[],[f1425,f24])).

fof(f1425,plain,(
    ! [X30,X31] : r1_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(sK0,X30))),k4_xboole_0(X30,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f199,f792])).

fof(f792,plain,(
    ! [X19] : k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(X19,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f156,f753])).

fof(f156,plain,(
    ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    inference(superposition,[],[f125,f125])).

fof(f199,plain,(
    ! [X6,X4,X5] : r1_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))),X6) ),
    inference(superposition,[],[f21,f33])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:20:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (30057)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (30056)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (30066)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (30058)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (30065)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (30059)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (30062)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (30054)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (30064)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (30067)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (30061)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (30068)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (30053)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (30060)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (30055)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.52  % (30063)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (30069)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (30070)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.55/0.56  % (30066)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f3257,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(subsumption_resolution,[],[f3255,f18])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f12,plain,(
% 1.55/0.56    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.55/0.56    inference(ennf_transformation,[],[f11])).
% 1.55/0.56  fof(f11,negated_conjecture,(
% 1.55/0.56    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.55/0.56    inference(negated_conjecture,[],[f10])).
% 1.55/0.56  fof(f10,conjecture,(
% 1.55/0.56    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.55/0.56  fof(f3255,plain,(
% 1.55/0.56    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.55/0.56    inference(resolution,[],[f3225,f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f13])).
% 1.55/0.56  fof(f13,plain,(
% 1.55/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.55/0.56    inference(ennf_transformation,[],[f2])).
% 1.55/0.56  fof(f2,axiom,(
% 1.55/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.55/0.56  fof(f3225,plain,(
% 1.55/0.56    r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f3207])).
% 1.55/0.56  fof(f3207,plain,(
% 1.55/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)),
% 1.55/0.56    inference(superposition,[],[f31,f3198])).
% 1.55/0.56  fof(f3198,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),sK1))),
% 1.55/0.56    inference(forward_demodulation,[],[f3196,f427])).
% 1.55/0.56  fof(f427,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f351,f188])).
% 1.55/0.56  fof(f188,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 1.55/0.56    inference(superposition,[],[f33,f30])).
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.55/0.56    inference(definition_unfolding,[],[f23,f22])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.55/0.56  fof(f23,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.55/0.56  fof(f33,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.55/0.56    inference(definition_unfolding,[],[f27,f22,f22])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.55/0.56  fof(f351,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.55/0.56    inference(superposition,[],[f34,f30])).
% 1.55/0.56  fof(f34,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.55/0.56    inference(definition_unfolding,[],[f28,f22,f22,f22])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.55/0.56  fof(f3196,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.55/0.56    inference(resolution,[],[f3148,f32])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.56    inference(definition_unfolding,[],[f25,f22])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f16])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.55/0.56    inference(nnf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.56  fof(f3148,plain,(
% 1.55/0.56    r1_xboole_0(k4_xboole_0(sK0,sK2),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.55/0.56    inference(superposition,[],[f2595,f753])).
% 1.55/0.56  fof(f753,plain,(
% 1.55/0.56    ( ! [X6] : (k4_xboole_0(sK0,X6) = k4_xboole_0(sK0,k4_xboole_0(X6,k4_xboole_0(sK1,sK2)))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f727,f30])).
% 1.55/0.56  fof(f727,plain,(
% 1.55/0.56    ( ! [X6] : (k4_xboole_0(sK0,k4_xboole_0(X6,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X6)))) )),
% 1.55/0.56    inference(superposition,[],[f30,f462])).
% 1.55/0.56  fof(f462,plain,(
% 1.55/0.56    ( ! [X24] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X24)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2))))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f461,f439])).
% 1.55/0.56  fof(f439,plain,(
% 1.55/0.56    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X7,X9)) = k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7))))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f438,f20])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f4])).
% 1.55/0.56  fof(f4,axiom,(
% 1.55/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.55/0.56  fof(f438,plain,(
% 1.55/0.56    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7)))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k1_xboole_0)) )),
% 1.55/0.56    inference(forward_demodulation,[],[f357,f35])).
% 1.55/0.56  fof(f35,plain,(
% 1.55/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.55/0.56    inference(backward_demodulation,[],[f29,f20])).
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.55/0.56    inference(definition_unfolding,[],[f19,f22])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.55/0.56  fof(f357,plain,(
% 1.55/0.56    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X9,k4_xboole_0(X8,X7)))) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X9)),k4_xboole_0(X7,X7))) )),
% 1.55/0.56    inference(superposition,[],[f34,f125])).
% 1.55/0.56  fof(f125,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.55/0.56    inference(forward_demodulation,[],[f106,f20])).
% 1.55/0.56  fof(f106,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.55/0.56    inference(superposition,[],[f30,f51])).
% 1.55/0.56  fof(f51,plain,(
% 1.55/0.56    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 1.55/0.56    inference(resolution,[],[f32,f40])).
% 1.55/0.56  fof(f40,plain,(
% 1.55/0.56    ( ! [X2,X3] : (r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 1.55/0.56    inference(resolution,[],[f24,f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f9])).
% 1.55/0.56  fof(f9,axiom,(
% 1.55/0.56    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.55/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.55/0.56  fof(f461,plain,(
% 1.55/0.56    ( ! [X24] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK0,sK0))))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f363,f33])).
% 1.55/0.56  fof(f363,plain,(
% 1.55/0.56    ( ! [X24] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X24,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X24)),k4_xboole_0(sK0,sK0))) )),
% 1.55/0.56    inference(superposition,[],[f34,f131])).
% 1.55/0.56  fof(f131,plain,(
% 1.55/0.56    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.56    inference(forward_demodulation,[],[f109,f20])).
% 1.55/0.56  fof(f109,plain,(
% 1.55/0.56    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.55/0.56    inference(superposition,[],[f30,f55])).
% 1.55/0.56  fof(f55,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.56    inference(resolution,[],[f32,f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f2595,plain,(
% 1.55/0.56    ( ! [X4,X5] : (r1_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(X4,X5)))))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f2594,f521])).
% 1.55/0.56  fof(f521,plain,(
% 1.55/0.56    ( ! [X13] : (k4_xboole_0(sK0,X13) = k4_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK1,sK2))) )),
% 1.55/0.56    inference(superposition,[],[f125,f333])).
% 1.55/0.56  fof(f333,plain,(
% 1.55/0.56    ( ! [X2] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X2))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f314,f20])).
% 1.55/0.56  fof(f314,plain,(
% 1.55/0.56    ( ! [X2] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X2))) )),
% 1.55/0.56    inference(superposition,[],[f30,f220])).
% 1.55/0.56  fof(f220,plain,(
% 1.55/0.56    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12)))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f219,f128])).
% 1.55/0.56  fof(f128,plain,(
% 1.55/0.56    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.55/0.56    inference(forward_demodulation,[],[f107,f20])).
% 1.55/0.56  fof(f107,plain,(
% 1.55/0.56    ( ! [X4] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.55/0.56    inference(superposition,[],[f30,f52])).
% 1.55/0.56  fof(f52,plain,(
% 1.55/0.56    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X3))) )),
% 1.55/0.56    inference(resolution,[],[f32,f37])).
% 1.55/0.56  fof(f37,plain,(
% 1.55/0.56    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.55/0.56    inference(superposition,[],[f21,f35])).
% 1.55/0.56  fof(f219,plain,(
% 1.55/0.56    ( ! [X12] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k1_xboole_0,X12)) )),
% 1.55/0.56    inference(forward_demodulation,[],[f184,f35])).
% 1.55/0.56  fof(f184,plain,(
% 1.55/0.56    ( ! [X12] : (k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X12))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)),X12)) )),
% 1.55/0.56    inference(superposition,[],[f33,f129])).
% 1.55/0.56  fof(f129,plain,(
% 1.55/0.56    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.55/0.56    inference(forward_demodulation,[],[f108,f20])).
% 1.55/0.56  fof(f108,plain,(
% 1.55/0.56    k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.55/0.56    inference(superposition,[],[f30,f54])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0))),
% 1.55/0.56    inference(resolution,[],[f32,f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 1.55/0.56    inference(resolution,[],[f24,f17])).
% 1.55/0.56  fof(f2594,plain,(
% 1.55/0.56    ( ! [X4,X5] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(X4,X5)))))) )),
% 1.55/0.56    inference(forward_demodulation,[],[f2593,f390])).
% 1.55/0.57  fof(f390,plain,(
% 1.55/0.57    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6)))))) )),
% 1.55/0.57    inference(forward_demodulation,[],[f389,f33])).
% 1.55/0.57  fof(f389,plain,(
% 1.55/0.57    ( ! [X6,X4,X5] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6)))))) )),
% 1.55/0.57    inference(forward_demodulation,[],[f388,f188])).
% 1.55/0.57  fof(f388,plain,(
% 1.55/0.57    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,X6)))))) )),
% 1.55/0.57    inference(forward_demodulation,[],[f342,f33])).
% 1.55/0.57  fof(f342,plain,(
% 1.55/0.57    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),X6))) = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,X6)))) )),
% 1.55/0.57    inference(superposition,[],[f34,f30])).
% 1.55/0.57  fof(f2593,plain,(
% 1.55/0.57    ( ! [X4,X5] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,X5)))))))) )),
% 1.55/0.57    inference(forward_demodulation,[],[f2567,f33])).
% 1.55/0.57  fof(f2567,plain,(
% 1.55/0.57    ( ! [X4,X5] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(sK0,X5),k4_xboole_0(sK1,sK2)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,X4)),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X4,X5)))))) )),
% 1.55/0.57    inference(superposition,[],[f2090,f34])).
% 1.55/0.57  fof(f2090,plain,(
% 1.55/0.57    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(sK1,sK2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(sK0,X2))))) )),
% 1.55/0.57    inference(resolution,[],[f1425,f24])).
% 1.55/0.57  fof(f1425,plain,(
% 1.55/0.57    ( ! [X30,X31] : (r1_xboole_0(k4_xboole_0(X31,k4_xboole_0(X31,k4_xboole_0(sK0,X30))),k4_xboole_0(X30,k4_xboole_0(sK1,sK2)))) )),
% 1.55/0.57    inference(superposition,[],[f199,f792])).
% 1.55/0.57  fof(f792,plain,(
% 1.55/0.57    ( ! [X19] : (k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(X19,k4_xboole_0(sK1,sK2)))) )),
% 1.55/0.57    inference(superposition,[],[f156,f753])).
% 1.55/0.57  fof(f156,plain,(
% 1.55/0.57    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) )),
% 1.55/0.57    inference(superposition,[],[f125,f125])).
% 1.55/0.57  fof(f199,plain,(
% 1.55/0.57    ( ! [X6,X4,X5] : (r1_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6))),X6)) )),
% 1.55/0.57    inference(superposition,[],[f21,f33])).
% 1.55/0.57  fof(f31,plain,(
% 1.55/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.55/0.57    inference(definition_unfolding,[],[f26,f22])).
% 1.55/0.57  fof(f26,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.55/0.57    inference(cnf_transformation,[],[f16])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (30066)------------------------------
% 1.55/0.57  % (30066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (30066)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (30066)Memory used [KB]: 3070
% 1.55/0.57  % (30066)Time elapsed: 0.137 s
% 1.55/0.57  % (30066)------------------------------
% 1.55/0.57  % (30066)------------------------------
% 1.55/0.57  % (30052)Success in time 0.206 s
%------------------------------------------------------------------------------
