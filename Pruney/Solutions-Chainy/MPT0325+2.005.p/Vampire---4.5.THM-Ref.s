%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:38 EST 2020

% Result     : Theorem 31.62s
% Output     : Refutation 31.62s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 858 expanded)
%              Number of leaves         :   21 ( 279 expanded)
%              Depth                    :   31
%              Number of atoms          :  176 (1108 expanded)
%              Number of equality atoms :  136 ( 947 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14828,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13926,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f13926,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f35,f13924])).

fof(f13924,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f13885,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13885,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f35,f12811])).

fof(f12811,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f12477,f8477])).

fof(f8477,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f8246,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f8246,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f8245])).

fof(f8245,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f72,f6502])).

fof(f6502,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f6457])).

fof(f6457,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f48,f6264])).

fof(f6264,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f6263,f78])).

fof(f6263,plain,(
    k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f6262,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f6262,plain,(
    k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f6261,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f75,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f59,f40])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f57,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f6261,plain,(
    k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f6209,f118])).

fof(f6209,plain,(
    k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))) ),
    inference(superposition,[],[f5690,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f5690,plain,(
    ! [X0] : k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),X0)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) ),
    inference(backward_demodulation,[],[f724,f5688])).

fof(f5688,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f5687,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f43,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f5687,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f5686,f70])).

fof(f5686,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1) ),
    inference(forward_demodulation,[],[f5627,f967])).

fof(f967,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X9)),X8) = k2_zfmisc_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X7)),X8) ),
    inference(superposition,[],[f176,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f54,f68,f68])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f176,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1))) ),
    inference(superposition,[],[f74,f69])).

fof(f69,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f42,f67,f67])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f5627,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1) ),
    inference(superposition,[],[f1127,f176])).

fof(f1127,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0))) ),
    inference(forward_demodulation,[],[f1095,f69])).

fof(f1095,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f161,f85])).

fof(f85,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f34,f47])).

fof(f34,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f161,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k3_xboole_0(X4,X5),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X6,X7)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))) ),
    inference(superposition,[],[f73,f59])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f55,f68,f68])).

fof(f55,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f724,plain,(
    ! [X0] : k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),X0)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(X0,sK3))) ),
    inference(superposition,[],[f150,f85])).

fof(f150,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),X8)),k3_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X4,X5),X6),k2_zfmisc_1(X8,X7))) ),
    inference(forward_demodulation,[],[f141,f59])).

fof(f141,plain,(
    ! [X6,X4,X8,X7,X5] : k2_zfmisc_1(k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),X8)),k3_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(X4,X5),X8),k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f122,f59])).

fof(f122,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f76,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f59,f40])).

fof(f76,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f56,f46,f46])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f12477,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f12476])).

fof(f12476,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f72,f7726])).

fof(f7726,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f7681])).

fof(f7681,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f48,f6095])).

fof(f6095,plain,(
    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(forward_demodulation,[],[f6045,f37])).

fof(f6045,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[],[f122,f5688])).

fof(f35,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (30439)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (30431)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (30423)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (30439)Refutation not found, incomplete strategy% (30439)------------------------------
% 0.20/0.50  % (30439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30439)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (30439)Memory used [KB]: 10746
% 0.20/0.50  % (30439)Time elapsed: 0.047 s
% 0.20/0.50  % (30439)------------------------------
% 0.20/0.50  % (30439)------------------------------
% 0.20/0.50  % (30421)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (30441)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (30426)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (30420)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (30422)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (30429)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30418)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (30443)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (30433)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (30417)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (30435)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (30442)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (30438)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (30419)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30444)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (30440)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (30437)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (30424)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (30446)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (30432)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (30436)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (30425)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (30428)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (30434)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (30434)Refutation not found, incomplete strategy% (30434)------------------------------
% 0.20/0.55  % (30434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (30434)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (30434)Memory used [KB]: 10618
% 0.20/0.55  % (30434)Time elapsed: 0.139 s
% 0.20/0.55  % (30434)------------------------------
% 0.20/0.55  % (30434)------------------------------
% 0.20/0.55  % (30430)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (30427)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (30445)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.07/0.64  % (30447)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.79/0.73  % (30448)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.35/0.82  % (30422)Time limit reached!
% 3.35/0.82  % (30422)------------------------------
% 3.35/0.82  % (30422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.82  % (30422)Termination reason: Time limit
% 3.35/0.82  
% 3.35/0.82  % (30422)Memory used [KB]: 9083
% 3.35/0.82  % (30422)Time elapsed: 0.418 s
% 3.35/0.82  % (30422)------------------------------
% 3.35/0.82  % (30422)------------------------------
% 4.06/0.91  % (30418)Time limit reached!
% 4.06/0.91  % (30418)------------------------------
% 4.06/0.91  % (30418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.91  % (30418)Termination reason: Time limit
% 4.06/0.91  % (30418)Termination phase: Saturation
% 4.06/0.91  
% 4.06/0.91  % (30418)Memory used [KB]: 9850
% 4.06/0.91  % (30418)Time elapsed: 0.500 s
% 4.06/0.91  % (30418)------------------------------
% 4.06/0.91  % (30418)------------------------------
% 4.31/0.91  % (30429)Time limit reached!
% 4.31/0.91  % (30429)------------------------------
% 4.31/0.91  % (30429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.91  % (30429)Termination reason: Time limit
% 4.31/0.91  
% 4.31/0.91  % (30429)Memory used [KB]: 10746
% 4.31/0.91  % (30429)Time elapsed: 0.515 s
% 4.31/0.91  % (30429)------------------------------
% 4.31/0.91  % (30429)------------------------------
% 4.31/0.92  % (30417)Time limit reached!
% 4.31/0.92  % (30417)------------------------------
% 4.31/0.92  % (30417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.92  % (30417)Termination reason: Time limit
% 4.31/0.92  
% 4.31/0.92  % (30417)Memory used [KB]: 3837
% 4.31/0.92  % (30417)Time elapsed: 0.505 s
% 4.31/0.92  % (30417)------------------------------
% 4.31/0.92  % (30417)------------------------------
% 4.31/0.92  % (30449)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.31/0.92  % (30427)Time limit reached!
% 4.31/0.92  % (30427)------------------------------
% 4.31/0.92  % (30427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.31/0.92  % (30427)Termination reason: Time limit
% 4.31/0.92  
% 4.31/0.92  % (30427)Memory used [KB]: 16502
% 4.31/0.92  % (30427)Time elapsed: 0.524 s
% 4.31/0.92  % (30427)------------------------------
% 4.31/0.92  % (30427)------------------------------
% 5.03/1.02  % (30445)Time limit reached!
% 5.03/1.02  % (30445)------------------------------
% 5.03/1.02  % (30445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.02  % (30445)Termination reason: Time limit
% 5.03/1.02  
% 5.03/1.02  % (30445)Memory used [KB]: 9594
% 5.03/1.02  % (30445)Time elapsed: 0.615 s
% 5.03/1.02  % (30445)------------------------------
% 5.03/1.02  % (30445)------------------------------
% 5.03/1.02  % (30433)Time limit reached!
% 5.03/1.02  % (30433)------------------------------
% 5.03/1.02  % (30433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.02  % (30433)Termination reason: Time limit
% 5.03/1.02  
% 5.03/1.02  % (30433)Memory used [KB]: 16375
% 5.03/1.02  % (30433)Time elapsed: 0.614 s
% 5.03/1.02  % (30433)------------------------------
% 5.03/1.02  % (30433)------------------------------
% 5.03/1.02  % (30424)Time limit reached!
% 5.03/1.02  % (30424)------------------------------
% 5.03/1.02  % (30424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.03/1.02  % (30424)Termination reason: Time limit
% 5.03/1.02  % (30424)Termination phase: Saturation
% 5.03/1.02  
% 5.03/1.02  % (30424)Memory used [KB]: 11257
% 5.03/1.02  % (30424)Time elapsed: 0.600 s
% 5.03/1.02  % (30424)------------------------------
% 5.03/1.02  % (30424)------------------------------
% 5.03/1.03  % (30451)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.03/1.04  % (30450)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.03/1.04  % (30452)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.03/1.05  % (30453)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.52/1.15  % (30456)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.52/1.17  % (30455)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.52/1.18  % (30454)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.56/1.21  % (30438)Time limit reached!
% 6.56/1.21  % (30438)------------------------------
% 6.56/1.21  % (30438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.56/1.21  % (30438)Termination reason: Time limit
% 6.56/1.21  % (30438)Termination phase: Saturation
% 6.56/1.21  
% 6.56/1.21  % (30438)Memory used [KB]: 8315
% 6.56/1.21  % (30438)Time elapsed: 0.800 s
% 6.56/1.21  % (30438)------------------------------
% 6.56/1.21  % (30438)------------------------------
% 7.45/1.36  % (30457)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.45/1.36  % (30451)Time limit reached!
% 7.45/1.36  % (30451)------------------------------
% 7.45/1.36  % (30451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.45/1.36  % (30451)Termination reason: Time limit
% 7.45/1.36  
% 7.45/1.36  % (30451)Memory used [KB]: 13560
% 7.45/1.36  % (30451)Time elapsed: 0.404 s
% 7.45/1.36  % (30451)------------------------------
% 7.45/1.36  % (30451)------------------------------
% 7.45/1.36  % (30450)Time limit reached!
% 7.45/1.36  % (30450)------------------------------
% 7.45/1.36  % (30450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.45/1.36  % (30450)Termination reason: Time limit
% 7.45/1.36  
% 7.45/1.36  % (30450)Memory used [KB]: 8699
% 7.45/1.36  % (30450)Time elapsed: 0.425 s
% 7.45/1.36  % (30450)------------------------------
% 7.45/1.36  % (30450)------------------------------
% 8.01/1.40  % (30419)Time limit reached!
% 8.01/1.40  % (30419)------------------------------
% 8.01/1.40  % (30419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.01/1.40  % (30419)Termination reason: Time limit
% 8.01/1.40  % (30419)Termination phase: Saturation
% 8.01/1.40  
% 8.01/1.40  % (30419)Memory used [KB]: 22387
% 8.01/1.40  % (30419)Time elapsed: 1.0000 s
% 8.01/1.40  % (30419)------------------------------
% 8.01/1.40  % (30419)------------------------------
% 8.70/1.49  % (30459)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 8.70/1.49  % (30458)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.06/1.54  % (30460)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 9.68/1.65  % (30443)Time limit reached!
% 9.68/1.65  % (30443)------------------------------
% 9.68/1.65  % (30443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.68/1.65  % (30443)Termination reason: Time limit
% 9.68/1.65  
% 9.68/1.65  % (30443)Memory used [KB]: 20596
% 9.68/1.65  % (30443)Time elapsed: 1.222 s
% 9.68/1.65  % (30443)------------------------------
% 9.68/1.65  % (30443)------------------------------
% 10.55/1.70  % (30432)Time limit reached!
% 10.55/1.70  % (30432)------------------------------
% 10.55/1.70  % (30432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.55/1.70  % (30432)Termination reason: Time limit
% 10.55/1.70  % (30432)Termination phase: Saturation
% 10.55/1.70  
% 10.55/1.70  % (30432)Memory used [KB]: 20596
% 10.55/1.70  % (30432)Time elapsed: 1.300 s
% 10.55/1.70  % (30432)------------------------------
% 10.55/1.70  % (30432)------------------------------
% 10.55/1.75  % (30461)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.55/1.77  % (30441)Time limit reached!
% 10.55/1.77  % (30441)------------------------------
% 10.55/1.77  % (30441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.55/1.77  % (30441)Termination reason: Time limit
% 10.55/1.77  
% 10.55/1.77  % (30441)Memory used [KB]: 21620
% 10.55/1.77  % (30441)Time elapsed: 1.342 s
% 10.55/1.77  % (30441)------------------------------
% 10.55/1.77  % (30441)------------------------------
% 11.60/1.84  % (30462)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.60/1.90  % (30463)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.60/1.91  % (30459)Time limit reached!
% 11.60/1.91  % (30459)------------------------------
% 11.60/1.91  % (30459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.60/1.91  % (30459)Termination reason: Time limit
% 11.60/1.91  
% 11.60/1.91  % (30459)Memory used [KB]: 4733
% 11.60/1.91  % (30459)Time elapsed: 0.510 s
% 11.60/1.91  % (30459)------------------------------
% 11.60/1.91  % (30459)------------------------------
% 12.33/1.93  % (30444)Time limit reached!
% 12.33/1.93  % (30444)------------------------------
% 12.33/1.93  % (30444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.33/1.93  % (30444)Termination reason: Time limit
% 12.33/1.93  
% 12.33/1.93  % (30444)Memory used [KB]: 18933
% 12.33/1.93  % (30444)Time elapsed: 1.518 s
% 12.33/1.93  % (30444)------------------------------
% 12.33/1.93  % (30444)------------------------------
% 12.33/1.93  % (30421)Time limit reached!
% 12.33/1.93  % (30421)------------------------------
% 12.33/1.93  % (30421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.33/1.95  % (30421)Termination reason: Time limit
% 12.33/1.95  
% 12.33/1.95  % (30421)Memory used [KB]: 15863
% 12.33/1.95  % (30421)Time elapsed: 1.524 s
% 12.33/1.95  % (30421)------------------------------
% 12.33/1.95  % (30421)------------------------------
% 12.88/2.02  % (30428)Time limit reached!
% 12.88/2.02  % (30428)------------------------------
% 12.88/2.02  % (30428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.03  % (30465)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.88/2.03  % (30428)Termination reason: Time limit
% 12.88/2.03  
% 12.88/2.03  % (30428)Memory used [KB]: 20340
% 12.88/2.03  % (30428)Time elapsed: 1.614 s
% 12.88/2.03  % (30428)------------------------------
% 12.88/2.03  % (30428)------------------------------
% 12.88/2.03  % (30464)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 13.62/2.10  % (30466)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 13.72/2.17  % (30453)Time limit reached!
% 13.72/2.17  % (30453)------------------------------
% 13.72/2.17  % (30453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.72/2.17  % (30453)Termination reason: Time limit
% 13.72/2.17  
% 13.72/2.17  % (30453)Memory used [KB]: 11385
% 13.72/2.17  % (30453)Time elapsed: 1.216 s
% 13.72/2.17  % (30453)------------------------------
% 13.72/2.17  % (30453)------------------------------
% 13.72/2.17  % (30467)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 13.72/2.20  % (30463)Time limit reached!
% 13.72/2.20  % (30463)------------------------------
% 13.72/2.20  % (30463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.72/2.20  % (30463)Termination reason: Time limit
% 13.72/2.20  % (30463)Termination phase: Saturation
% 13.72/2.20  
% 13.72/2.20  % (30463)Memory used [KB]: 4093
% 13.72/2.20  % (30463)Time elapsed: 0.400 s
% 13.72/2.20  % (30463)------------------------------
% 13.72/2.20  % (30463)------------------------------
% 14.47/2.28  % (30468)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.49/2.31  % (30431)Time limit reached!
% 15.49/2.31  % (30431)------------------------------
% 15.49/2.31  % (30431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.49/2.31  % (30431)Termination reason: Time limit
% 15.49/2.31  
% 15.49/2.31  % (30431)Memory used [KB]: 6012
% 15.49/2.31  % (30431)Time elapsed: 1.843 s
% 15.49/2.31  % (30431)------------------------------
% 15.49/2.31  % (30431)------------------------------
% 15.49/2.35  % (30469)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 16.31/2.42  % (30466)Time limit reached!
% 16.31/2.42  % (30466)------------------------------
% 16.31/2.42  % (30466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.42  % (30466)Termination reason: Time limit
% 16.31/2.42  % (30466)Termination phase: Saturation
% 16.31/2.42  
% 16.31/2.42  % (30466)Memory used [KB]: 3326
% 16.31/2.42  % (30466)Time elapsed: 0.400 s
% 16.31/2.42  % (30466)------------------------------
% 16.31/2.42  % (30466)------------------------------
% 16.31/2.46  % (30423)Time limit reached!
% 16.31/2.46  % (30423)------------------------------
% 16.31/2.46  % (30423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.47  % (30435)Time limit reached!
% 16.31/2.47  % (30435)------------------------------
% 16.31/2.47  % (30435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.31/2.47  % (30435)Termination reason: Time limit
% 16.31/2.47  % (30435)Termination phase: Saturation
% 16.31/2.47  
% 16.31/2.47  % (30435)Memory used [KB]: 18549
% 16.31/2.47  % (30435)Time elapsed: 2.0000 s
% 16.31/2.47  % (30435)------------------------------
% 16.31/2.47  % (30435)------------------------------
% 16.31/2.47  % (30423)Termination reason: Time limit
% 16.31/2.47  
% 16.31/2.47  % (30423)Memory used [KB]: 24946
% 16.31/2.47  % (30423)Time elapsed: 2.026 s
% 16.31/2.47  % (30423)------------------------------
% 16.31/2.47  % (30423)------------------------------
% 16.31/2.47  % (30470)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 17.07/2.57  % (30471)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.07/2.57  % (30449)Time limit reached!
% 17.07/2.57  % (30449)------------------------------
% 17.07/2.57  % (30449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.07/2.57  % (30449)Termination reason: Time limit
% 17.07/2.57  
% 17.07/2.57  % (30449)Memory used [KB]: 22131
% 17.07/2.57  % (30449)Time elapsed: 1.713 s
% 17.07/2.57  % (30449)------------------------------
% 17.07/2.57  % (30449)------------------------------
% 17.67/2.62  % (30473)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.67/2.63  % (30472)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 18.43/2.72  % (30474)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 19.54/2.85  % (30455)Time limit reached!
% 19.54/2.85  % (30455)------------------------------
% 19.54/2.85  % (30455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.54/2.86  % (30455)Termination reason: Time limit
% 19.54/2.86  
% 19.54/2.86  % (30455)Memory used [KB]: 19189
% 19.54/2.86  % (30455)Time elapsed: 1.735 s
% 19.54/2.86  % (30455)------------------------------
% 19.54/2.86  % (30455)------------------------------
% 19.54/2.88  % (30471)Time limit reached!
% 19.54/2.88  % (30471)------------------------------
% 19.54/2.88  % (30471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.54/2.88  % (30471)Termination reason: Time limit
% 19.54/2.88  
% 19.54/2.88  % (30471)Memory used [KB]: 11257
% 19.54/2.88  % (30471)Time elapsed: 0.427 s
% 19.54/2.88  % (30471)------------------------------
% 19.54/2.88  % (30471)------------------------------
% 20.22/2.94  % (30473)Time limit reached!
% 20.22/2.94  % (30473)------------------------------
% 20.22/2.94  % (30473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.22/2.94  % (30473)Termination reason: Time limit
% 20.22/2.94  
% 20.22/2.94  % (30473)Memory used [KB]: 11257
% 20.22/2.94  % (30473)Time elapsed: 0.428 s
% 20.22/2.94  % (30473)------------------------------
% 20.22/2.94  % (30473)------------------------------
% 20.22/2.96  % (30462)Time limit reached!
% 20.22/2.96  % (30462)------------------------------
% 20.22/2.96  % (30462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.22/2.96  % (30462)Termination reason: Time limit
% 20.22/2.96  
% 20.22/2.96  % (30462)Memory used [KB]: 15479
% 20.22/2.96  % (30462)Time elapsed: 1.218 s
% 20.22/2.96  % (30462)------------------------------
% 20.22/2.96  % (30462)------------------------------
% 20.98/3.02  % (30436)Time limit reached!
% 20.98/3.02  % (30436)------------------------------
% 20.98/3.02  % (30436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.98/3.02  % (30436)Termination reason: Time limit
% 20.98/3.02  
% 20.98/3.02  % (30436)Memory used [KB]: 51683
% 20.98/3.02  % (30436)Time elapsed: 2.613 s
% 20.98/3.02  % (30436)------------------------------
% 20.98/3.02  % (30436)------------------------------
% 20.98/3.09  % (30425)Time limit reached!
% 20.98/3.09  % (30425)------------------------------
% 20.98/3.09  % (30425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.98/3.09  % (30425)Termination reason: Time limit
% 20.98/3.09  
% 20.98/3.09  % (30425)Memory used [KB]: 25713
% 20.98/3.09  % (30425)Time elapsed: 2.684 s
% 20.98/3.09  % (30425)------------------------------
% 20.98/3.09  % (30425)------------------------------
% 23.40/3.31  % (30465)Time limit reached!
% 23.40/3.31  % (30465)------------------------------
% 23.40/3.31  % (30465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.40/3.34  % (30465)Termination reason: Time limit
% 23.40/3.34  
% 23.40/3.34  % (30465)Memory used [KB]: 9722
% 23.40/3.34  % (30465)Time elapsed: 1.364 s
% 23.40/3.34  % (30465)------------------------------
% 23.40/3.34  % (30465)------------------------------
% 24.38/3.41  % (30430)Time limit reached!
% 24.38/3.41  % (30430)------------------------------
% 24.38/3.41  % (30430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.38/3.42  % (30448)Time limit reached!
% 24.38/3.42  % (30448)------------------------------
% 24.38/3.42  % (30448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.38/3.42  % (30448)Termination reason: Time limit
% 24.38/3.42  % (30448)Termination phase: Saturation
% 24.38/3.42  
% 24.38/3.42  % (30448)Memory used [KB]: 19061
% 24.38/3.42  % (30448)Time elapsed: 2.800 s
% 24.38/3.42  % (30448)------------------------------
% 24.38/3.42  % (30448)------------------------------
% 24.38/3.43  % (30430)Termination reason: Time limit
% 24.38/3.43  
% 24.38/3.43  % (30430)Memory used [KB]: 21875
% 24.38/3.43  % (30430)Time elapsed: 3.013 s
% 24.38/3.43  % (30430)------------------------------
% 24.38/3.43  % (30430)------------------------------
% 31.50/4.32  % (30446)Time limit reached!
% 31.50/4.32  % (30446)------------------------------
% 31.50/4.32  % (30446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.50/4.32  % (30446)Termination reason: Time limit
% 31.50/4.32  % (30446)Termination phase: Saturation
% 31.50/4.32  
% 31.50/4.32  % (30446)Memory used [KB]: 39786
% 31.50/4.32  % (30446)Time elapsed: 3.900 s
% 31.50/4.32  % (30446)------------------------------
% 31.50/4.32  % (30446)------------------------------
% 31.62/4.33  % (30468)Refutation found. Thanks to Tanya!
% 31.62/4.33  % SZS status Theorem for theBenchmark
% 31.62/4.33  % SZS output start Proof for theBenchmark
% 31.62/4.33  fof(f14828,plain,(
% 31.62/4.33    $false),
% 31.62/4.33    inference(subsumption_resolution,[],[f13926,f78])).
% 31.62/4.33  fof(f78,plain,(
% 31.62/4.33    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.62/4.33    inference(equality_resolution,[],[f49])).
% 31.62/4.33  fof(f49,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.62/4.33    inference(cnf_transformation,[],[f32])).
% 31.62/4.33  fof(f32,plain,(
% 31.62/4.33    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.62/4.33    inference(flattening,[],[f31])).
% 31.62/4.33  fof(f31,plain,(
% 31.62/4.33    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.62/4.33    inference(nnf_transformation,[],[f18])).
% 31.62/4.33  fof(f18,axiom,(
% 31.62/4.33    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 31.62/4.33  fof(f13926,plain,(
% 31.62/4.33    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 31.62/4.33    inference(backward_demodulation,[],[f35,f13924])).
% 31.62/4.33  fof(f13924,plain,(
% 31.62/4.33    k1_xboole_0 = sK0),
% 31.62/4.33    inference(subsumption_resolution,[],[f13885,f77])).
% 31.62/4.33  fof(f77,plain,(
% 31.62/4.33    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 31.62/4.33    inference(equality_resolution,[],[f50])).
% 31.62/4.33  fof(f50,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 31.62/4.33    inference(cnf_transformation,[],[f32])).
% 31.62/4.33  fof(f13885,plain,(
% 31.62/4.33    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 31.62/4.33    inference(superposition,[],[f35,f12811])).
% 31.62/4.33  fof(f12811,plain,(
% 31.62/4.33    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 31.62/4.33    inference(resolution,[],[f12477,f8477])).
% 31.62/4.33  fof(f8477,plain,(
% 31.62/4.33    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 31.62/4.33    inference(resolution,[],[f8246,f36])).
% 31.62/4.33  fof(f36,plain,(
% 31.62/4.33    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 31.62/4.33    inference(cnf_transformation,[],[f30])).
% 31.62/4.33  fof(f30,plain,(
% 31.62/4.33    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 31.62/4.33    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f29])).
% 31.62/4.33  fof(f29,plain,(
% 31.62/4.33    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 31.62/4.33    introduced(choice_axiom,[])).
% 31.62/4.33  fof(f26,plain,(
% 31.62/4.33    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 31.62/4.33    inference(flattening,[],[f25])).
% 31.62/4.33  fof(f25,plain,(
% 31.62/4.33    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 31.62/4.33    inference(ennf_transformation,[],[f23])).
% 31.62/4.33  fof(f23,negated_conjecture,(
% 31.62/4.33    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 31.62/4.33    inference(negated_conjecture,[],[f22])).
% 31.62/4.33  fof(f22,conjecture,(
% 31.62/4.33    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 31.62/4.33  fof(f8246,plain,(
% 31.62/4.33    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 31.62/4.33    inference(trivial_inequality_removal,[],[f8245])).
% 31.62/4.33  fof(f8245,plain,(
% 31.62/4.33    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 31.62/4.33    inference(superposition,[],[f72,f6502])).
% 31.62/4.33  fof(f6502,plain,(
% 31.62/4.33    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) | k1_xboole_0 = sK0),
% 31.62/4.33    inference(trivial_inequality_removal,[],[f6457])).
% 31.62/4.33  fof(f6457,plain,(
% 31.62/4.33    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))),
% 31.62/4.33    inference(superposition,[],[f48,f6264])).
% 31.62/4.33  fof(f6264,plain,(
% 31.62/4.33    k1_xboole_0 = k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)))),
% 31.62/4.33    inference(forward_demodulation,[],[f6263,f78])).
% 31.62/4.33  fof(f6263,plain,(
% 31.62/4.33    k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK1,sK3))),
% 31.62/4.33    inference(forward_demodulation,[],[f6262,f37])).
% 31.62/4.33  fof(f37,plain,(
% 31.62/4.33    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f9])).
% 31.62/4.33  fof(f9,axiom,(
% 31.62/4.33    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 31.62/4.33  fof(f6262,plain,(
% 31.62/4.33    k2_zfmisc_1(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))),
% 31.62/4.33    inference(forward_demodulation,[],[f6261,f121])).
% 31.62/4.33  fof(f121,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k3_xboole_0(X0,X1)))) )),
% 31.62/4.33    inference(backward_demodulation,[],[f75,f118])).
% 31.62/4.33  fof(f118,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 31.62/4.33    inference(superposition,[],[f59,f40])).
% 31.62/4.33  fof(f40,plain,(
% 31.62/4.33    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 31.62/4.33    inference(cnf_transformation,[],[f24])).
% 31.62/4.33  fof(f24,plain,(
% 31.62/4.33    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 31.62/4.33    inference(rectify,[],[f1])).
% 31.62/4.33  fof(f1,axiom,(
% 31.62/4.33    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 31.62/4.33  fof(f59,plain,(
% 31.62/4.33    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f20])).
% 31.62/4.33  fof(f20,axiom,(
% 31.62/4.33    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 31.62/4.33  fof(f75,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 31.62/4.33    inference(definition_unfolding,[],[f57,f46,f46])).
% 31.62/4.33  fof(f46,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f3])).
% 31.62/4.33  fof(f3,axiom,(
% 31.62/4.33    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 31.62/4.33  fof(f57,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f21])).
% 31.62/4.33  fof(f21,axiom,(
% 31.62/4.33    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 31.62/4.33  fof(f6261,plain,(
% 31.62/4.33    k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 31.62/4.33    inference(forward_demodulation,[],[f6209,f118])).
% 31.62/4.33  fof(f6209,plain,(
% 31.62/4.33    k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)))),
% 31.62/4.33    inference(superposition,[],[f5690,f86])).
% 31.62/4.33  fof(f86,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 31.62/4.33    inference(unit_resulting_resolution,[],[f41,f47])).
% 31.62/4.33  fof(f47,plain,(
% 31.62/4.33    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 31.62/4.33    inference(cnf_transformation,[],[f28])).
% 31.62/4.33  fof(f28,plain,(
% 31.62/4.33    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 31.62/4.33    inference(ennf_transformation,[],[f6])).
% 31.62/4.33  fof(f6,axiom,(
% 31.62/4.33    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 31.62/4.33  fof(f41,plain,(
% 31.62/4.33    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f4])).
% 31.62/4.33  fof(f4,axiom,(
% 31.62/4.33    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 31.62/4.33  fof(f5690,plain,(
% 31.62/4.33    ( ! [X0] : (k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),X0)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)))) )),
% 31.62/4.33    inference(backward_demodulation,[],[f724,f5688])).
% 31.62/4.33  fof(f5688,plain,(
% 31.62/4.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 31.62/4.33    inference(forward_demodulation,[],[f5687,f70])).
% 31.62/4.33  fof(f70,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 31.62/4.33    inference(definition_unfolding,[],[f43,f68])).
% 31.62/4.33  fof(f68,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 31.62/4.33    inference(definition_unfolding,[],[f45,f67])).
% 31.62/4.33  fof(f67,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f44,f66])).
% 31.62/4.33  fof(f66,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f53,f65])).
% 31.62/4.33  fof(f65,plain,(
% 31.62/4.33    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f58,f64])).
% 31.62/4.33  fof(f64,plain,(
% 31.62/4.33    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f60,f63])).
% 31.62/4.33  fof(f63,plain,(
% 31.62/4.33    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f61,f62])).
% 31.62/4.33  fof(f62,plain,(
% 31.62/4.33    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f16])).
% 31.62/4.33  fof(f16,axiom,(
% 31.62/4.33    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 31.62/4.33  fof(f61,plain,(
% 31.62/4.33    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f15])).
% 31.62/4.33  fof(f15,axiom,(
% 31.62/4.33    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 31.62/4.33  fof(f60,plain,(
% 31.62/4.33    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f14])).
% 31.62/4.33  fof(f14,axiom,(
% 31.62/4.33    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 31.62/4.33  fof(f58,plain,(
% 31.62/4.33    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f13])).
% 31.62/4.33  fof(f13,axiom,(
% 31.62/4.33    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 31.62/4.33  fof(f53,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f12])).
% 31.62/4.33  fof(f12,axiom,(
% 31.62/4.33    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 31.62/4.33  fof(f44,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f11])).
% 31.62/4.33  fof(f11,axiom,(
% 31.62/4.33    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 31.62/4.33  fof(f45,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f17])).
% 31.62/4.33  fof(f17,axiom,(
% 31.62/4.33    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 31.62/4.33  fof(f43,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 31.62/4.33    inference(cnf_transformation,[],[f5])).
% 31.62/4.33  fof(f5,axiom,(
% 31.62/4.33    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 31.62/4.33  fof(f5687,plain,(
% 31.62/4.33    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3))))),
% 31.62/4.33    inference(forward_demodulation,[],[f5686,f70])).
% 31.62/4.33  fof(f5686,plain,(
% 31.62/4.33    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k3_xboole_0(sK0,sK2))),sK1)),
% 31.62/4.33    inference(forward_demodulation,[],[f5627,f967])).
% 31.62/4.33  fof(f967,plain,(
% 31.62/4.33    ( ! [X8,X7,X9] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X9)),X8) = k2_zfmisc_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X7)),X8)) )),
% 31.62/4.33    inference(superposition,[],[f176,f74])).
% 31.62/4.33  fof(f74,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k6_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 31.62/4.33    inference(definition_unfolding,[],[f54,f68,f68])).
% 31.62/4.33  fof(f54,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f19])).
% 31.62/4.33  fof(f19,axiom,(
% 31.62/4.33    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 31.62/4.33  fof(f176,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X2,X1),k2_zfmisc_1(X0,X1)))) )),
% 31.62/4.33    inference(superposition,[],[f74,f69])).
% 31.62/4.33  fof(f69,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f42,f67,f67])).
% 31.62/4.33  fof(f42,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 31.62/4.33    inference(cnf_transformation,[],[f10])).
% 31.62/4.33  fof(f10,axiom,(
% 31.62/4.33    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 31.62/4.33  fof(f5627,plain,(
% 31.62/4.33    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k3_tarski(k6_enumset1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),k3_xboole_0(sK0,sK2),sK0)),sK1)),
% 31.62/4.33    inference(superposition,[],[f1127,f176])).
% 31.62/4.33  fof(f1127,plain,(
% 31.62/4.33    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0)))) )),
% 31.62/4.33    inference(forward_demodulation,[],[f1095,f69])).
% 31.62/4.33  fof(f1095,plain,(
% 31.62/4.33    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(sK1,sK3)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X0),k2_zfmisc_1(sK0,sK1)))) )),
% 31.62/4.33    inference(superposition,[],[f161,f85])).
% 31.62/4.33  fof(f85,plain,(
% 31.62/4.33    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 31.62/4.33    inference(unit_resulting_resolution,[],[f34,f47])).
% 31.62/4.33  fof(f34,plain,(
% 31.62/4.33    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 31.62/4.33    inference(cnf_transformation,[],[f30])).
% 31.62/4.33  fof(f161,plain,(
% 31.62/4.33    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k3_xboole_0(X4,X5),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,k3_xboole_0(X6,X7)))) = k3_tarski(k6_enumset1(k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k2_zfmisc_1(k3_xboole_0(X4,X5),X8),k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))))) )),
% 31.62/4.33    inference(superposition,[],[f73,f59])).
% 31.62/4.33  fof(f73,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k6_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 31.62/4.33    inference(definition_unfolding,[],[f55,f68,f68])).
% 31.62/4.33  fof(f55,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f19])).
% 31.62/4.33  fof(f724,plain,(
% 31.62/4.33    ( ! [X0] : (k2_zfmisc_1(k5_xboole_0(k3_xboole_0(sK0,sK2),k3_xboole_0(k3_xboole_0(sK0,sK2),X0)),k3_xboole_0(sK1,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(X0,sK3)))) )),
% 31.62/4.33    inference(superposition,[],[f150,f85])).
% 31.62/4.33  fof(f150,plain,(
% 31.62/4.33    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),X8)),k3_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k3_xboole_0(k2_zfmisc_1(k3_xboole_0(X4,X5),X6),k2_zfmisc_1(X8,X7)))) )),
% 31.62/4.33    inference(forward_demodulation,[],[f141,f59])).
% 31.62/4.33  fof(f141,plain,(
% 31.62/4.33    ( ! [X6,X4,X8,X7,X5] : (k2_zfmisc_1(k5_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(k3_xboole_0(X4,X5),X8)),k3_xboole_0(X6,X7)) = k5_xboole_0(k3_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)),k2_zfmisc_1(k3_xboole_0(k3_xboole_0(X4,X5),X8),k3_xboole_0(X6,X7)))) )),
% 31.62/4.33    inference(superposition,[],[f122,f59])).
% 31.62/4.33  fof(f122,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k3_xboole_0(X0,X1),X2))) )),
% 31.62/4.33    inference(backward_demodulation,[],[f76,f119])).
% 31.62/4.33  fof(f119,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 31.62/4.33    inference(superposition,[],[f59,f40])).
% 31.62/4.33  fof(f76,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 31.62/4.33    inference(definition_unfolding,[],[f56,f46,f46])).
% 31.62/4.33  fof(f56,plain,(
% 31.62/4.33    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 31.62/4.33    inference(cnf_transformation,[],[f21])).
% 31.62/4.33  fof(f48,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 31.62/4.33    inference(cnf_transformation,[],[f32])).
% 31.62/4.33  fof(f72,plain,(
% 31.62/4.33    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 31.62/4.33    inference(definition_unfolding,[],[f51,f46])).
% 31.62/4.33  fof(f51,plain,(
% 31.62/4.33    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 31.62/4.33    inference(cnf_transformation,[],[f33])).
% 31.62/4.33  fof(f33,plain,(
% 31.62/4.33    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 31.62/4.33    inference(nnf_transformation,[],[f2])).
% 31.62/4.33  fof(f2,axiom,(
% 31.62/4.33    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 31.62/4.33    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 31.62/4.33  fof(f12477,plain,(
% 31.62/4.33    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 31.62/4.33    inference(trivial_inequality_removal,[],[f12476])).
% 31.62/4.33  fof(f12476,plain,(
% 31.62/4.33    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 31.62/4.33    inference(superposition,[],[f72,f7726])).
% 31.62/4.33  fof(f7726,plain,(
% 31.62/4.33    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 31.62/4.33    inference(trivial_inequality_removal,[],[f7681])).
% 31.62/4.33  fof(f7681,plain,(
% 31.62/4.33    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 31.62/4.33    inference(superposition,[],[f48,f6095])).
% 31.62/4.33  fof(f6095,plain,(
% 31.62/4.33    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 31.62/4.33    inference(forward_demodulation,[],[f6045,f37])).
% 31.62/4.33  fof(f6045,plain,(
% 31.62/4.33    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 31.62/4.33    inference(superposition,[],[f122,f5688])).
% 31.62/4.33  fof(f35,plain,(
% 31.62/4.33    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 31.62/4.33    inference(cnf_transformation,[],[f30])).
% 31.62/4.33  % SZS output end Proof for theBenchmark
% 31.62/4.33  % (30468)------------------------------
% 31.62/4.33  % (30468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.62/4.33  % (30468)Termination reason: Refutation
% 31.62/4.33  
% 31.62/4.33  % (30468)Memory used [KB]: 28400
% 31.62/4.33  % (30468)Time elapsed: 2.088 s
% 31.62/4.33  % (30468)------------------------------
% 31.62/4.33  % (30468)------------------------------
% 31.62/4.33  % (30416)Success in time 3.961 s
%------------------------------------------------------------------------------
