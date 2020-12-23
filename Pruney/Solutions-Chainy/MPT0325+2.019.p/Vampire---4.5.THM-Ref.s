%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 9.33s
% Output     : Refutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 263 expanded)
%              Number of leaves         :   12 (  69 expanded)
%              Depth                    :   27
%              Number of atoms          :  161 ( 588 expanded)
%              Number of equality atoms :  122 ( 391 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5554,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5427,f40])).

fof(f40,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5427,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f23,f5286])).

fof(f5286,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f5171,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5171,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f23,f5134])).

fof(f5134,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f5089])).

fof(f5089,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f4400,f5078])).

fof(f5078,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f5075,f4515])).

fof(f4515,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f4514])).

fof(f4514,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f4443])).

fof(f4443,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f4442,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f4442,plain,
    ( k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f4413,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f4413,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK0),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f104,f4399])).

fof(f4399,plain,
    ( sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f4391,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4391,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f4390])).

fof(f4390,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f4316])).

fof(f4316,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f4295])).

fof(f4295,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f30,f4271])).

fof(f4271,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[],[f4256,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f4256,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)) ),
    inference(forward_demodulation,[],[f4244,f39])).

fof(f4244,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[],[f2740,f442])).

fof(f442,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X17,X18),X17) ),
    inference(forward_demodulation,[],[f431,f25])).

fof(f431,plain,(
    ! [X17,X18] : k4_xboole_0(k3_xboole_0(X17,X18),X17) = k5_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f49,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f49,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2740,plain,(
    ! [X23] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(k3_xboole_0(sK1,sK3),X23)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X23)) ),
    inference(superposition,[],[f216,f41])).

fof(f41,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f22,f29])).

fof(f22,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).

fof(f17,plain,
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

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f216,plain,(
    ! [X6,X8,X7,X5,X9] : k2_zfmisc_1(k3_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X7,X8),X9)) = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)),k2_zfmisc_1(k3_xboole_0(X5,X6),X9)) ),
    inference(superposition,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f28,f35])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5075,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f5067,f24])).

fof(f24,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f5067,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f5066])).

fof(f5066,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f33,f4976])).

fof(f4976,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f4955])).

fof(f4955,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f30,f4865])).

fof(f4865,plain,(
    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4831,f1941])).

fof(f1941,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,X6),sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f1317,f208])).

fof(f208,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f38,f26])).

fof(f1317,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f1311,f27])).

fof(f1311,plain,(
    ! [X29] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1297,f25])).

fof(f1297,plain,(
    ! [X29] : k4_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f49,f1188])).

fof(f1188,plain,(
    ! [X28] : k3_xboole_0(X28,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X28,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f95,f694])).

fof(f694,plain,(
    ! [X32] : k3_xboole_0(X32,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X32)) ),
    inference(superposition,[],[f101,f41])).

fof(f101,plain,(
    ! [X6,X7,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f35,f27])).

fof(f4831,plain,(
    k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f2610,f438])).

fof(f438,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f427,f28])).

fof(f427,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f28,f95])).

fof(f2610,plain,(
    ! [X23] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(X23,k3_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X23),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f215,f41])).

fof(f215,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k4_xboole_0(X4,k3_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X4),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(superposition,[],[f37,f38])).

fof(f4400,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f4399,f95])).

fof(f23,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:58:47 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (8651)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (8643)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (8641)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (8647)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8659)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (8654)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (8638)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8636)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8640)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8658)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (8650)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (8649)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (8653)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (8635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (8637)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (8664)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (8662)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (8642)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (8646)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (8656)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (8661)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (8657)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (8663)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (8648)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (8657)Refutation not found, incomplete strategy% (8657)------------------------------
% 0.21/0.55  % (8657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8657)Memory used [KB]: 10618
% 0.21/0.55  % (8657)Time elapsed: 0.139 s
% 0.21/0.55  % (8657)------------------------------
% 0.21/0.55  % (8657)------------------------------
% 0.21/0.55  % (8645)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (8655)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (8660)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (8644)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (8652)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.59  % (8652)Refutation not found, incomplete strategy% (8652)------------------------------
% 0.21/0.59  % (8652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (8652)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (8652)Memory used [KB]: 10618
% 0.21/0.59  % (8652)Time elapsed: 0.143 s
% 0.21/0.59  % (8652)------------------------------
% 0.21/0.59  % (8652)------------------------------
% 2.97/0.76  % (8687)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.97/0.84  % (8640)Time limit reached!
% 2.97/0.84  % (8640)------------------------------
% 2.97/0.84  % (8640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.84  % (8640)Termination reason: Time limit
% 2.97/0.84  % (8640)Termination phase: Saturation
% 2.97/0.84  
% 2.97/0.84  % (8640)Memory used [KB]: 8571
% 2.97/0.84  % (8640)Time elapsed: 0.400 s
% 2.97/0.84  % (8640)------------------------------
% 2.97/0.84  % (8640)------------------------------
% 2.97/0.84  % (8668)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.04/0.92  % (8645)Time limit reached!
% 4.04/0.92  % (8645)------------------------------
% 4.04/0.92  % (8645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.92  % (8645)Termination reason: Time limit
% 4.04/0.92  
% 4.04/0.92  % (8645)Memory used [KB]: 13816
% 4.04/0.92  % (8645)Time elapsed: 0.511 s
% 4.04/0.92  % (8645)------------------------------
% 4.04/0.92  % (8645)------------------------------
% 4.04/0.93  % (8635)Time limit reached!
% 4.04/0.93  % (8635)------------------------------
% 4.04/0.93  % (8635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.93  % (8635)Termination reason: Time limit
% 4.04/0.93  
% 4.04/0.93  % (8635)Memory used [KB]: 4093
% 4.04/0.93  % (8635)Time elapsed: 0.508 s
% 4.04/0.93  % (8635)------------------------------
% 4.04/0.93  % (8635)------------------------------
% 4.04/0.93  % (8647)Time limit reached!
% 4.04/0.93  % (8647)------------------------------
% 4.04/0.93  % (8647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.93  % (8647)Termination reason: Time limit
% 4.04/0.93  % (8647)Termination phase: Saturation
% 4.04/0.93  
% 4.04/0.93  % (8647)Memory used [KB]: 8699
% 4.04/0.93  % (8647)Time elapsed: 0.500 s
% 4.04/0.93  % (8647)------------------------------
% 4.04/0.93  % (8647)------------------------------
% 4.51/0.96  % (8636)Time limit reached!
% 4.51/0.96  % (8636)------------------------------
% 4.51/0.96  % (8636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.96  % (8636)Termination reason: Time limit
% 4.51/0.96  % (8636)Termination phase: Saturation
% 4.51/0.96  
% 4.51/0.96  % (8636)Memory used [KB]: 7803
% 4.51/0.96  % (8636)Time elapsed: 0.500 s
% 4.51/0.96  % (8636)------------------------------
% 4.51/0.96  % (8636)------------------------------
% 4.84/1.03  % (8651)Time limit reached!
% 4.84/1.03  % (8651)------------------------------
% 4.84/1.03  % (8651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.84/1.03  % (8651)Termination reason: Time limit
% 4.84/1.03  
% 4.84/1.03  % (8651)Memory used [KB]: 14456
% 4.84/1.03  % (8651)Time elapsed: 0.615 s
% 4.84/1.03  % (8651)------------------------------
% 4.84/1.03  % (8651)------------------------------
% 4.84/1.04  % (8694)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.17/1.05  % (8663)Time limit reached!
% 5.17/1.05  % (8663)------------------------------
% 5.17/1.05  % (8663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.05  % (8663)Termination reason: Time limit
% 5.17/1.05  
% 5.17/1.05  % (8663)Memory used [KB]: 8187
% 5.17/1.05  % (8663)Time elapsed: 0.642 s
% 5.17/1.05  % (8663)------------------------------
% 5.17/1.05  % (8663)------------------------------
% 5.17/1.06  % (8642)Time limit reached!
% 5.17/1.06  % (8642)------------------------------
% 5.17/1.06  % (8642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.17/1.06  % (8642)Termination reason: Time limit
% 5.17/1.06  
% 5.17/1.06  % (8642)Memory used [KB]: 9594
% 5.17/1.06  % (8642)Time elapsed: 0.614 s
% 5.17/1.06  % (8642)------------------------------
% 5.17/1.06  % (8642)------------------------------
% 5.17/1.10  % (8695)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.17/1.15  % (8697)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.17/1.15  % (8696)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.17/1.16  % (8698)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.66/1.24  % (8656)Time limit reached!
% 6.66/1.24  % (8656)------------------------------
% 6.66/1.24  % (8656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.66/1.24  % (8656)Termination reason: Time limit
% 6.66/1.24  
% 6.66/1.24  % (8656)Memory used [KB]: 4733
% 6.66/1.24  % (8656)Time elapsed: 0.828 s
% 6.66/1.24  % (8656)------------------------------
% 6.66/1.24  % (8656)------------------------------
% 6.66/1.26  % (8699)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 7.07/1.29  % (8700)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 7.07/1.31  % (8701)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.97/1.39  % (8695)Time limit reached!
% 7.97/1.39  % (8695)------------------------------
% 7.97/1.39  % (8695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.97/1.39  % (8695)Termination reason: Time limit
% 7.97/1.39  
% 7.97/1.39  % (8695)Memory used [KB]: 7036
% 7.97/1.39  % (8695)Time elapsed: 0.419 s
% 7.97/1.39  % (8695)------------------------------
% 7.97/1.39  % (8695)------------------------------
% 7.97/1.43  % (8696)Time limit reached!
% 7.97/1.43  % (8696)------------------------------
% 7.97/1.43  % (8696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.97/1.43  % (8696)Termination reason: Time limit
% 7.97/1.43  
% 7.97/1.43  % (8696)Memory used [KB]: 12665
% 7.97/1.43  % (8696)Time elapsed: 0.437 s
% 7.97/1.43  % (8696)------------------------------
% 7.97/1.43  % (8696)------------------------------
% 7.97/1.43  % (8637)Time limit reached!
% 7.97/1.43  % (8637)------------------------------
% 7.97/1.43  % (8637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.48/1.45  % (8637)Termination reason: Time limit
% 8.48/1.45  % (8637)Termination phase: Saturation
% 8.48/1.45  
% 8.48/1.45  % (8637)Memory used [KB]: 17270
% 8.48/1.45  % (8637)Time elapsed: 1.016 s
% 8.48/1.45  % (8637)------------------------------
% 8.48/1.45  % (8637)------------------------------
% 8.48/1.48  % (8702)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.33/1.60  % (8704)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.33/1.61  % (8698)Refutation found. Thanks to Tanya!
% 9.33/1.61  % SZS status Theorem for theBenchmark
% 9.33/1.61  % SZS output start Proof for theBenchmark
% 9.33/1.61  fof(f5554,plain,(
% 9.33/1.61    $false),
% 9.33/1.61    inference(subsumption_resolution,[],[f5427,f40])).
% 9.33/1.61  fof(f40,plain,(
% 9.33/1.61    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 9.33/1.61    inference(equality_resolution,[],[f31])).
% 9.33/1.61  fof(f31,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 9.33/1.61    inference(cnf_transformation,[],[f20])).
% 9.33/1.61  fof(f20,plain,(
% 9.33/1.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 9.33/1.61    inference(flattening,[],[f19])).
% 9.33/1.61  fof(f19,plain,(
% 9.33/1.61    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 9.33/1.61    inference(nnf_transformation,[],[f8])).
% 9.33/1.61  fof(f8,axiom,(
% 9.33/1.61    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 9.33/1.61  fof(f5427,plain,(
% 9.33/1.61    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 9.33/1.61    inference(backward_demodulation,[],[f23,f5286])).
% 9.33/1.61  fof(f5286,plain,(
% 9.33/1.61    k1_xboole_0 = sK0),
% 9.33/1.61    inference(subsumption_resolution,[],[f5171,f39])).
% 9.33/1.61  fof(f39,plain,(
% 9.33/1.61    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 9.33/1.61    inference(equality_resolution,[],[f32])).
% 9.33/1.61  fof(f32,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 9.33/1.61    inference(cnf_transformation,[],[f20])).
% 9.33/1.61  fof(f5171,plain,(
% 9.33/1.61    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 9.33/1.61    inference(superposition,[],[f23,f5134])).
% 9.33/1.61  fof(f5134,plain,(
% 9.33/1.61    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 9.33/1.61    inference(duplicate_literal_removal,[],[f5089])).
% 9.33/1.61  fof(f5089,plain,(
% 9.33/1.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f4400,f5078])).
% 9.33/1.61  fof(f5078,plain,(
% 9.33/1.61    k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(resolution,[],[f5075,f4515])).
% 9.33/1.61  fof(f4515,plain,(
% 9.33/1.61    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(trivial_inequality_removal,[],[f4514])).
% 9.33/1.61  fof(f4514,plain,(
% 9.33/1.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f33,f4443])).
% 9.33/1.61  fof(f4443,plain,(
% 9.33/1.61    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(forward_demodulation,[],[f4442,f25])).
% 9.33/1.61  fof(f25,plain,(
% 9.33/1.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 9.33/1.61    inference(cnf_transformation,[],[f7])).
% 9.33/1.61  fof(f7,axiom,(
% 9.33/1.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 9.33/1.61  fof(f4442,plain,(
% 9.33/1.61    k5_xboole_0(sK0,sK0) = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(forward_demodulation,[],[f4413,f26])).
% 9.33/1.61  fof(f26,plain,(
% 9.33/1.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 9.33/1.61    inference(cnf_transformation,[],[f13])).
% 9.33/1.61  fof(f13,plain,(
% 9.33/1.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 9.33/1.61    inference(rectify,[],[f2])).
% 9.33/1.61  fof(f2,axiom,(
% 9.33/1.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 9.33/1.61  fof(f4413,plain,(
% 9.33/1.61    k4_xboole_0(k3_xboole_0(sK0,sK0),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK0),sK0) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f104,f4399])).
% 9.33/1.61  fof(f4399,plain,(
% 9.33/1.61    sK0 = k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(resolution,[],[f4391,f29])).
% 9.33/1.61  fof(f29,plain,(
% 9.33/1.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 9.33/1.61    inference(cnf_transformation,[],[f16])).
% 9.33/1.61  fof(f16,plain,(
% 9.33/1.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 9.33/1.61    inference(ennf_transformation,[],[f6])).
% 9.33/1.61  fof(f6,axiom,(
% 9.33/1.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 9.33/1.61  fof(f4391,plain,(
% 9.33/1.61    r1_tarski(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(trivial_inequality_removal,[],[f4390])).
% 9.33/1.61  fof(f4390,plain,(
% 9.33/1.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f33,f4316])).
% 9.33/1.61  fof(f4316,plain,(
% 9.33/1.61    k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(trivial_inequality_removal,[],[f4295])).
% 9.33/1.61  fof(f4295,plain,(
% 9.33/1.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f30,f4271])).
% 9.33/1.61  fof(f4271,plain,(
% 9.33/1.61    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 9.33/1.61    inference(superposition,[],[f4256,f36])).
% 9.33/1.61  fof(f36,plain,(
% 9.33/1.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 9.33/1.61    inference(cnf_transformation,[],[f10])).
% 9.33/1.61  fof(f10,axiom,(
% 9.33/1.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 9.33/1.61  fof(f4256,plain,(
% 9.33/1.61    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1))),
% 9.33/1.61    inference(forward_demodulation,[],[f4244,f39])).
% 9.33/1.61  fof(f4244,plain,(
% 9.33/1.61    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1))),
% 9.33/1.61    inference(superposition,[],[f2740,f442])).
% 9.33/1.61  fof(f442,plain,(
% 9.33/1.61    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X17,X18),X17)) )),
% 9.33/1.61    inference(forward_demodulation,[],[f431,f25])).
% 9.33/1.61  fof(f431,plain,(
% 9.33/1.61    ( ! [X17,X18] : (k4_xboole_0(k3_xboole_0(X17,X18),X17) = k5_xboole_0(k3_xboole_0(X17,X18),k3_xboole_0(X17,X18))) )),
% 9.33/1.61    inference(superposition,[],[f49,f95])).
% 9.33/1.61  fof(f95,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.33/1.61    inference(superposition,[],[f35,f26])).
% 9.33/1.61  fof(f35,plain,(
% 9.33/1.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 9.33/1.61    inference(cnf_transformation,[],[f5])).
% 9.33/1.61  fof(f5,axiom,(
% 9.33/1.61    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 9.33/1.61  fof(f49,plain,(
% 9.33/1.61    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 9.33/1.61    inference(superposition,[],[f28,f27])).
% 9.33/1.61  fof(f27,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.33/1.61    inference(cnf_transformation,[],[f1])).
% 9.33/1.61  fof(f1,axiom,(
% 9.33/1.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.33/1.61  fof(f28,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 9.33/1.61    inference(cnf_transformation,[],[f4])).
% 9.33/1.61  fof(f4,axiom,(
% 9.33/1.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 9.33/1.61  fof(f2740,plain,(
% 9.33/1.61    ( ! [X23] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(k3_xboole_0(sK1,sK3),X23)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X23))) )),
% 9.33/1.61    inference(superposition,[],[f216,f41])).
% 9.33/1.61  fof(f41,plain,(
% 9.33/1.61    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 9.33/1.61    inference(unit_resulting_resolution,[],[f22,f29])).
% 9.33/1.61  fof(f22,plain,(
% 9.33/1.61    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 9.33/1.61    inference(cnf_transformation,[],[f18])).
% 9.33/1.61  fof(f18,plain,(
% 9.33/1.61    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 9.33/1.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f17])).
% 9.33/1.61  fof(f17,plain,(
% 9.33/1.61    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 9.33/1.61    introduced(choice_axiom,[])).
% 9.33/1.61  fof(f15,plain,(
% 9.33/1.61    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 9.33/1.61    inference(flattening,[],[f14])).
% 9.33/1.61  fof(f14,plain,(
% 9.33/1.61    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 9.33/1.61    inference(ennf_transformation,[],[f12])).
% 9.33/1.61  fof(f12,negated_conjecture,(
% 9.33/1.61    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 9.33/1.61    inference(negated_conjecture,[],[f11])).
% 9.33/1.61  fof(f11,conjecture,(
% 9.33/1.61    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 9.33/1.61  fof(f216,plain,(
% 9.33/1.61    ( ! [X6,X8,X7,X5,X9] : (k2_zfmisc_1(k3_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X7,X8),X9)) = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)),k2_zfmisc_1(k3_xboole_0(X5,X6),X9))) )),
% 9.33/1.61    inference(superposition,[],[f37,f38])).
% 9.33/1.61  fof(f38,plain,(
% 9.33/1.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 9.33/1.61    inference(cnf_transformation,[],[f9])).
% 9.33/1.61  fof(f9,axiom,(
% 9.33/1.61    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 9.33/1.61  fof(f37,plain,(
% 9.33/1.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 9.33/1.61    inference(cnf_transformation,[],[f10])).
% 9.33/1.61  fof(f30,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 9.33/1.61    inference(cnf_transformation,[],[f20])).
% 9.33/1.61  fof(f104,plain,(
% 9.33/1.61    ( ! [X4,X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4)))) )),
% 9.33/1.61    inference(superposition,[],[f28,f35])).
% 9.33/1.61  fof(f33,plain,(
% 9.33/1.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 9.33/1.61    inference(cnf_transformation,[],[f21])).
% 9.33/1.61  fof(f21,plain,(
% 9.33/1.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 9.33/1.61    inference(nnf_transformation,[],[f3])).
% 9.33/1.61  fof(f3,axiom,(
% 9.33/1.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 9.33/1.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 9.33/1.61  fof(f5075,plain,(
% 9.33/1.61    ~r1_tarski(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 9.33/1.61    inference(resolution,[],[f5067,f24])).
% 9.33/1.61  fof(f24,plain,(
% 9.33/1.61    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 9.33/1.61    inference(cnf_transformation,[],[f18])).
% 9.33/1.61  fof(f5067,plain,(
% 9.33/1.61    r1_tarski(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 9.33/1.61    inference(trivial_inequality_removal,[],[f5066])).
% 9.33/1.61  fof(f5066,plain,(
% 9.33/1.61    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 9.33/1.61    inference(superposition,[],[f33,f4976])).
% 9.33/1.61  fof(f4976,plain,(
% 9.33/1.61    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 9.33/1.61    inference(trivial_inequality_removal,[],[f4955])).
% 9.33/1.61  fof(f4955,plain,(
% 9.33/1.61    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 9.33/1.61    inference(superposition,[],[f30,f4865])).
% 9.33/1.61  fof(f4865,plain,(
% 9.33/1.61    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK3))),
% 9.33/1.61    inference(forward_demodulation,[],[f4831,f1941])).
% 9.33/1.61  fof(f1941,plain,(
% 9.33/1.61    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,X6),sK1),k2_zfmisc_1(sK0,sK1))) )),
% 9.33/1.61    inference(superposition,[],[f1317,f208])).
% 9.33/1.61  fof(f208,plain,(
% 9.33/1.61    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 9.33/1.61    inference(superposition,[],[f38,f26])).
% 9.33/1.61  fof(f1317,plain,(
% 9.33/1.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(sK0,sK1))) )),
% 9.33/1.61    inference(superposition,[],[f1311,f27])).
% 9.33/1.61  fof(f1311,plain,(
% 9.33/1.61    ( ! [X29] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))) )),
% 9.33/1.61    inference(forward_demodulation,[],[f1297,f25])).
% 9.33/1.61  fof(f1297,plain,(
% 9.33/1.61    ( ! [X29] : (k4_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) = k5_xboole_0(k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)),k3_xboole_0(X29,k2_zfmisc_1(sK0,sK1)))) )),
% 9.33/1.61    inference(superposition,[],[f49,f1188])).
% 9.33/1.61  fof(f1188,plain,(
% 9.33/1.61    ( ! [X28] : (k3_xboole_0(X28,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X28,k2_zfmisc_1(sK0,sK1)))) )),
% 9.33/1.61    inference(superposition,[],[f95,f694])).
% 9.33/1.61  fof(f694,plain,(
% 9.33/1.61    ( ! [X32] : (k3_xboole_0(X32,k2_zfmisc_1(sK0,sK1)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k3_xboole_0(k2_zfmisc_1(sK2,sK3),X32))) )),
% 9.33/1.61    inference(superposition,[],[f101,f41])).
% 9.33/1.61  fof(f101,plain,(
% 9.33/1.61    ( ! [X6,X7,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X7)) = k3_xboole_0(X7,k3_xboole_0(X5,X6))) )),
% 9.33/1.61    inference(superposition,[],[f35,f27])).
% 9.33/1.61  fof(f4831,plain,(
% 9.33/1.61    k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(sK1,sK3))),
% 9.33/1.61    inference(superposition,[],[f2610,f438])).
% 9.33/1.61  fof(f438,plain,(
% 9.33/1.61    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 9.33/1.61    inference(forward_demodulation,[],[f427,f28])).
% 9.33/1.61  fof(f427,plain,(
% 9.33/1.61    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 9.33/1.61    inference(superposition,[],[f28,f95])).
% 9.33/1.61  fof(f2610,plain,(
% 9.33/1.61    ( ! [X23] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(X23,k3_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X23),k2_zfmisc_1(sK0,sK1))) )),
% 9.33/1.61    inference(superposition,[],[f215,f41])).
% 9.33/1.61  fof(f215,plain,(
% 9.33/1.61    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k4_xboole_0(X4,k3_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X4),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 9.33/1.61    inference(superposition,[],[f37,f38])).
% 9.33/1.61  fof(f4400,plain,(
% 9.33/1.61    sK0 = k3_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 9.33/1.61    inference(superposition,[],[f4399,f95])).
% 9.33/1.61  fof(f23,plain,(
% 9.33/1.61    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 9.33/1.61    inference(cnf_transformation,[],[f18])).
% 9.33/1.61  % SZS output end Proof for theBenchmark
% 9.33/1.61  % (8698)------------------------------
% 9.33/1.61  % (8698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.61  % (8698)Termination reason: Refutation
% 9.33/1.61  
% 9.33/1.61  % (8698)Memory used [KB]: 5117
% 9.33/1.61  % (8698)Time elapsed: 0.580 s
% 9.33/1.61  % (8698)------------------------------
% 9.33/1.61  % (8698)------------------------------
% 9.33/1.63  % (8703)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.33/1.63  % (8634)Success in time 1.266 s
%------------------------------------------------------------------------------
