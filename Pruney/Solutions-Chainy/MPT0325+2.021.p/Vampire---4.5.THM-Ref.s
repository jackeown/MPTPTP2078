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
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 12.56s
% Output     : Refutation 12.56s
% Verified   : 
% Statistics : Number of formulae       :  149 (2513 expanded)
%              Number of leaves         :   14 ( 690 expanded)
%              Depth                    :   44
%              Number of atoms          :  208 (4770 expanded)
%              Number of equality atoms :  173 (3577 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19105,f19108])).

fof(f19108,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f25,f19103])).

fof(f19103,plain,(
    r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f18830,f10651])).

fof(f10651,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f10458,f729])).

fof(f729,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f720,f27])).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f720,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f72,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f36,f26])).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f10458,plain,(
    sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f1672,f9048])).

fof(f9048,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f9047,f24])).

fof(f24,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f19,plain,
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

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f9047,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f9046,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f47,f26])).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f9046,plain,
    ( k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f9040,f7288])).

fof(f7288,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f7249,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f7249,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) ),
    inference(superposition,[],[f4994,f213])).

fof(f213,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f40,f28])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f4994,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f114,f4889])).

fof(f4889,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f4874,f203])).

fof(f203,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f40,f30])).

fof(f4874,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4873,f696])).

fof(f696,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = X31 ),
    inference(forward_demodulation,[],[f688,f27])).

fof(f688,plain,(
    ! [X31] : k4_xboole_0(X31,k1_xboole_0) = k5_xboole_0(X31,k1_xboole_0) ),
    inference(superposition,[],[f48,f630])).

fof(f630,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f490,f621])).

fof(f621,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f44,f597])).

fof(f597,plain,(
    ! [X36] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,X36),k1_xboole_0) ),
    inference(forward_demodulation,[],[f577,f26])).

fof(f577,plain,(
    ! [X36] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X36),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X36),k3_xboole_0(k1_xboole_0,X36)) ),
    inference(superposition,[],[f48,f490])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f490,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f258,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f258,plain,(
    ! [X6,X7] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),X7)) = k3_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f37,f231])).

fof(f231,plain,(
    ! [X17] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)) ),
    inference(forward_demodulation,[],[f230,f42])).

fof(f42,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f230,plain,(
    ! [X17,X16] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X16),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)) ),
    inference(forward_demodulation,[],[f206,f42])).

fof(f206,plain,(
    ! [X17,X16] : k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X16),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X16,X17)) ),
    inference(superposition,[],[f40,f54])).

fof(f54,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f53,f32])).

fof(f53,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f29,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f51,f26])).

fof(f51,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f31,f43])).

fof(f43,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f23,f32])).

fof(f23,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f48,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f31,f30])).

fof(f4873,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f4840,f41])).

fof(f4840,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k1_xboole_0)) ),
    inference(superposition,[],[f3548,f696])).

fof(f3548,plain,(
    ! [X20] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(k3_xboole_0(sK1,sK3),X20)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X20)) ),
    inference(superposition,[],[f225,f43])).

fof(f225,plain,(
    ! [X6,X8,X7,X5,X9] : k2_zfmisc_1(k3_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X7,X8),X9)) = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)),k2_zfmisc_1(k3_xboole_0(X5,X6),X9)) ),
    inference(superposition,[],[f39,f40])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f114,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f28])).

fof(f9040,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f3370,f8465])).

fof(f8465,plain,(
    ! [X20] :
      ( sK1 = k4_xboole_0(sK1,X20)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(forward_demodulation,[],[f8367,f27])).

fof(f8367,plain,(
    ! [X20] :
      ( k4_xboole_0(sK1,X20) = k5_xboole_0(sK1,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f31,f7705])).

fof(f7705,plain,(
    ! [X11] :
      ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
      | k1_xboole_0 = k3_xboole_0(sK1,X11) ) ),
    inference(trivial_inequality_removal,[],[f7682])).

fof(f7682,plain,(
    ! [X11] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k4_xboole_0(sK0,sK2)
      | k1_xboole_0 = k3_xboole_0(sK1,X11) ) ),
    inference(superposition,[],[f33,f7349])).

fof(f7349,plain,(
    ! [X11] : k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X11)) ),
    inference(forward_demodulation,[],[f7322,f630])).

fof(f7322,plain,(
    ! [X11] : k2_zfmisc_1(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X11)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),X11)) ),
    inference(superposition,[],[f202,f7302])).

fof(f7302,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f7301,f26])).

fof(f7301,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f7269,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7269,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f48,f4994])).

fof(f202,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f40,f28])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3370,plain,(
    ! [X20] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(X20,k3_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X20),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f224,f43])).

fof(f224,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k4_xboole_0(X4,k3_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X4),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(superposition,[],[f39,f40])).

fof(f1672,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f1633,f27])).

fof(f1633,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f74,f26])).

fof(f74,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f36,f31])).

fof(f18830,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f29,f17807])).

fof(f17807,plain,(
    ! [X31,X32] : k3_xboole_0(X32,X31) = k4_xboole_0(X31,k4_xboole_0(X31,X32)) ),
    inference(forward_demodulation,[],[f17738,f14977])).

fof(f14977,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f5679,f13079])).

fof(f13079,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X15)) = X15 ),
    inference(forward_demodulation,[],[f13012,f802])).

fof(f802,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f114,f30])).

fof(f13012,plain,(
    ! [X15,X16] : k5_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X15,k3_xboole_0(X16,X15))) = X15 ),
    inference(superposition,[],[f1672,f12451])).

fof(f12451,plain,(
    ! [X23,X22] : k4_xboole_0(X23,k3_xboole_0(X22,X23)) = k4_xboole_0(X23,X22) ),
    inference(forward_demodulation,[],[f12377,f48])).

fof(f12377,plain,(
    ! [X23,X22] : k4_xboole_0(X23,k3_xboole_0(X22,X23)) = k5_xboole_0(X23,k3_xboole_0(X22,X23)) ),
    inference(superposition,[],[f48,f11990])).

fof(f11990,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(k3_xboole_0(X8,X9),X9) ),
    inference(forward_demodulation,[],[f11828,f696])).

fof(f11828,plain,(
    ! [X8,X9] : k3_xboole_0(k3_xboole_0(X8,X9),X9) = k4_xboole_0(k3_xboole_0(X8,X9),k1_xboole_0) ),
    inference(superposition,[],[f11804,f2318])).

fof(f2318,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f2218,f26])).

fof(f2218,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f124,f28])).

fof(f124,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f31,f37])).

fof(f11804,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k4_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f557,f5881])).

fof(f5881,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f5679,f31])).

fof(f557,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f48,f44])).

fof(f5679,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f72,f729])).

fof(f17738,plain,(
    ! [X31,X32] : k4_xboole_0(X31,k4_xboole_0(X31,X32)) = k5_xboole_0(k4_xboole_0(X31,X32),X31) ),
    inference(superposition,[],[f16320,f459])).

fof(f459,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f44,f30])).

fof(f16320,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(k3_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f14976,f30])).

fof(f14976,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f5904,f13079])).

fof(f5904,plain,(
    ! [X14,X13] : k5_xboole_0(X14,k5_xboole_0(X13,X14)) = X13 ),
    inference(forward_demodulation,[],[f5885,f27])).

fof(f5885,plain,(
    ! [X14,X13] : k5_xboole_0(X14,k5_xboole_0(X13,X14)) = k5_xboole_0(X13,k1_xboole_0) ),
    inference(superposition,[],[f5679,f76])).

fof(f76,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f36,f26])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f19105,plain,(
    r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f18830,f10817])).

fof(f10817,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f10468,f729])).

fof(f10468,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f1672,f7073])).

fof(f7073,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f7072,f24])).

fof(f7072,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f7071,f50])).

fof(f7071,plain,
    ( k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f7044,f5100])).

fof(f5100,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f5061,f30])).

fof(f5061,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f4955,f202])).

fof(f4955,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f114,f4888])).

fof(f4888,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f4874,f214])).

fof(f214,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f40,f30])).

fof(f7044,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f3754,f6613])).

fof(f6613,plain,(
    ! [X25] :
      ( sK0 = k4_xboole_0(sK0,X25)
      | k1_xboole_0 = k4_xboole_0(sK1,sK3) ) ),
    inference(forward_demodulation,[],[f6518,f27])).

fof(f6518,plain,(
    ! [X25] :
      ( k4_xboole_0(sK0,X25) = k5_xboole_0(sK0,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f48,f5746])).

fof(f5746,plain,(
    ! [X11] :
      ( k1_xboole_0 = k3_xboole_0(X11,sK0)
      | k1_xboole_0 = k4_xboole_0(sK1,sK3) ) ),
    inference(trivial_inequality_removal,[],[f5723])).

fof(f5723,plain,(
    ! [X11] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(X11,sK0)
      | k1_xboole_0 = k4_xboole_0(sK1,sK3) ) ),
    inference(superposition,[],[f33,f5163])).

fof(f5163,plain,(
    ! [X13] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f5162,f630])).

fof(f5162,plain,(
    ! [X13] : k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X13,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f5134,f30])).

fof(f5134,plain,(
    ! [X13] : k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(X13,k4_xboole_0(sK1,sK3)),k1_xboole_0) ),
    inference(superposition,[],[f213,f5114])).

fof(f5114,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f5113,f26])).

fof(f5113,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f5081,f39])).

fof(f5081,plain,(
    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f48,f4955])).

fof(f3754,plain,(
    ! [X20] : k2_zfmisc_1(k4_xboole_0(X20,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(X20,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f226,f43])).

fof(f226,plain,(
    ! [X14,X12,X10,X13,X11] : k2_zfmisc_1(k4_xboole_0(X14,k3_xboole_0(X10,X11)),k3_xboole_0(X12,X13)) = k4_xboole_0(k2_zfmisc_1(X14,k3_xboole_0(X12,X13)),k3_xboole_0(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X13))) ),
    inference(superposition,[],[f38,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (4297)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (4288)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (4277)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (4280)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (4297)Refutation not found, incomplete strategy% (4297)------------------------------
% 0.22/0.51  % (4297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4278)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (4297)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (4297)Memory used [KB]: 10746
% 0.22/0.52  % (4297)Time elapsed: 0.062 s
% 0.22/0.52  % (4297)------------------------------
% 0.22/0.52  % (4297)------------------------------
% 0.22/0.52  % (4287)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (4283)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (4304)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.53  % (4285)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.53  % (4279)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.30/0.53  % (4276)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (4274)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (4300)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.54  % (4299)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.54  % (4302)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.30/0.54  % (4298)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.54  % (4301)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (4303)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.44/0.55  % (4275)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.44/0.55  % (4295)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (4296)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (4293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (4289)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.44/0.55  % (4290)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (4286)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.56  % (4291)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.44/0.56  % (4291)Refutation not found, incomplete strategy% (4291)------------------------------
% 1.44/0.56  % (4291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (4291)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (4291)Memory used [KB]: 10618
% 1.44/0.56  % (4291)Time elapsed: 0.148 s
% 1.44/0.56  % (4291)------------------------------
% 1.44/0.56  % (4291)------------------------------
% 1.44/0.56  % (4281)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.56  % (4284)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.44/0.56  % (4292)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.56  % (4282)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.03/0.64  % (4329)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.41/0.72  % (4330)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.35/0.84  % (4279)Time limit reached!
% 3.35/0.84  % (4279)------------------------------
% 3.35/0.84  % (4279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.84  % (4279)Termination reason: Time limit
% 3.35/0.84  % (4279)Termination phase: Saturation
% 3.35/0.84  
% 3.35/0.84  % (4279)Memory used [KB]: 10618
% 3.35/0.84  % (4279)Time elapsed: 0.400 s
% 3.35/0.84  % (4279)------------------------------
% 3.35/0.84  % (4279)------------------------------
% 3.60/0.91  % (4275)Time limit reached!
% 3.60/0.91  % (4275)------------------------------
% 3.60/0.91  % (4275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (4284)Time limit reached!
% 3.60/0.92  % (4284)------------------------------
% 3.60/0.92  % (4284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (4284)Termination reason: Time limit
% 3.60/0.92  % (4284)Termination phase: Saturation
% 3.60/0.92  
% 3.60/0.92  % (4284)Memory used [KB]: 16630
% 3.60/0.92  % (4284)Time elapsed: 0.500 s
% 3.60/0.92  % (4284)------------------------------
% 3.60/0.92  % (4284)------------------------------
% 3.60/0.92  % (4274)Time limit reached!
% 3.60/0.92  % (4274)------------------------------
% 3.60/0.92  % (4274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (4274)Termination reason: Time limit
% 3.60/0.92  
% 3.60/0.92  % (4274)Memory used [KB]: 5117
% 3.60/0.92  % (4274)Time elapsed: 0.517 s
% 3.60/0.92  % (4274)------------------------------
% 3.60/0.92  % (4274)------------------------------
% 3.60/0.92  % (4275)Termination reason: Time limit
% 3.60/0.92  
% 3.60/0.92  % (4275)Memory used [KB]: 9083
% 3.60/0.92  % (4275)Time elapsed: 0.508 s
% 3.60/0.92  % (4275)------------------------------
% 3.60/0.92  % (4275)------------------------------
% 3.60/0.92  % (4286)Time limit reached!
% 3.60/0.92  % (4286)------------------------------
% 3.60/0.92  % (4286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.92  % (4286)Termination reason: Time limit
% 3.60/0.92  
% 3.60/0.92  % (4286)Memory used [KB]: 10106
% 3.60/0.92  % (4286)Time elapsed: 0.523 s
% 3.60/0.92  % (4286)------------------------------
% 3.60/0.92  % (4286)------------------------------
% 4.22/0.97  % (4354)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.55/1.01  % (4303)Time limit reached!
% 4.55/1.01  % (4303)------------------------------
% 4.55/1.01  % (4303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.01  % (4303)Termination reason: Time limit
% 4.55/1.01  % (4303)Termination phase: Saturation
% 4.55/1.01  
% 4.55/1.01  % (4303)Memory used [KB]: 9850
% 4.55/1.01  % (4303)Time elapsed: 0.600 s
% 4.55/1.01  % (4303)------------------------------
% 4.55/1.01  % (4303)------------------------------
% 4.55/1.02  % (4396)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.55/1.02  % (4281)Time limit reached!
% 4.55/1.02  % (4281)------------------------------
% 4.55/1.02  % (4281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.02  % (4290)Time limit reached!
% 4.55/1.02  % (4290)------------------------------
% 4.55/1.02  % (4290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.02  % (4281)Termination reason: Time limit
% 4.55/1.02  
% 4.55/1.02  % (4281)Memory used [KB]: 11769
% 4.55/1.02  % (4281)Time elapsed: 0.612 s
% 4.55/1.02  % (4281)------------------------------
% 4.55/1.02  % (4281)------------------------------
% 4.55/1.03  % (4400)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.55/1.04  % (4402)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.55/1.05  % (4290)Termination reason: Time limit
% 4.55/1.05  % (4290)Termination phase: Saturation
% 4.55/1.05  
% 4.55/1.05  % (4290)Memory used [KB]: 16630
% 4.55/1.05  % (4290)Time elapsed: 0.600 s
% 4.55/1.05  % (4290)------------------------------
% 4.55/1.05  % (4290)------------------------------
% 5.00/1.05  % (4398)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 6.22/1.15  % (4469)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.22/1.16  % (4463)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.22/1.19  % (4478)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.22/1.22  % (4296)Time limit reached!
% 6.22/1.22  % (4296)------------------------------
% 6.22/1.22  % (4296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.22/1.22  % (4296)Termination reason: Time limit
% 6.22/1.22  % (4296)Termination phase: Saturation
% 6.22/1.22  
% 6.22/1.22  % (4296)Memory used [KB]: 7547
% 6.22/1.22  % (4296)Time elapsed: 0.821 s
% 6.22/1.22  % (4296)------------------------------
% 6.22/1.22  % (4296)------------------------------
% 7.17/1.32  % (4531)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 7.69/1.37  % (4396)Time limit reached!
% 7.69/1.37  % (4396)------------------------------
% 7.69/1.37  % (4396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.69/1.37  % (4396)Termination reason: Time limit
% 7.69/1.37  % (4396)Termination phase: Saturation
% 7.69/1.37  
% 7.69/1.37  % (4396)Memory used [KB]: 8827
% 7.69/1.37  % (4396)Time elapsed: 0.400 s
% 7.69/1.37  % (4396)------------------------------
% 7.69/1.37  % (4396)------------------------------
% 7.89/1.37  % (4398)Time limit reached!
% 7.89/1.37  % (4398)------------------------------
% 7.89/1.37  % (4398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.37  % (4398)Termination reason: Time limit
% 7.89/1.37  
% 7.89/1.37  % (4398)Memory used [KB]: 14711
% 7.89/1.37  % (4398)Time elapsed: 0.431 s
% 7.89/1.37  % (4398)------------------------------
% 7.89/1.37  % (4398)------------------------------
% 7.89/1.41  % (4276)Time limit reached!
% 7.89/1.41  % (4276)------------------------------
% 7.89/1.41  % (4276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.41  % (4276)Termination reason: Time limit
% 7.89/1.41  
% 7.89/1.41  % (4276)Memory used [KB]: 21875
% 7.89/1.41  % (4276)Time elapsed: 1.008 s
% 7.89/1.41  % (4276)------------------------------
% 7.89/1.41  % (4276)------------------------------
% 8.52/1.49  % (4580)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 8.52/1.50  % (4582)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 8.52/1.51  % (4581)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 9.34/1.64  % (4301)Time limit reached!
% 9.34/1.64  % (4301)------------------------------
% 9.34/1.64  % (4301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.34/1.64  % (4301)Termination reason: Time limit
% 9.34/1.64  
% 9.34/1.64  % (4301)Memory used [KB]: 23922
% 9.34/1.64  % (4301)Time elapsed: 1.218 s
% 9.34/1.64  % (4301)------------------------------
% 9.34/1.64  % (4301)------------------------------
% 10.40/1.70  % (4289)Time limit reached!
% 10.40/1.70  % (4289)------------------------------
% 10.40/1.70  % (4289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.70  % (4289)Termination reason: Time limit
% 10.40/1.70  % (4289)Termination phase: Saturation
% 10.40/1.70  
% 10.40/1.70  % (4289)Memory used [KB]: 17782
% 10.40/1.70  % (4289)Time elapsed: 1.300 s
% 10.40/1.70  % (4289)------------------------------
% 10.40/1.70  % (4289)------------------------------
% 10.83/1.74  % (4299)Time limit reached!
% 10.83/1.74  % (4299)------------------------------
% 10.83/1.74  % (4299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.94/1.76  % (4299)Termination reason: Time limit
% 10.94/1.76  
% 10.94/1.76  % (4299)Memory used [KB]: 19701
% 10.94/1.76  % (4299)Time elapsed: 1.335 s
% 10.94/1.76  % (4299)------------------------------
% 10.94/1.76  % (4299)------------------------------
% 10.94/1.77  % (4583)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 10.94/1.81  % (4584)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.71/1.90  % (4585)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.71/1.90  % (4581)Time limit reached!
% 11.71/1.90  % (4581)------------------------------
% 11.71/1.90  % (4581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.71/1.90  % (4302)Time limit reached!
% 11.71/1.90  % (4302)------------------------------
% 11.71/1.90  % (4302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.71/1.90  % (4302)Termination reason: Time limit
% 11.71/1.90  
% 11.71/1.90  % (4302)Memory used [KB]: 16758
% 11.71/1.90  % (4302)Time elapsed: 1.501 s
% 11.71/1.90  % (4302)------------------------------
% 11.71/1.90  % (4302)------------------------------
% 11.71/1.92  % (4581)Termination reason: Time limit
% 11.71/1.92  % (4581)Termination phase: Saturation
% 11.71/1.92  
% 11.71/1.92  % (4581)Memory used [KB]: 4733
% 11.71/1.92  % (4581)Time elapsed: 0.500 s
% 11.71/1.92  % (4581)------------------------------
% 11.71/1.92  % (4581)------------------------------
% 12.33/1.94  % (4278)Time limit reached!
% 12.33/1.94  % (4278)------------------------------
% 12.33/1.94  % (4278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.33/1.94  % (4278)Termination reason: Time limit
% 12.33/1.94  % (4278)Termination phase: Saturation
% 12.33/1.94  
% 12.33/1.94  % (4278)Memory used [KB]: 19061
% 12.33/1.94  % (4278)Time elapsed: 1.500 s
% 12.33/1.94  % (4278)------------------------------
% 12.33/1.94  % (4278)------------------------------
% 12.56/2.01  % (4402)Refutation found. Thanks to Tanya!
% 12.56/2.01  % SZS status Theorem for theBenchmark
% 12.56/2.03  % SZS output start Proof for theBenchmark
% 12.56/2.03  fof(f19111,plain,(
% 12.56/2.03    $false),
% 12.56/2.03    inference(subsumption_resolution,[],[f19105,f19108])).
% 12.56/2.03  fof(f19108,plain,(
% 12.56/2.03    ~r1_tarski(sK1,sK3)),
% 12.56/2.03    inference(subsumption_resolution,[],[f25,f19103])).
% 12.56/2.03  fof(f19103,plain,(
% 12.56/2.03    r1_tarski(sK0,sK2)),
% 12.56/2.03    inference(superposition,[],[f18830,f10651])).
% 12.56/2.03  fof(f10651,plain,(
% 12.56/2.03    sK0 = k3_xboole_0(sK0,sK2)),
% 12.56/2.03    inference(superposition,[],[f10458,f729])).
% 12.56/2.03  fof(f729,plain,(
% 12.56/2.03    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 12.56/2.03    inference(forward_demodulation,[],[f720,f27])).
% 12.56/2.03  fof(f27,plain,(
% 12.56/2.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.56/2.03    inference(cnf_transformation,[],[f7])).
% 12.56/2.03  fof(f7,axiom,(
% 12.56/2.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 12.56/2.03  fof(f720,plain,(
% 12.56/2.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 12.56/2.03    inference(superposition,[],[f72,f26])).
% 12.56/2.03  fof(f26,plain,(
% 12.56/2.03    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 12.56/2.03    inference(cnf_transformation,[],[f9])).
% 12.56/2.03  fof(f9,axiom,(
% 12.56/2.03    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 12.56/2.03  fof(f72,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 12.56/2.03    inference(superposition,[],[f36,f26])).
% 12.56/2.03  fof(f36,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f8])).
% 12.56/2.03  fof(f8,axiom,(
% 12.56/2.03    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 12.56/2.03  fof(f10458,plain,(
% 12.56/2.03    sK0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK0,sK2))),
% 12.56/2.03    inference(superposition,[],[f1672,f9048])).
% 12.56/2.03  fof(f9048,plain,(
% 12.56/2.03    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 12.56/2.03    inference(subsumption_resolution,[],[f9047,f24])).
% 12.56/2.03  fof(f24,plain,(
% 12.56/2.03    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 12.56/2.03    inference(cnf_transformation,[],[f20])).
% 12.56/2.03  fof(f20,plain,(
% 12.56/2.03    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 12.56/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 12.56/2.03  fof(f19,plain,(
% 12.56/2.03    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 12.56/2.03    introduced(choice_axiom,[])).
% 12.56/2.03  fof(f17,plain,(
% 12.56/2.03    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 12.56/2.03    inference(flattening,[],[f16])).
% 12.56/2.03  fof(f16,plain,(
% 12.56/2.03    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 12.56/2.03    inference(ennf_transformation,[],[f14])).
% 12.56/2.03  fof(f14,negated_conjecture,(
% 12.56/2.03    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 12.56/2.03    inference(negated_conjecture,[],[f13])).
% 12.56/2.03  fof(f13,conjecture,(
% 12.56/2.03    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 12.56/2.03  fof(f9047,plain,(
% 12.56/2.03    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 12.56/2.03    inference(forward_demodulation,[],[f9046,f50])).
% 12.56/2.03  fof(f50,plain,(
% 12.56/2.03    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f47,f26])).
% 12.56/2.03  fof(f47,plain,(
% 12.56/2.03    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 12.56/2.03    inference(superposition,[],[f31,f28])).
% 12.56/2.03  fof(f28,plain,(
% 12.56/2.03    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 12.56/2.03    inference(cnf_transformation,[],[f15])).
% 12.56/2.03  fof(f15,plain,(
% 12.56/2.03    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 12.56/2.03    inference(rectify,[],[f2])).
% 12.56/2.03  fof(f2,axiom,(
% 12.56/2.03    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 12.56/2.03  fof(f31,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f3])).
% 12.56/2.03  fof(f3,axiom,(
% 12.56/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.56/2.03  fof(f9046,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 12.56/2.03    inference(forward_demodulation,[],[f9040,f7288])).
% 12.56/2.03  fof(f7288,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 12.56/2.03    inference(forward_demodulation,[],[f7249,f30])).
% 12.56/2.03  fof(f30,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.56/2.03    inference(cnf_transformation,[],[f1])).
% 12.56/2.03  fof(f1,axiom,(
% 12.56/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.56/2.03  fof(f7249,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)),
% 12.56/2.03    inference(superposition,[],[f4994,f213])).
% 12.56/2.03  fof(f213,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 12.56/2.03    inference(superposition,[],[f40,f28])).
% 12.56/2.03  fof(f40,plain,(
% 12.56/2.03    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f11])).
% 12.56/2.03  fof(f11,axiom,(
% 12.56/2.03    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 12.56/2.03  fof(f4994,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 12.56/2.03    inference(superposition,[],[f114,f4889])).
% 12.56/2.03  fof(f4889,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK3))),
% 12.56/2.03    inference(superposition,[],[f4874,f203])).
% 12.56/2.03  fof(f203,plain,(
% 12.56/2.03    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))) )),
% 12.56/2.03    inference(superposition,[],[f40,f30])).
% 12.56/2.03  fof(f4874,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f4873,f696])).
% 12.56/2.03  fof(f696,plain,(
% 12.56/2.03    ( ! [X31] : (k4_xboole_0(X31,k1_xboole_0) = X31) )),
% 12.56/2.03    inference(forward_demodulation,[],[f688,f27])).
% 12.56/2.03  fof(f688,plain,(
% 12.56/2.03    ( ! [X31] : (k4_xboole_0(X31,k1_xboole_0) = k5_xboole_0(X31,k1_xboole_0)) )),
% 12.56/2.03    inference(superposition,[],[f48,f630])).
% 12.56/2.03  fof(f630,plain,(
% 12.56/2.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 12.56/2.03    inference(backward_demodulation,[],[f490,f621])).
% 12.56/2.03  fof(f621,plain,(
% 12.56/2.03    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 12.56/2.03    inference(superposition,[],[f44,f597])).
% 12.56/2.03  fof(f597,plain,(
% 12.56/2.03    ( ! [X36] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(k1_xboole_0,X36),k1_xboole_0)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f577,f26])).
% 12.56/2.03  fof(f577,plain,(
% 12.56/2.03    ( ! [X36] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X36),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X36),k3_xboole_0(k1_xboole_0,X36))) )),
% 12.56/2.03    inference(superposition,[],[f48,f490])).
% 12.56/2.03  fof(f44,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 12.56/2.03    inference(unit_resulting_resolution,[],[f29,f32])).
% 12.56/2.03  fof(f32,plain,(
% 12.56/2.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 12.56/2.03    inference(cnf_transformation,[],[f18])).
% 12.56/2.03  fof(f18,plain,(
% 12.56/2.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 12.56/2.03    inference(ennf_transformation,[],[f5])).
% 12.56/2.03  fof(f5,axiom,(
% 12.56/2.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 12.56/2.03  fof(f29,plain,(
% 12.56/2.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.56/2.03    inference(cnf_transformation,[],[f6])).
% 12.56/2.03  fof(f6,axiom,(
% 12.56/2.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.56/2.03  fof(f490,plain,(
% 12.56/2.03    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 12.56/2.03    inference(superposition,[],[f258,f41])).
% 12.56/2.03  fof(f41,plain,(
% 12.56/2.03    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 12.56/2.03    inference(equality_resolution,[],[f35])).
% 12.56/2.03  fof(f35,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 12.56/2.03    inference(cnf_transformation,[],[f22])).
% 12.56/2.03  fof(f22,plain,(
% 12.56/2.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.56/2.03    inference(flattening,[],[f21])).
% 12.56/2.03  fof(f21,plain,(
% 12.56/2.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 12.56/2.03    inference(nnf_transformation,[],[f10])).
% 12.56/2.03  fof(f10,axiom,(
% 12.56/2.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 12.56/2.03  fof(f258,plain,(
% 12.56/2.03    ( ! [X6,X7] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X6),X7)) = k3_xboole_0(k1_xboole_0,X7)) )),
% 12.56/2.03    inference(superposition,[],[f37,f231])).
% 12.56/2.03  fof(f231,plain,(
% 12.56/2.03    ( ! [X17] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f230,f42])).
% 12.56/2.03  fof(f42,plain,(
% 12.56/2.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 12.56/2.03    inference(equality_resolution,[],[f34])).
% 12.56/2.03  fof(f34,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 12.56/2.03    inference(cnf_transformation,[],[f22])).
% 12.56/2.03  fof(f230,plain,(
% 12.56/2.03    ( ! [X17,X16] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X16),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f206,f42])).
% 12.56/2.03  fof(f206,plain,(
% 12.56/2.03    ( ! [X17,X16] : (k3_xboole_0(k2_zfmisc_1(k1_xboole_0,X16),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X17)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X16,X17))) )),
% 12.56/2.03    inference(superposition,[],[f40,f54])).
% 12.56/2.03  fof(f54,plain,(
% 12.56/2.03    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 12.56/2.03    inference(unit_resulting_resolution,[],[f53,f32])).
% 12.56/2.03  fof(f53,plain,(
% 12.56/2.03    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 12.56/2.03    inference(superposition,[],[f29,f52])).
% 12.56/2.03  fof(f52,plain,(
% 12.56/2.03    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f51,f26])).
% 12.56/2.03  fof(f51,plain,(
% 12.56/2.03    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 12.56/2.03    inference(superposition,[],[f31,f43])).
% 12.56/2.03  fof(f43,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 12.56/2.03    inference(unit_resulting_resolution,[],[f23,f32])).
% 12.56/2.03  fof(f23,plain,(
% 12.56/2.03    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 12.56/2.03    inference(cnf_transformation,[],[f20])).
% 12.56/2.03  fof(f37,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f4])).
% 12.56/2.03  fof(f4,axiom,(
% 12.56/2.03    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 12.56/2.03  fof(f48,plain,(
% 12.56/2.03    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 12.56/2.03    inference(superposition,[],[f31,f30])).
% 12.56/2.03  fof(f4873,plain,(
% 12.56/2.03    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f4840,f41])).
% 12.56/2.03  fof(f4840,plain,(
% 12.56/2.03    k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),k1_xboole_0))),
% 12.56/2.03    inference(superposition,[],[f3548,f696])).
% 12.56/2.03  fof(f3548,plain,(
% 12.56/2.03    ( ! [X20] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(k3_xboole_0(sK1,sK3),X20)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X20))) )),
% 12.56/2.03    inference(superposition,[],[f225,f43])).
% 12.56/2.03  fof(f225,plain,(
% 12.56/2.03    ( ! [X6,X8,X7,X5,X9] : (k2_zfmisc_1(k3_xboole_0(X5,X6),k4_xboole_0(k3_xboole_0(X7,X8),X9)) = k4_xboole_0(k3_xboole_0(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X8)),k2_zfmisc_1(k3_xboole_0(X5,X6),X9))) )),
% 12.56/2.03    inference(superposition,[],[f39,f40])).
% 12.56/2.03  fof(f39,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f12])).
% 12.56/2.03  fof(f12,axiom,(
% 12.56/2.03    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 12.56/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 12.56/2.03  fof(f114,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.56/2.03    inference(superposition,[],[f37,f28])).
% 12.56/2.03  fof(f9040,plain,(
% 12.56/2.03    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 12.56/2.03    inference(superposition,[],[f3370,f8465])).
% 12.56/2.03  fof(f8465,plain,(
% 12.56/2.03    ( ! [X20] : (sK1 = k4_xboole_0(sK1,X20) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f8367,f27])).
% 12.56/2.03  fof(f8367,plain,(
% 12.56/2.03    ( ! [X20] : (k4_xboole_0(sK1,X20) = k5_xboole_0(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 12.56/2.03    inference(superposition,[],[f31,f7705])).
% 12.56/2.03  fof(f7705,plain,(
% 12.56/2.03    ( ! [X11] : (k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,X11)) )),
% 12.56/2.03    inference(trivial_inequality_removal,[],[f7682])).
% 12.56/2.03  fof(f7682,plain,(
% 12.56/2.03    ( ! [X11] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = k3_xboole_0(sK1,X11)) )),
% 12.56/2.03    inference(superposition,[],[f33,f7349])).
% 12.56/2.03  fof(f7349,plain,(
% 12.56/2.03    ( ! [X11] : (k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X11))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f7322,f630])).
% 12.56/2.03  fof(f7322,plain,(
% 12.56/2.03    ( ! [X11] : (k2_zfmisc_1(k4_xboole_0(sK0,sK2),k3_xboole_0(sK1,X11)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),X11))) )),
% 12.56/2.03    inference(superposition,[],[f202,f7302])).
% 12.56/2.03  fof(f7302,plain,(
% 12.56/2.03    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 12.56/2.03    inference(forward_demodulation,[],[f7301,f26])).
% 12.56/2.03  fof(f7301,plain,(
% 12.56/2.03    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 12.56/2.03    inference(forward_demodulation,[],[f7269,f38])).
% 12.56/2.03  fof(f38,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 12.56/2.03    inference(cnf_transformation,[],[f12])).
% 12.56/2.03  fof(f7269,plain,(
% 12.56/2.03    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 12.56/2.03    inference(superposition,[],[f48,f4994])).
% 12.56/2.03  fof(f202,plain,(
% 12.56/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 12.56/2.03    inference(superposition,[],[f40,f28])).
% 12.56/2.03  fof(f33,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 12.56/2.03    inference(cnf_transformation,[],[f22])).
% 12.56/2.03  fof(f3370,plain,(
% 12.56/2.03    ( ! [X20] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k4_xboole_0(X20,k3_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X20),k2_zfmisc_1(sK0,sK1))) )),
% 12.56/2.03    inference(superposition,[],[f224,f43])).
% 12.56/2.03  fof(f224,plain,(
% 12.56/2.03    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k4_xboole_0(X4,k3_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(k3_xboole_0(X0,X1),X4),k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 12.56/2.03    inference(superposition,[],[f39,f40])).
% 12.56/2.03  fof(f1672,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 12.56/2.03    inference(forward_demodulation,[],[f1633,f27])).
% 12.56/2.03  fof(f1633,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 12.56/2.03    inference(superposition,[],[f74,f26])).
% 12.56/2.03  fof(f74,plain,(
% 12.56/2.03    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X5),X6)) = k5_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 12.56/2.03    inference(superposition,[],[f36,f31])).
% 12.56/2.03  fof(f18830,plain,(
% 12.56/2.03    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 12.56/2.03    inference(superposition,[],[f29,f17807])).
% 12.56/2.03  fof(f17807,plain,(
% 12.56/2.03    ( ! [X31,X32] : (k3_xboole_0(X32,X31) = k4_xboole_0(X31,k4_xboole_0(X31,X32))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f17738,f14977])).
% 12.56/2.03  fof(f14977,plain,(
% 12.56/2.03    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 12.56/2.03    inference(superposition,[],[f5679,f13079])).
% 12.56/2.03  fof(f13079,plain,(
% 12.56/2.03    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X16,X15)) = X15) )),
% 12.56/2.03    inference(forward_demodulation,[],[f13012,f802])).
% 12.56/2.03  fof(f802,plain,(
% 12.56/2.03    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 12.56/2.03    inference(superposition,[],[f114,f30])).
% 12.56/2.03  fof(f13012,plain,(
% 12.56/2.03    ( ! [X15,X16] : (k5_xboole_0(k4_xboole_0(X15,X16),k3_xboole_0(X15,k3_xboole_0(X16,X15))) = X15) )),
% 12.56/2.03    inference(superposition,[],[f1672,f12451])).
% 12.56/2.03  fof(f12451,plain,(
% 12.56/2.03    ( ! [X23,X22] : (k4_xboole_0(X23,k3_xboole_0(X22,X23)) = k4_xboole_0(X23,X22)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f12377,f48])).
% 12.56/2.03  fof(f12377,plain,(
% 12.56/2.03    ( ! [X23,X22] : (k4_xboole_0(X23,k3_xboole_0(X22,X23)) = k5_xboole_0(X23,k3_xboole_0(X22,X23))) )),
% 12.56/2.03    inference(superposition,[],[f48,f11990])).
% 12.56/2.03  fof(f11990,plain,(
% 12.56/2.03    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k3_xboole_0(k3_xboole_0(X8,X9),X9)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f11828,f696])).
% 12.56/2.03  fof(f11828,plain,(
% 12.56/2.03    ( ! [X8,X9] : (k3_xboole_0(k3_xboole_0(X8,X9),X9) = k4_xboole_0(k3_xboole_0(X8,X9),k1_xboole_0)) )),
% 12.56/2.03    inference(superposition,[],[f11804,f2318])).
% 12.56/2.03  fof(f2318,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f2218,f26])).
% 12.56/2.03  fof(f2218,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) )),
% 12.56/2.03    inference(superposition,[],[f124,f28])).
% 12.56/2.03  fof(f124,plain,(
% 12.56/2.03    ( ! [X4,X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X4) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,X4)))) )),
% 12.56/2.03    inference(superposition,[],[f31,f37])).
% 12.56/2.03  fof(f11804,plain,(
% 12.56/2.03    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k4_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f557,f5881])).
% 12.56/2.03  fof(f5881,plain,(
% 12.56/2.03    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 12.56/2.03    inference(superposition,[],[f5679,f31])).
% 12.56/2.03  fof(f557,plain,(
% 12.56/2.03    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,X9)) = k5_xboole_0(X8,k4_xboole_0(X8,X9))) )),
% 12.56/2.03    inference(superposition,[],[f48,f44])).
% 12.56/2.03  fof(f5679,plain,(
% 12.56/2.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 12.56/2.03    inference(backward_demodulation,[],[f72,f729])).
% 12.56/2.03  fof(f17738,plain,(
% 12.56/2.03    ( ! [X31,X32] : (k4_xboole_0(X31,k4_xboole_0(X31,X32)) = k5_xboole_0(k4_xboole_0(X31,X32),X31)) )),
% 12.56/2.03    inference(superposition,[],[f16320,f459])).
% 12.56/2.03  fof(f459,plain,(
% 12.56/2.03    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 12.56/2.03    inference(superposition,[],[f44,f30])).
% 12.56/2.03  fof(f16320,plain,(
% 12.56/2.03    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(k3_xboole_0(X2,X1),X2)) )),
% 12.56/2.03    inference(superposition,[],[f14976,f30])).
% 12.56/2.03  fof(f14976,plain,(
% 12.56/2.03    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k3_xboole_0(X2,X1),X1)) )),
% 12.56/2.03    inference(superposition,[],[f5904,f13079])).
% 12.56/2.03  fof(f5904,plain,(
% 12.56/2.03    ( ! [X14,X13] : (k5_xboole_0(X14,k5_xboole_0(X13,X14)) = X13) )),
% 12.56/2.03    inference(forward_demodulation,[],[f5885,f27])).
% 12.56/2.03  fof(f5885,plain,(
% 12.56/2.03    ( ! [X14,X13] : (k5_xboole_0(X14,k5_xboole_0(X13,X14)) = k5_xboole_0(X13,k1_xboole_0)) )),
% 12.56/2.03    inference(superposition,[],[f5679,f76])).
% 12.56/2.03  fof(f76,plain,(
% 12.56/2.03    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 12.56/2.03    inference(superposition,[],[f36,f26])).
% 12.56/2.03  fof(f25,plain,(
% 12.56/2.03    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 12.56/2.03    inference(cnf_transformation,[],[f20])).
% 12.56/2.03  fof(f19105,plain,(
% 12.56/2.03    r1_tarski(sK1,sK3)),
% 12.56/2.03    inference(superposition,[],[f18830,f10817])).
% 12.56/2.03  fof(f10817,plain,(
% 12.56/2.03    sK1 = k3_xboole_0(sK1,sK3)),
% 12.56/2.03    inference(superposition,[],[f10468,f729])).
% 12.56/2.03  fof(f10468,plain,(
% 12.56/2.03    sK1 = k5_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(superposition,[],[f1672,f7073])).
% 12.56/2.03  fof(f7073,plain,(
% 12.56/2.03    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 12.56/2.03    inference(subsumption_resolution,[],[f7072,f24])).
% 12.56/2.03  fof(f7072,plain,(
% 12.56/2.03    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 12.56/2.03    inference(forward_demodulation,[],[f7071,f50])).
% 12.56/2.03  fof(f7071,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 12.56/2.03    inference(forward_demodulation,[],[f7044,f5100])).
% 12.56/2.03  fof(f5100,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f5061,f30])).
% 12.56/2.03  fof(f5061,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1))),
% 12.56/2.03    inference(superposition,[],[f4955,f202])).
% 12.56/2.03  fof(f4955,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 12.56/2.03    inference(superposition,[],[f114,f4888])).
% 12.56/2.03  fof(f4888,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK2,sK1))),
% 12.56/2.03    inference(superposition,[],[f4874,f214])).
% 12.56/2.03  fof(f214,plain,(
% 12.56/2.03    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X5,X3),k2_zfmisc_1(X6,X4)) = k2_zfmisc_1(k3_xboole_0(X5,X6),k3_xboole_0(X4,X3))) )),
% 12.56/2.03    inference(superposition,[],[f40,f30])).
% 12.56/2.03  fof(f7044,plain,(
% 12.56/2.03    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 12.56/2.03    inference(superposition,[],[f3754,f6613])).
% 12.56/2.03  fof(f6613,plain,(
% 12.56/2.03    ( ! [X25] : (sK0 = k4_xboole_0(sK0,X25) | k1_xboole_0 = k4_xboole_0(sK1,sK3)) )),
% 12.56/2.03    inference(forward_demodulation,[],[f6518,f27])).
% 12.56/2.03  fof(f6518,plain,(
% 12.56/2.03    ( ! [X25] : (k4_xboole_0(sK0,X25) = k5_xboole_0(sK0,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK1,sK3)) )),
% 12.56/2.03    inference(superposition,[],[f48,f5746])).
% 12.56/2.03  fof(f5746,plain,(
% 12.56/2.03    ( ! [X11] : (k1_xboole_0 = k3_xboole_0(X11,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK3)) )),
% 12.56/2.03    inference(trivial_inequality_removal,[],[f5723])).
% 12.56/2.03  fof(f5723,plain,(
% 12.56/2.03    ( ! [X11] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(X11,sK0) | k1_xboole_0 = k4_xboole_0(sK1,sK3)) )),
% 12.56/2.03    inference(superposition,[],[f33,f5163])).
% 12.56/2.03  fof(f5163,plain,(
% 12.56/2.03    ( ! [X13] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f5162,f630])).
% 12.56/2.03  fof(f5162,plain,(
% 12.56/2.03    ( ! [X13] : (k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3)) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(X13,k4_xboole_0(sK1,sK3)))) )),
% 12.56/2.03    inference(forward_demodulation,[],[f5134,f30])).
% 12.56/2.03  fof(f5134,plain,(
% 12.56/2.03    ( ! [X13] : (k2_zfmisc_1(k3_xboole_0(X13,sK0),k4_xboole_0(sK1,sK3)) = k3_xboole_0(k2_zfmisc_1(X13,k4_xboole_0(sK1,sK3)),k1_xboole_0)) )),
% 12.56/2.03    inference(superposition,[],[f213,f5114])).
% 12.56/2.03  fof(f5114,plain,(
% 12.56/2.03    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f5113,f26])).
% 12.56/2.03  fof(f5113,plain,(
% 12.56/2.03    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 12.56/2.03    inference(forward_demodulation,[],[f5081,f39])).
% 12.56/2.03  fof(f5081,plain,(
% 12.56/2.03    k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 12.56/2.03    inference(superposition,[],[f48,f4955])).
% 12.56/2.03  fof(f3754,plain,(
% 12.56/2.03    ( ! [X20] : (k2_zfmisc_1(k4_xboole_0(X20,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3)) = k4_xboole_0(k2_zfmisc_1(X20,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 12.56/2.03    inference(superposition,[],[f226,f43])).
% 12.56/2.03  fof(f226,plain,(
% 12.56/2.03    ( ! [X14,X12,X10,X13,X11] : (k2_zfmisc_1(k4_xboole_0(X14,k3_xboole_0(X10,X11)),k3_xboole_0(X12,X13)) = k4_xboole_0(k2_zfmisc_1(X14,k3_xboole_0(X12,X13)),k3_xboole_0(k2_zfmisc_1(X10,X12),k2_zfmisc_1(X11,X13)))) )),
% 12.56/2.03    inference(superposition,[],[f38,f40])).
% 12.56/2.03  % SZS output end Proof for theBenchmark
% 12.56/2.03  % (4402)------------------------------
% 12.56/2.03  % (4402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.56/2.03  % (4402)Termination reason: Refutation
% 12.56/2.03  
% 12.56/2.03  % (4402)Memory used [KB]: 11897
% 12.56/2.03  % (4402)Time elapsed: 1.056 s
% 12.56/2.03  % (4402)------------------------------
% 12.56/2.03  % (4402)------------------------------
% 12.96/2.04  % (4268)Success in time 1.665 s
%------------------------------------------------------------------------------
