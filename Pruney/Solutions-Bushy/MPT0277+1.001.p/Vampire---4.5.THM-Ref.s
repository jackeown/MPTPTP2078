%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0277+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 411 expanded)
%              Number of leaves         :    4 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          :  117 (1568 expanded)
%              Number of equality atoms :  102 (1371 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f13])).

fof(f13,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f143,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(forward_demodulation,[],[f139,f138])).

fof(f138,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f127,f108])).

fof(f108,plain,
    ( sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f103,f64])).

fof(f64,plain,
    ( sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f63])).

fof(f63,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | sK0 != sK0
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f11,f38])).

fof(f38,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f37,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f15,f12])).

fof(f12,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f11,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f28,f38])).

fof(f28,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k2_tarski(X6,X7),k2_tarski(X6,X7)) ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f103,plain,
    ( sK0 != k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f10,f66])).

fof(f66,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(X1,sK2))
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f26,f64])).

fof(f26,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k1_tarski(X2),k2_tarski(X3,X2)) ),
    inference(resolution,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f127,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k1_tarski(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f9,f111])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,X0))
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f27,f108])).

fof(f27,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k1_tarski(X4),k2_tarski(X4,X5)) ),
    inference(resolution,[],[f14,f23])).

fof(f23,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f139,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f8,f138])).

fof(f8,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
