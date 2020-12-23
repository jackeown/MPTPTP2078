%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:55 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 864 expanded)
%              Number of leaves         :   24 ( 246 expanded)
%              Depth                    :   28
%              Number of atoms          :  228 (2108 expanded)
%              Number of equality atoms :  108 ( 718 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(subsumption_resolution,[],[f224,f103])).

fof(f103,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f79,f100])).

fof(f100,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f82,f91])).

fof(f91,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f88,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f88,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f86,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f85,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f43])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f82,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f41,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f79,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f224,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f223,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f223,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f222,f137])).

fof(f137,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f136,f46])).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f136,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f72,f96])).

fof(f96,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f73,f88])).

fof(f73,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f48,f52,f71])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f222,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f221,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f221,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f152,f220])).

fof(f220,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f219,f111])).

fof(f111,plain,(
    ! [X1] : k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f107,f47])).

fof(f107,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f67,f91])).

fof(f67,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f219,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f208,f131])).

fof(f131,plain,(
    sK1 = k4_subset_1(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f128,f96])).

fof(f128,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) = k4_subset_1(sK0,sK1,sK1) ),
    inference(resolution,[],[f81,f41])).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X1,sK1) = k3_tarski(k2_enumset1(X1,X1,X1,sK1)) ) ),
    inference(resolution,[],[f41,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f208,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k4_subset_1(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f164,f206])).

fof(f206,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f197,f45])).

fof(f197,plain,(
    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f139,f137])).

fof(f139,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f66,f137])).

fof(f164,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1)))) ),
    inference(backward_demodulation,[],[f153,f163])).

fof(f163,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f162,f147])).

fof(f147,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f66,f146])).

fof(f146,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f145,f46])).

fof(f145,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f72,f109])).

fof(f109,plain,(
    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f73,f91])).

fof(f162,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f117,f154])).

fof(f154,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f126,f47])).

fof(f126,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f124,f58])).

fof(f124,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(resolution,[],[f120,f78])).

fof(f120,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,
    ( r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f114,f54])).

fof(f114,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f113,f41])).

fof(f113,plain,
    ( m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f59,f100])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f117,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f114,f75])).

fof(f153,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f150,f143])).

fof(f143,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f121,f114])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0)) ) ),
    inference(resolution,[],[f80,f59])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0) ) ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f150,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))))) ),
    inference(resolution,[],[f130,f114])).

fof(f130,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_subset_1(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,X0)))) ) ),
    inference(forward_demodulation,[],[f127,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f53,f71,f52])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f127,plain,(
    ! [X0] :
      ( k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f81,f59])).

fof(f152,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f151,f123])).

fof(f123,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f80,f114])).

fof(f151,plain,(
    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f149,f100])).

fof(f149,plain,(
    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))) ),
    inference(resolution,[],[f130,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (20480)Refutation not found, incomplete strategy% (20480)------------------------------
% 0.22/0.52  % (20480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (20488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (20480)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20480)Memory used [KB]: 6140
% 0.22/0.52  % (20480)Time elapsed: 0.006 s
% 0.22/0.52  % (20480)------------------------------
% 0.22/0.52  % (20480)------------------------------
% 0.22/0.52  % (20472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (20473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (20469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (20479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.54  % (20474)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.54  % (20466)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.54  % (20468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (20494)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.54  % (20492)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (20473)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f225,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(subsumption_resolution,[],[f224,f103])).
% 1.32/0.54  fof(f103,plain,(
% 1.32/0.54    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(backward_demodulation,[],[f79,f100])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.32/0.54    inference(backward_demodulation,[],[f82,f91])).
% 1.32/0.54  fof(f91,plain,(
% 1.32/0.54    sK1 = k3_xboole_0(sK0,sK1)),
% 1.32/0.54    inference(superposition,[],[f88,f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.32/0.54  fof(f88,plain,(
% 1.32/0.54    sK1 = k3_xboole_0(sK1,sK0)),
% 1.32/0.54    inference(resolution,[],[f86,f58])).
% 1.32/0.54  fof(f58,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.32/0.54  fof(f86,plain,(
% 1.32/0.54    r1_tarski(sK1,sK0)),
% 1.32/0.54    inference(resolution,[],[f85,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f61])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.54    inference(rectify,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.32/0.54    inference(nnf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,axiom,(
% 1.32/0.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.32/0.54  fof(f85,plain,(
% 1.32/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f83,f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f20])).
% 1.32/0.54  fof(f20,axiom,(
% 1.32/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.32/0.54  fof(f83,plain,(
% 1.32/0.54    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(resolution,[],[f41,f54])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.32/0.54    inference(nnf_transformation,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,axiom,(
% 1.32/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.32/0.54    inference(negated_conjecture,[],[f22])).
% 1.32/0.54  fof(f22,conjecture,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.32/0.54  fof(f82,plain,(
% 1.32/0.54    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(resolution,[],[f41,f75])).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f60,f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f18])).
% 1.32/0.54  fof(f18,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.32/0.54  fof(f79,plain,(
% 1.32/0.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.32/0.54    inference(forward_demodulation,[],[f42,f44])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,axiom,(
% 1.32/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.32/0.54    inference(cnf_transformation,[],[f35])).
% 1.32/0.54  fof(f224,plain,(
% 1.32/0.54    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(forward_demodulation,[],[f223,f45])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.32/0.54  fof(f223,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.32/0.54    inference(forward_demodulation,[],[f222,f137])).
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f136,f46])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    inference(rectify,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.32/0.54  fof(f136,plain,(
% 1.32/0.54    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),
% 1.32/0.54    inference(superposition,[],[f72,f96])).
% 1.32/0.54  fof(f96,plain,(
% 1.32/0.54    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    inference(superposition,[],[f73,f88])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.32/0.54    inference(definition_unfolding,[],[f49,f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f50,f70])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f51,f65])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,axiom,(
% 1.32/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f48,f52,f71])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.32/0.54  fof(f222,plain,(
% 1.32/0.54    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(forward_demodulation,[],[f221,f66])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.32/0.54  fof(f221,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.32/0.54    inference(backward_demodulation,[],[f152,f220])).
% 1.32/0.54  fof(f220,plain,(
% 1.32/0.54    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.32/0.54    inference(forward_demodulation,[],[f219,f111])).
% 1.32/0.54  fof(f111,plain,(
% 1.32/0.54    ( ! [X1] : (k5_xboole_0(sK1,k3_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) )),
% 1.32/0.54    inference(forward_demodulation,[],[f107,f47])).
% 1.32/0.54  fof(f107,plain,(
% 1.32/0.54    ( ! [X1] : (k3_xboole_0(k5_xboole_0(sK0,X1),sK1) = k5_xboole_0(sK1,k3_xboole_0(X1,sK1))) )),
% 1.32/0.54    inference(superposition,[],[f67,f91])).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.32/0.54  fof(f219,plain,(
% 1.32/0.54    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)))),
% 1.32/0.54    inference(forward_demodulation,[],[f208,f131])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    sK1 = k4_subset_1(sK0,sK1,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f128,f96])).
% 1.32/0.54  fof(f128,plain,(
% 1.32/0.54    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) = k4_subset_1(sK0,sK1,sK1)),
% 1.32/0.54    inference(resolution,[],[f81,f41])).
% 1.32/0.54  fof(f81,plain,(
% 1.32/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X1,sK1) = k3_tarski(k2_enumset1(X1,X1,X1,sK1))) )),
% 1.32/0.54    inference(resolution,[],[f41,f76])).
% 1.32/0.54  fof(f76,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f68,f71])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(flattening,[],[f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.32/0.54    inference(ennf_transformation,[],[f21])).
% 1.32/0.54  fof(f21,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.32/0.54  fof(f208,plain,(
% 1.32/0.54    k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k4_subset_1(sK0,sK1,sK1)),
% 1.32/0.54    inference(backward_demodulation,[],[f164,f206])).
% 1.32/0.54  fof(f206,plain,(
% 1.32/0.54    sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f197,f45])).
% 1.32/0.54  fof(f197,plain,(
% 1.32/0.54    k5_xboole_0(k1_xboole_0,sK1) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.32/0.54    inference(superposition,[],[f139,f137])).
% 1.32/0.54  fof(f139,plain,(
% 1.32/0.54    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.54    inference(superposition,[],[f66,f137])).
% 1.32/0.54  fof(f164,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k5_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k1_xboole_0,sK1))))),
% 1.32/0.54    inference(backward_demodulation,[],[f153,f163])).
% 1.32/0.54  fof(f163,plain,(
% 1.32/0.54    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k1_xboole_0,sK1)),
% 1.32/0.54    inference(forward_demodulation,[],[f162,f147])).
% 1.32/0.54  fof(f147,plain,(
% 1.32/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,X0))) )),
% 1.32/0.54    inference(superposition,[],[f66,f146])).
% 1.32/0.54  fof(f146,plain,(
% 1.32/0.54    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.32/0.54    inference(forward_demodulation,[],[f145,f46])).
% 1.32/0.54  fof(f145,plain,(
% 1.32/0.54    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))),
% 1.32/0.54    inference(superposition,[],[f72,f109])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.32/0.54    inference(superposition,[],[f73,f91])).
% 1.32/0.54  fof(f162,plain,(
% 1.32/0.54    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(backward_demodulation,[],[f117,f154])).
% 1.32/0.54  fof(f154,plain,(
% 1.32/0.54    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(superposition,[],[f126,f47])).
% 1.32/0.54  fof(f126,plain,(
% 1.32/0.54    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 1.32/0.54    inference(resolution,[],[f124,f58])).
% 1.32/0.54  fof(f124,plain,(
% 1.32/0.54    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 1.32/0.54    inference(resolution,[],[f120,f78])).
% 1.32/0.54  fof(f120,plain,(
% 1.32/0.54    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f118,f43])).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(resolution,[],[f114,f54])).
% 1.32/0.54  fof(f114,plain,(
% 1.32/0.54    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f113,f41])).
% 1.32/0.54  fof(f113,plain,(
% 1.32/0.54    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.32/0.54    inference(superposition,[],[f59,f100])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))) = k3_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 1.32/0.54    inference(resolution,[],[f114,f75])).
% 1.32/0.54  fof(f153,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))))),
% 1.32/0.54    inference(forward_demodulation,[],[f150,f143])).
% 1.32/0.54  fof(f143,plain,(
% 1.32/0.54    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f121,f114])).
% 1.32/0.54  fof(f121,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,X0))) )),
% 1.32/0.54    inference(resolution,[],[f80,f59])).
% 1.32/0.54  fof(f80,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)) )),
% 1.32/0.54    inference(resolution,[],[f41,f69])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(flattening,[],[f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.32/0.54    inference(ennf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 1.32/0.54  fof(f150,plain,(
% 1.32/0.54    k4_subset_1(sK0,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),sK1) = k5_xboole_0(k3_subset_1(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))))),
% 1.32/0.54    inference(resolution,[],[f130,f114])).
% 1.32/0.54  fof(f130,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k5_xboole_0(k3_subset_1(sK0,X0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,X0))))) )),
% 1.32/0.54    inference(forward_demodulation,[],[f127,f74])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.32/0.54    inference(definition_unfolding,[],[f53,f71,f52])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.32/0.54  fof(f127,plain,(
% 1.32/0.54    ( ! [X0] : (k4_subset_1(sK0,k3_subset_1(sK0,X0),sK1) = k3_tarski(k2_enumset1(k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),k3_subset_1(sK0,X0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.32/0.54    inference(resolution,[],[f81,f59])).
% 1.32/0.54  fof(f152,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 1.32/0.54    inference(forward_demodulation,[],[f151,f123])).
% 1.32/0.54  fof(f123,plain,(
% 1.32/0.54    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1)),
% 1.32/0.54    inference(resolution,[],[f80,f114])).
% 1.32/0.54  fof(f151,plain,(
% 1.32/0.54    k4_subset_1(sK0,k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),
% 1.32/0.54    inference(forward_demodulation,[],[f149,f100])).
% 1.32/0.54  fof(f149,plain,(
% 1.32/0.54    k4_subset_1(sK0,k3_subset_1(sK0,sK1),sK1) = k5_xboole_0(k3_subset_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_subset_1(sK0,sK1))))),
% 1.32/0.54    inference(resolution,[],[f130,f41])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (20473)------------------------------
% 1.32/0.54  % (20473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (20473)Termination reason: Refutation
% 1.32/0.55  
% 1.32/0.55  % (20473)Memory used [KB]: 10874
% 1.32/0.55  % (20473)Time elapsed: 0.128 s
% 1.32/0.55  % (20473)------------------------------
% 1.32/0.55  % (20473)------------------------------
% 1.32/0.55  % (20475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  % (20487)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.55  % (20465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.55  % (20493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.55  % (20485)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (20487)Refutation not found, incomplete strategy% (20487)------------------------------
% 1.32/0.55  % (20487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (20487)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (20487)Memory used [KB]: 10746
% 1.32/0.55  % (20487)Time elapsed: 0.142 s
% 1.32/0.55  % (20487)------------------------------
% 1.32/0.55  % (20487)------------------------------
% 1.38/0.55  % (20489)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (20467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  % (20490)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (20486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (20484)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (20483)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.56  % (20471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.56  % (20491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.56  % (20482)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.56  % (20478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.56  % (20482)Refutation not found, incomplete strategy% (20482)------------------------------
% 1.38/0.56  % (20482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (20482)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (20482)Memory used [KB]: 10618
% 1.38/0.56  % (20482)Time elapsed: 0.148 s
% 1.38/0.56  % (20482)------------------------------
% 1.38/0.56  % (20482)------------------------------
% 1.38/0.56  % (20476)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (20481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.56  % (20477)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.57  % (20464)Success in time 0.2 s
%------------------------------------------------------------------------------
