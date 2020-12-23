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
% DateTime   : Thu Dec  3 12:43:56 EST 2020

% Result     : Theorem 34.10s
% Output     : Refutation 34.10s
% Verified   : 
% Statistics : Number of formulae       :  234 (17608 expanded)
%              Number of leaves         :   28 (5036 expanded)
%              Depth                    :   55
%              Number of atoms          :  475 (55665 expanded)
%              Number of equality atoms :  173 (16355 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14762,plain,(
    $false ),
    inference(subsumption_resolution,[],[f14761,f204])).

fof(f204,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f104,f203])).

fof(f203,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f191,f194])).

fof(f194,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f147,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f147,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f129,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f129,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f126,f100])).

fof(f100,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f126,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f46,f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f48,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f191,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f47,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f14761,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f8278,f14747])).

fof(f14747,plain,(
    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(superposition,[],[f14249,f147])).

fof(f14249,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = X0 ),
    inference(backward_demodulation,[],[f3339,f14248])).

fof(f14248,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5)))) = X5 ),
    inference(forward_demodulation,[],[f14143,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f14143,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5)))) ),
    inference(superposition,[],[f546,f5229])).

fof(f5229,plain,(
    ! [X10,X9] : k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9))) ),
    inference(subsumption_resolution,[],[f3754,f5212])).

fof(f5212,plain,(
    ! [X37,X38,X36] :
      ( r2_hidden(sK3(X36,X36,k3_xboole_0(X37,X38)),X37)
      | k1_xboole_0 = k3_xboole_0(X37,X38) ) ),
    inference(resolution,[],[f5177,f3741])).

fof(f3741,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(backward_demodulation,[],[f570,f3660])).

fof(f3660,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f1103,f3637])).

fof(f3637,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f981,f2925])).

fof(f2925,plain,(
    ! [X94,X95] :
      ( r2_hidden(sK3(k1_xboole_0,X94,X95),X95)
      | k1_xboole_0 = X95 ) ),
    inference(forward_demodulation,[],[f2924,f2905])).

fof(f2905,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f2430,f63])).

fof(f2430,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(superposition,[],[f2089,f50])).

fof(f2089,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,X0),X1) ),
    inference(superposition,[],[f1944,f1103])).

fof(f1944,plain,(
    ! [X4] : r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)),X4) ),
    inference(superposition,[],[f116,f1103])).

fof(f116,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f89,f51])).

fof(f51,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2924,plain,(
    ! [X94,X95] :
      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X94)) = X95
      | r2_hidden(sK3(k1_xboole_0,X94,X95),X95) ) ),
    inference(forward_demodulation,[],[f2921,f2905])).

fof(f2921,plain,(
    ! [X94,X95,X93] :
      ( r2_hidden(sK3(k1_xboole_0,X94,X95),X95)
      | k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95 ) ),
    inference(backward_demodulation,[],[f2862,f2905])).

fof(f2862,plain,(
    ! [X94,X95,X93] :
      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95
      | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95) ) ),
    inference(forward_demodulation,[],[f2861,f546])).

fof(f2861,plain,(
    ! [X94,X95,X93] :
      ( k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95
      | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95) ) ),
    inference(forward_demodulation,[],[f2860,f105])).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f54,f50])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2860,plain,(
    ! [X94,X95,X93] :
      ( r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95)
      | k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94))) = X95 ) ),
    inference(subsumption_resolution,[],[f2723,f312])).

fof(f312,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f146,f50])).

fof(f146,plain,(
    ! [X0,X1] : ~ r2_hidden(X1,k5_xboole_0(X0,X0)) ),
    inference(subsumption_resolution,[],[f142,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f102,f51])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f74,f57])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f103,f51])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f73,f57])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2723,plain,(
    ! [X94,X95,X93] :
      ( r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95)
      | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),k1_xboole_0)
      | k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94))) = X95 ) ),
    inference(superposition,[],[f632,f105])).

fof(f632,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11)
      | r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X8)
      | k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10))) = X11 ) ),
    inference(forward_demodulation,[],[f631,f546])).

fof(f631,plain,(
    ! [X10,X8,X11,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10))) = X11
      | r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11)
      | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8) ) ),
    inference(forward_demodulation,[],[f593,f546])).

fof(f593,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11)
      | k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10))) = X11
      | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8) ) ),
    inference(backward_demodulation,[],[f271,f546])).

fof(f271,plain,(
    ! [X10,X8,X11,X9] :
      ( k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10))) = X11
      | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X11)
      | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8) ) ),
    inference(forward_demodulation,[],[f265,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f265,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X11)
      | k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10)) = X11
      | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8) ) ),
    inference(resolution,[],[f95,f103])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f76,f57])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f981,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f980,f233])).

fof(f233,plain,(
    ! [X1] : k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f232,f53])).

fof(f232,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f225,f187])).

fof(f187,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f171,f53])).

fof(f171,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f71,f51])).

fof(f71,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f225,plain,(
    ! [X1] : k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1) ),
    inference(superposition,[],[f71,f194])).

fof(f980,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f966,f388])).

fof(f388,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X2,k5_xboole_0(X3,X2)))
      | r2_hidden(X4,X2) ) ),
    inference(superposition,[],[f184,f54])).

fof(f184,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X2,k5_xboole_0(X2,X3)))
      | r2_hidden(X4,X2) ) ),
    inference(backward_demodulation,[],[f143,f183])).

fof(f183,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f168,f53])).

fof(f168,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f71,f51])).

fof(f143,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2)))
      | r2_hidden(X4,X2) ) ),
    inference(superposition,[],[f103,f53])).

fof(f966,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f582,f548])).

fof(f548,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f183,f147])).

fof(f582,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_xboole_0(X4,k3_xboole_0(X3,k5_xboole_0(X3,X4))))
      | ~ r2_hidden(X5,X4) ) ),
    inference(backward_demodulation,[],[f189,f546])).

fof(f189,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_xboole_0(X4,k5_xboole_0(X3,k3_xboole_0(X3,X4))))
      | ~ r2_hidden(X5,X4) ) ),
    inference(forward_demodulation,[],[f177,f53])).

fof(f177,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4))
      | ~ r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f102,f71])).

fof(f1103,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f981,f570])).

fof(f570,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,X0) = X1 ) ),
    inference(backward_demodulation,[],[f270,f545])).

fof(f545,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k3_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f183,f51])).

fof(f270,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k5_xboole_0(X0,X0)) = X1
      | r2_hidden(sK3(X0,X0,X1),X1) ) ),
    inference(forward_demodulation,[],[f268,f183])).

fof(f268,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
      | r2_hidden(sK3(X0,X0,X1),X1) ) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f77,f57])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5177,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,k3_xboole_0(X3,X2))
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f5036,f53])).

fof(f5036,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k3_xboole_0(X6,X7))
      | r2_hidden(X8,X7) ) ),
    inference(subsumption_resolution,[],[f585,f5034])).

fof(f5034,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8)))) ),
    inference(forward_demodulation,[],[f5033,f183])).

fof(f5033,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f5032,f54])).

fof(f5032,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X9))) ),
    inference(forward_demodulation,[],[f5031,f3912])).

fof(f3912,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(X7,X8)) = X8 ),
    inference(forward_demodulation,[],[f3674,f105])).

fof(f3674,plain,(
    ! [X8,X7] : k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X7,k5_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f1945,f3637])).

fof(f1945,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k5_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)),X8) ),
    inference(superposition,[],[f70,f1103])).

fof(f5031,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X9))))) ),
    inference(forward_demodulation,[],[f5030,f458])).

fof(f458,plain,(
    ! [X19,X17,X18,X16] : k5_xboole_0(X18,k5_xboole_0(X17,k5_xboole_0(X16,X19))) = k5_xboole_0(X18,k5_xboole_0(X16,k5_xboole_0(X17,X19))) ),
    inference(forward_demodulation,[],[f457,f70])).

fof(f457,plain,(
    ! [X19,X17,X18,X16] : k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X16,X17),X19)) = k5_xboole_0(X18,k5_xboole_0(X17,k5_xboole_0(X16,X19))) ),
    inference(forward_demodulation,[],[f429,f456])).

fof(f456,plain,(
    ! [X14,X12,X15,X13] : k5_xboole_0(k5_xboole_0(X13,k5_xboole_0(X12,X14)),X15) = k5_xboole_0(X14,k5_xboole_0(X12,k5_xboole_0(X13,X15))) ),
    inference(forward_demodulation,[],[f428,f70])).

fof(f428,plain,(
    ! [X14,X12,X15,X13] : k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X12,X13),X15)) = k5_xboole_0(k5_xboole_0(X13,k5_xboole_0(X12,X14)),X15) ),
    inference(superposition,[],[f152,f152])).

fof(f152,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f70,f54])).

fof(f429,plain,(
    ! [X19,X17,X18,X16] : k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X16,X17),X19)) = k5_xboole_0(k5_xboole_0(X16,k5_xboole_0(X17,X18)),X19) ),
    inference(superposition,[],[f152,f70])).

fof(f5030,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))))) ),
    inference(forward_demodulation,[],[f5029,f3912])).

fof(f5029,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9))))))) ),
    inference(forward_demodulation,[],[f5028,f562])).

fof(f562,plain,(
    ! [X21,X22,X20] : k5_xboole_0(X20,k5_xboole_0(k3_xboole_0(X21,X20),X22)) = k5_xboole_0(X22,k3_xboole_0(X20,k5_xboole_0(X20,X21))) ),
    inference(superposition,[],[f157,f183])).

fof(f157,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f70,f54])).

fof(f5028,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X9,k5_xboole_0(X9,X8))))))) ),
    inference(forward_demodulation,[],[f5027,f157])).

fof(f5027,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),X9))))) ),
    inference(forward_demodulation,[],[f5026,f458])).

fof(f5026,plain,(
    ! [X10,X8,X9] : ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9))))) ),
    inference(subsumption_resolution,[],[f5025,f184])).

fof(f5025,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9)))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5024,f183])).

fof(f5024,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k3_xboole_0(k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9)),X8)))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5023,f169])).

fof(f169,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f71,f53])).

fof(f5023,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5022,f54])).

fof(f5022,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8),k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5021,f910])).

fof(f910,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5))) = k3_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X5,k5_xboole_0(X5,X6))) ),
    inference(forward_demodulation,[],[f909,f183])).

fof(f909,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f908,f546])).

fof(f908,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5))) ),
    inference(forward_demodulation,[],[f907,f54])).

fof(f907,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k5_xboole_0(k3_xboole_0(X6,X5),X6)) ),
    inference(forward_demodulation,[],[f878,f53])).

fof(f878,plain,(
    ! [X6,X5] : k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X6,X5),X6),X5) ),
    inference(superposition,[],[f169,f187])).

fof(f5021,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8),k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5020,f54])).

fof(f5020,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5019,f892])).

fof(f892,plain,(
    ! [X35,X33,X36,X34] : k5_xboole_0(k3_xboole_0(X35,X33),k5_xboole_0(X36,k3_xboole_0(X33,X34))) = k5_xboole_0(X36,k3_xboole_0(k5_xboole_0(X34,X35),X33)) ),
    inference(superposition,[],[f157,f169])).

fof(f5019,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,X8),k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5018,f458])).

fof(f5018,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5017,f54])).

fof(f5017,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f5016,f157])).

fof(f5016,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(forward_demodulation,[],[f4943,f473])).

fof(f473,plain,(
    ! [X30,X28,X29] : k5_xboole_0(k3_xboole_0(X28,X29),k5_xboole_0(X30,k5_xboole_0(X28,X29))) = k5_xboole_0(X30,k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29))) ),
    inference(superposition,[],[f157,f90])).

fof(f90,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f58,f88])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f79,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f80,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f81,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f4943,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k5_xboole_0(X8,k3_tarski(k6_enumset1(k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))))))
      | ~ r2_hidden(X10,X8) ) ),
    inference(superposition,[],[f3929,f183])).

fof(f3929,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3)))))
      | ~ r2_hidden(X5,X4) ) ),
    inference(backward_demodulation,[],[f1822,f3925])).

fof(f3925,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X15,X14)) = X15 ),
    inference(forward_demodulation,[],[f3676,f50])).

fof(f3676,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X15,X14)) = k5_xboole_0(X15,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1948,f3637])).

fof(f1948,plain,(
    ! [X14,X15] : k5_xboole_0(X14,k5_xboole_0(X15,X14)) = k5_xboole_0(X15,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f157,f1103])).

fof(f1822,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k5_xboole_0(X3,k5_xboole_0(X4,X3)))
      | ~ r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3))))) ) ),
    inference(forward_demodulation,[],[f1788,f54])).

fof(f1788,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3)))))
      | ~ r2_hidden(X5,k5_xboole_0(k5_xboole_0(X4,X3),X3)) ) ),
    inference(superposition,[],[f163,f250])).

fof(f250,plain,(
    ! [X2,X3] : k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f243,f183])).

fof(f243,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(superposition,[],[f90,f70])).

fof(f163,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r2_hidden(X15,k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(k5_xboole_0(X12,X13),X14))))
      | ~ r2_hidden(X15,X14) ) ),
    inference(superposition,[],[f102,f70])).

fof(f585,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X8,k3_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X6,X7))))
      | r2_hidden(X8,X7)
      | ~ r2_hidden(X8,k3_xboole_0(X6,X7)) ) ),
    inference(backward_demodulation,[],[f220,f546])).

fof(f220,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X8,k3_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7))))
      | r2_hidden(X8,X7)
      | ~ r2_hidden(X8,k3_xboole_0(X6,X7)) ) ),
    inference(forward_demodulation,[],[f214,f53])).

fof(f214,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X8,k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7))
      | r2_hidden(X8,X7)
      | ~ r2_hidden(X8,k3_xboole_0(X6,X7)) ) ),
    inference(superposition,[],[f101,f71])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f75,f57])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3754,plain,(
    ! [X10,X8,X9] :
      ( k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))
      | ~ r2_hidden(sK3(X8,X8,k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))),X9) ) ),
    inference(backward_demodulation,[],[f796,f3660])).

fof(f796,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(sK3(X8,X8,k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))),X9)
      | k5_xboole_0(X8,X8) = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9))) ) ),
    inference(resolution,[],[f582,f570])).

fof(f546,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f183,f53])).

fof(f3339,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f3338,f546])).

fof(f3338,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f3337,f54])).

fof(f3337,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1))) ),
    inference(forward_demodulation,[],[f3336,f157])).

fof(f3336,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f3335,f53])).

fof(f3335,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f3334,f71])).

fof(f3334,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X0),X0),k3_xboole_0(k5_xboole_0(X1,X0),X0)) ),
    inference(forward_demodulation,[],[f3267,f54])).

fof(f3267,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X1,X0),X0),k3_xboole_0(k3_xboole_0(X1,X0),X0)) ),
    inference(superposition,[],[f238,f51])).

fof(f238,plain,(
    ! [X6,X7,X5] : k3_tarski(k6_enumset1(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X7,X6))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X5,X7),X6),k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X7,X6))) ),
    inference(superposition,[],[f90,f71])).

fof(f8278,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(forward_demodulation,[],[f8096,f352])).

fof(f352,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f46,f302,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f88])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f302,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f254,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f254,plain,(
    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f226,f99])).

fof(f99,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f226,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f89,f194])).

fof(f8096,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f5299,f548])).

fof(f5299,plain,(
    ! [X15,X16] : k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)) = k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) ),
    inference(forward_demodulation,[],[f5250,f50])).

fof(f5250,plain,(
    ! [X15,X16] : k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1791,f5229])).

fof(f1791,plain,(
    ! [X15,X16] : k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k3_xboole_0(X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) ),
    inference(superposition,[],[f90,f250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8050)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (8041)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (8066)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.53  % (8040)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (8039)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (8035)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (8047)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (8047)Refutation not found, incomplete strategy% (8047)------------------------------
% 1.29/0.54  % (8047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (8047)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (8047)Memory used [KB]: 10618
% 1.29/0.54  % (8047)Time elapsed: 0.127 s
% 1.29/0.54  % (8047)------------------------------
% 1.29/0.54  % (8047)------------------------------
% 1.29/0.54  % (8062)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.54  % (8049)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (8038)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.54  % (8065)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (8063)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (8058)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.54  % (8060)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % (8064)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (8037)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.55  % (8055)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (8052)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.41/0.55  % (8048)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (8046)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (8057)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (8045)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (8043)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (8046)Refutation not found, incomplete strategy% (8046)------------------------------
% 1.41/0.56  % (8046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (8053)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.56  % (8053)Refutation not found, incomplete strategy% (8053)------------------------------
% 1.41/0.56  % (8053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (8053)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (8053)Memory used [KB]: 10618
% 1.41/0.56  % (8053)Time elapsed: 0.159 s
% 1.41/0.56  % (8053)------------------------------
% 1.41/0.56  % (8053)------------------------------
% 1.41/0.57  % (8061)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.57  % (8056)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.57  % (8044)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.57  % (8046)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (8046)Memory used [KB]: 10618
% 1.41/0.57  % (8046)Time elapsed: 0.148 s
% 1.41/0.57  % (8046)------------------------------
% 1.41/0.57  % (8046)------------------------------
% 1.41/0.59  % (8059)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.60  % (8059)Refutation not found, incomplete strategy% (8059)------------------------------
% 1.41/0.60  % (8059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (8059)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.60  
% 1.41/0.60  % (8059)Memory used [KB]: 10746
% 1.41/0.60  % (8059)Time elapsed: 0.100 s
% 1.41/0.60  % (8059)------------------------------
% 1.41/0.60  % (8059)------------------------------
% 1.41/0.61  % (8051)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.62  % (8042)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.40/0.74  % (8087)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.40/0.75  % (8090)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.91/0.76  % (8071)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.33/0.83  % (8041)Time limit reached!
% 3.33/0.83  % (8041)------------------------------
% 3.33/0.83  % (8041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.33/0.83  % (8041)Termination reason: Time limit
% 3.33/0.83  
% 3.33/0.83  % (8041)Memory used [KB]: 8571
% 3.33/0.83  % (8041)Time elapsed: 0.403 s
% 3.33/0.83  % (8041)------------------------------
% 3.33/0.83  % (8041)------------------------------
% 3.51/0.88  % (8094)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 3.51/0.92  % (8035)Time limit reached!
% 3.51/0.92  % (8035)------------------------------
% 3.51/0.92  % (8035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.92  % (8035)Termination reason: Time limit
% 3.51/0.92  % (8035)Termination phase: Saturation
% 3.51/0.92  
% 3.51/0.92  % (8035)Memory used [KB]: 4221
% 3.51/0.92  % (8035)Time elapsed: 0.500 s
% 3.51/0.92  % (8035)------------------------------
% 3.51/0.92  % (8035)------------------------------
% 3.51/0.92  % (8037)Time limit reached!
% 3.51/0.92  % (8037)------------------------------
% 3.51/0.92  % (8037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.92  % (8037)Termination reason: Time limit
% 3.51/0.92  % (8037)Termination phase: Saturation
% 3.51/0.92  
% 3.51/0.92  % (8037)Memory used [KB]: 7675
% 3.51/0.92  % (8037)Time elapsed: 0.500 s
% 3.51/0.92  % (8037)------------------------------
% 3.51/0.92  % (8037)------------------------------
% 4.10/0.93  % (8048)Time limit reached!
% 4.10/0.93  % (8048)------------------------------
% 4.10/0.93  % (8048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.93  % (8048)Termination reason: Time limit
% 4.10/0.93  % (8048)Termination phase: Saturation
% 4.10/0.93  
% 4.10/0.93  % (8048)Memory used [KB]: 9338
% 4.10/0.93  % (8048)Time elapsed: 0.522 s
% 4.10/0.93  % (8048)------------------------------
% 4.10/0.93  % (8048)------------------------------
% 4.10/0.97  % (8096)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.46/1.01  % (8052)Time limit reached!
% 4.46/1.01  % (8052)------------------------------
% 4.46/1.01  % (8052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/1.01  % (8052)Termination reason: Time limit
% 4.46/1.01  
% 4.46/1.01  % (8052)Memory used [KB]: 14711
% 4.46/1.01  % (8052)Time elapsed: 0.607 s
% 4.46/1.01  % (8052)------------------------------
% 4.46/1.01  % (8052)------------------------------
% 4.46/1.02  % (8043)Time limit reached!
% 4.46/1.02  % (8043)------------------------------
% 4.46/1.02  % (8043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/1.02  % (8043)Termination reason: Time limit
% 4.46/1.02  % (8043)Termination phase: Saturation
% 4.46/1.02  
% 4.46/1.02  % (8043)Memory used [KB]: 9850
% 4.46/1.02  % (8043)Time elapsed: 0.600 s
% 4.46/1.02  % (8043)------------------------------
% 4.46/1.02  % (8043)------------------------------
% 4.46/1.03  % (8065)Time limit reached!
% 4.46/1.03  % (8065)------------------------------
% 4.46/1.03  % (8065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/1.03  % (8065)Termination reason: Time limit
% 4.46/1.03  % (8065)Termination phase: Saturation
% 4.46/1.03  
% 4.46/1.03  % (8065)Memory used [KB]: 9083
% 4.46/1.03  % (8065)Time elapsed: 0.600 s
% 4.46/1.03  % (8065)------------------------------
% 4.46/1.03  % (8065)------------------------------
% 4.88/1.05  % (8094)Time limit reached!
% 4.88/1.05  % (8094)------------------------------
% 4.88/1.05  % (8094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.88/1.05  % (8094)Termination reason: Time limit
% 4.88/1.05  % (8094)Termination phase: Saturation
% 4.88/1.05  
% 4.88/1.05  % (8094)Memory used [KB]: 6268
% 4.88/1.05  % (8094)Time elapsed: 0.400 s
% 4.88/1.05  % (8094)------------------------------
% 4.88/1.05  % (8094)------------------------------
% 4.88/1.07  % (8101)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.63/1.08  % (8100)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.63/1.10  % (8102)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.02/1.14  % (8104)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.02/1.14  % (8103)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.23/1.17  % (8107)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.23/1.17  % (8106)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.23/1.21  % (8058)Time limit reached!
% 6.23/1.21  % (8058)------------------------------
% 6.23/1.21  % (8058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.23/1.22  % (8058)Termination reason: Time limit
% 6.23/1.22  
% 6.23/1.22  % (8058)Memory used [KB]: 6908
% 6.23/1.22  % (8058)Time elapsed: 0.813 s
% 6.23/1.22  % (8058)------------------------------
% 6.23/1.22  % (8058)------------------------------
% 6.81/1.25  % (8096)Time limit reached!
% 6.81/1.25  % (8096)------------------------------
% 6.81/1.25  % (8096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.81/1.25  % (8096)Termination reason: Time limit
% 6.81/1.25  % (8096)Termination phase: Saturation
% 6.81/1.25  
% 6.81/1.25  % (8096)Memory used [KB]: 13432
% 6.81/1.25  % (8096)Time elapsed: 0.400 s
% 6.81/1.25  % (8096)------------------------------
% 6.81/1.25  % (8096)------------------------------
% 7.67/1.36  % (8161)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.89/1.39  % (8176)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.89/1.41  % (8038)Time limit reached!
% 7.89/1.41  % (8038)------------------------------
% 7.89/1.41  % (8038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.41  % (8038)Termination reason: Time limit
% 7.89/1.41  
% 7.89/1.41  % (8038)Memory used [KB]: 17270
% 7.89/1.41  % (8038)Time elapsed: 1.007 s
% 7.89/1.41  % (8038)------------------------------
% 7.89/1.41  % (8038)------------------------------
% 9.01/1.55  % (8261)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.33/1.63  % (8063)Time limit reached!
% 9.33/1.63  % (8063)------------------------------
% 9.33/1.63  % (8063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.13/1.65  % (8063)Termination reason: Time limit
% 10.13/1.65  
% 10.13/1.65  % (8063)Memory used [KB]: 20084
% 10.13/1.65  % (8063)Time elapsed: 1.224 s
% 10.13/1.65  % (8063)------------------------------
% 10.13/1.65  % (8063)------------------------------
% 10.36/1.73  % (8061)Time limit reached!
% 10.36/1.73  % (8061)------------------------------
% 10.36/1.73  % (8061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.77/1.73  % (8061)Termination reason: Time limit
% 10.77/1.73  
% 10.77/1.73  % (8061)Memory used [KB]: 22003
% 10.77/1.73  % (8061)Time elapsed: 1.318 s
% 10.77/1.73  % (8061)------------------------------
% 10.77/1.73  % (8061)------------------------------
% 10.77/1.75  % (8161)Time limit reached!
% 10.77/1.75  % (8161)------------------------------
% 10.77/1.75  % (8161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.77/1.75  % (8161)Termination reason: Time limit
% 10.77/1.75  
% 10.77/1.75  % (8161)Memory used [KB]: 4093
% 10.77/1.75  % (8161)Time elapsed: 0.519 s
% 10.77/1.75  % (8161)------------------------------
% 10.77/1.75  % (8161)------------------------------
% 10.77/1.75  % (8329)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 10.95/1.79  % (8051)Time limit reached!
% 10.95/1.79  % (8051)------------------------------
% 10.95/1.79  % (8051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.95/1.79  % (8051)Termination reason: Time limit
% 10.95/1.79  % (8051)Termination phase: Saturation
% 10.95/1.79  
% 10.95/1.79  % (8051)Memory used [KB]: 14328
% 10.95/1.79  % (8051)Time elapsed: 1.300 s
% 10.95/1.79  % (8051)------------------------------
% 10.95/1.79  % (8051)------------------------------
% 11.38/1.84  % (8340)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.71/1.88  % (8341)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.71/1.90  % (8064)Time limit reached!
% 11.71/1.90  % (8064)------------------------------
% 11.71/1.90  % (8064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.71/1.90  % (8064)Termination reason: Time limit
% 11.71/1.90  % (8064)Termination phase: Saturation
% 11.71/1.90  
% 11.71/1.90  % (8064)Memory used [KB]: 18166
% 11.71/1.90  % (8064)Time elapsed: 1.500 s
% 11.71/1.90  % (8064)------------------------------
% 11.71/1.90  % (8064)------------------------------
% 11.71/1.90  % (8040)Time limit reached!
% 11.71/1.90  % (8040)------------------------------
% 11.71/1.90  % (8040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.71/1.91  % (8040)Termination reason: Time limit
% 11.71/1.91  % (8040)Termination phase: Saturation
% 11.71/1.91  
% 11.71/1.91  % (8040)Memory used [KB]: 20468
% 11.71/1.91  % (8040)Time elapsed: 1.500 s
% 11.71/1.91  % (8040)------------------------------
% 11.71/1.91  % (8040)------------------------------
% 11.71/1.92  % (8342)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.48/2.01  % (8343)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 12.48/2.03  % (8344)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 14.23/2.17  % (8340)Time limit reached!
% 14.23/2.17  % (8340)------------------------------
% 14.23/2.17  % (8340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.23/2.17  % (8340)Termination reason: Time limit
% 14.23/2.17  % (8340)Termination phase: Saturation
% 14.23/2.17  
% 14.23/2.17  % (8340)Memory used [KB]: 4989
% 14.23/2.17  % (8340)Time elapsed: 0.400 s
% 14.23/2.17  % (8340)------------------------------
% 14.23/2.17  % (8340)------------------------------
% 14.23/2.18  % (8101)Time limit reached!
% 14.23/2.18  % (8101)------------------------------
% 14.23/2.18  % (8101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.23/2.18  % (8101)Termination reason: Time limit
% 14.23/2.18  
% 14.23/2.18  % (8101)Memory used [KB]: 13944
% 14.23/2.18  % (8101)Time elapsed: 1.227 s
% 14.23/2.18  % (8101)------------------------------
% 14.23/2.18  % (8101)------------------------------
% 14.23/2.22  % (8050)Time limit reached!
% 14.23/2.22  % (8050)------------------------------
% 14.23/2.22  % (8050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.23/2.22  % (8050)Termination reason: Time limit
% 14.23/2.22  % (8050)Termination phase: Saturation
% 14.23/2.22  
% 14.23/2.22  % (8050)Memory used [KB]: 6652
% 14.23/2.22  % (8050)Time elapsed: 1.800 s
% 14.23/2.22  % (8050)------------------------------
% 14.23/2.22  % (8050)------------------------------
% 14.90/2.28  % (8345)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 15.14/2.31  % (8346)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 15.14/2.33  % (8343)Time limit reached!
% 15.14/2.33  % (8343)------------------------------
% 15.14/2.33  % (8343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.14/2.33  % (8343)Termination reason: Time limit
% 15.14/2.33  % (8343)Termination phase: Saturation
% 15.14/2.33  
% 15.14/2.33  % (8343)Memory used [KB]: 3582
% 15.14/2.33  % (8343)Time elapsed: 0.400 s
% 15.14/2.33  % (8343)------------------------------
% 15.14/2.33  % (8343)------------------------------
% 15.60/2.35  % (8090)Time limit reached!
% 15.60/2.35  % (8090)------------------------------
% 15.60/2.35  % (8090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.60/2.35  % (8347)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 15.60/2.35  % (8090)Termination reason: Time limit
% 15.60/2.35  
% 15.60/2.35  % (8090)Memory used [KB]: 25202
% 15.60/2.35  % (8090)Time elapsed: 1.718 s
% 15.60/2.35  % (8090)------------------------------
% 15.60/2.35  % (8090)------------------------------
% 16.01/2.44  % (8055)Time limit reached!
% 16.01/2.44  % (8055)------------------------------
% 16.01/2.44  % (8055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.01/2.44  % (8055)Termination reason: Time limit
% 16.01/2.44  
% 16.01/2.44  % (8055)Memory used [KB]: 20596
% 16.01/2.44  % (8055)Time elapsed: 2.012 s
% 16.01/2.44  % (8055)------------------------------
% 16.01/2.44  % (8055)------------------------------
% 16.01/2.45  % (8349)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.38/2.47  % (8348)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.38/2.53  % (8042)Time limit reached!
% 16.38/2.53  % (8042)------------------------------
% 16.38/2.53  % (8042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.38/2.54  % (8042)Termination reason: Time limit
% 16.38/2.54  
% 16.38/2.54  % (8042)Memory used [KB]: 26865
% 16.38/2.54  % (8042)Time elapsed: 2.021 s
% 16.38/2.54  % (8042)------------------------------
% 16.38/2.54  % (8042)------------------------------
% 16.97/2.57  % (8350)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 17.52/2.67  % (8351)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 18.64/2.75  % (8103)Time limit reached!
% 18.64/2.75  % (8103)------------------------------
% 18.64/2.75  % (8103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.09/2.77  % (8103)Termination reason: Time limit
% 19.09/2.77  % (8103)Termination phase: Saturation
% 19.09/2.77  
% 19.09/2.77  % (8103)Memory used [KB]: 15479
% 19.09/2.77  % (8103)Time elapsed: 1.700 s
% 19.09/2.77  % (8103)------------------------------
% 19.09/2.77  % (8103)------------------------------
% 19.09/2.79  % (8348)Time limit reached!
% 19.09/2.79  % (8348)------------------------------
% 19.09/2.79  % (8348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.09/2.79  % (8348)Termination reason: Time limit
% 19.09/2.79  
% 19.09/2.79  % (8348)Memory used [KB]: 10362
% 19.09/2.79  % (8348)Time elapsed: 0.419 s
% 19.09/2.79  % (8348)------------------------------
% 19.09/2.79  % (8348)------------------------------
% 19.84/2.88  % (8329)Time limit reached!
% 19.84/2.88  % (8329)------------------------------
% 19.84/2.88  % (8329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.84/2.88  % (8329)Termination reason: Time limit
% 19.84/2.88  
% 19.84/2.88  % (8329)Memory used [KB]: 20980
% 19.84/2.88  % (8329)Time elapsed: 1.212 s
% 19.84/2.88  % (8329)------------------------------
% 19.84/2.88  % (8329)------------------------------
% 20.02/2.90  % (8350)Time limit reached!
% 20.02/2.90  % (8350)------------------------------
% 20.02/2.90  % (8350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.02/2.90  % (8350)Termination reason: Time limit
% 20.02/2.90  % (8350)Termination phase: Saturation
% 20.02/2.90  
% 20.02/2.90  % (8350)Memory used [KB]: 9594
% 20.02/2.90  % (8350)Time elapsed: 0.400 s
% 20.02/2.90  % (8350)------------------------------
% 20.02/2.90  % (8350)------------------------------
% 20.43/2.95  % (8044)Time limit reached!
% 20.43/2.95  % (8044)------------------------------
% 20.43/2.95  % (8044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.43/2.96  % (8044)Termination reason: Time limit
% 20.43/2.96  % (8044)Termination phase: Saturation
% 20.43/2.96  
% 20.43/2.96  % (8044)Memory used [KB]: 28400
% 20.43/2.96  % (8044)Time elapsed: 2.500 s
% 20.43/2.96  % (8044)------------------------------
% 20.43/2.96  % (8044)------------------------------
% 20.98/3.03  % (8056)Time limit reached!
% 20.98/3.03  % (8056)------------------------------
% 20.98/3.03  % (8056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.98/3.03  % (8056)Termination reason: Time limit
% 20.98/3.03  
% 20.98/3.03  % (8056)Memory used [KB]: 36332
% 20.98/3.03  % (8056)Time elapsed: 2.623 s
% 20.98/3.03  % (8056)------------------------------
% 20.98/3.03  % (8056)------------------------------
% 21.51/3.13  % (8342)Time limit reached!
% 21.51/3.13  % (8342)------------------------------
% 21.51/3.13  % (8342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.51/3.14  % (8342)Termination reason: Time limit
% 21.51/3.14  
% 21.51/3.14  % (8342)Memory used [KB]: 19061
% 21.51/3.14  % (8342)Time elapsed: 1.309 s
% 21.51/3.14  % (8342)------------------------------
% 21.51/3.14  % (8342)------------------------------
% 24.00/3.41  % (8087)Time limit reached!
% 24.00/3.41  % (8087)------------------------------
% 24.00/3.41  % (8087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.00/3.41  % (8087)Termination reason: Time limit
% 24.00/3.41  
% 24.00/3.41  % (8087)Memory used [KB]: 30831
% 24.00/3.41  % (8087)Time elapsed: 2.815 s
% 24.00/3.41  % (8087)------------------------------
% 24.00/3.41  % (8087)------------------------------
% 24.00/3.42  % (8049)Time limit reached!
% 24.00/3.42  % (8049)------------------------------
% 24.00/3.42  % (8049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.00/3.42  % (8049)Termination reason: Time limit
% 24.00/3.42  % (8049)Termination phase: Saturation
% 24.00/3.42  
% 24.00/3.42  % (8049)Memory used [KB]: 12409
% 24.00/3.42  % (8049)Time elapsed: 3.0000 s
% 24.00/3.42  % (8049)------------------------------
% 24.00/3.42  % (8049)------------------------------
% 31.78/4.37  % (8066)Time limit reached!
% 31.78/4.37  % (8066)------------------------------
% 31.78/4.37  % (8066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.78/4.37  % (8066)Termination reason: Time limit
% 31.78/4.37  % (8066)Termination phase: Saturation
% 31.78/4.37  
% 31.78/4.37  % (8066)Memory used [KB]: 40553
% 31.78/4.37  % (8066)Time elapsed: 3.900 s
% 31.78/4.37  % (8066)------------------------------
% 31.78/4.37  % (8066)------------------------------
% 34.10/4.64  % (8345)Refutation found. Thanks to Tanya!
% 34.10/4.64  % SZS status Theorem for theBenchmark
% 34.10/4.64  % SZS output start Proof for theBenchmark
% 34.10/4.64  fof(f14762,plain,(
% 34.10/4.64    $false),
% 34.10/4.64    inference(subsumption_resolution,[],[f14761,f204])).
% 34.10/4.64  fof(f204,plain,(
% 34.10/4.64    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 34.10/4.64    inference(backward_demodulation,[],[f104,f203])).
% 34.10/4.64  fof(f203,plain,(
% 34.10/4.64    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 34.10/4.64    inference(backward_demodulation,[],[f191,f194])).
% 34.10/4.64  fof(f194,plain,(
% 34.10/4.64    sK1 = k3_xboole_0(sK0,sK1)),
% 34.10/4.64    inference(superposition,[],[f147,f53])).
% 34.10/4.64  fof(f53,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f1])).
% 34.10/4.64  fof(f1,axiom,(
% 34.10/4.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 34.10/4.64  fof(f147,plain,(
% 34.10/4.64    sK1 = k3_xboole_0(sK1,sK0)),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f129,f63])).
% 34.10/4.64  fof(f63,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 34.10/4.64    inference(cnf_transformation,[],[f30])).
% 34.10/4.64  fof(f30,plain,(
% 34.10/4.64    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 34.10/4.64    inference(ennf_transformation,[],[f7])).
% 34.10/4.64  fof(f7,axiom,(
% 34.10/4.64    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 34.10/4.64  fof(f129,plain,(
% 34.10/4.64    r1_tarski(sK1,sK0)),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f126,f100])).
% 34.10/4.64  fof(f100,plain,(
% 34.10/4.64    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 34.10/4.64    inference(equality_resolution,[],[f65])).
% 34.10/4.64  fof(f65,plain,(
% 34.10/4.64    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 34.10/4.64    inference(cnf_transformation,[],[f40])).
% 34.10/4.64  fof(f40,plain,(
% 34.10/4.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 34.10/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 34.10/4.64  fof(f39,plain,(
% 34.10/4.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 34.10/4.64    introduced(choice_axiom,[])).
% 34.10/4.64  fof(f38,plain,(
% 34.10/4.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 34.10/4.64    inference(rectify,[],[f37])).
% 34.10/4.64  fof(f37,plain,(
% 34.10/4.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 34.10/4.64    inference(nnf_transformation,[],[f18])).
% 34.10/4.64  fof(f18,axiom,(
% 34.10/4.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 34.10/4.64  fof(f126,plain,(
% 34.10/4.64    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f48,f46,f59])).
% 34.10/4.64  fof(f59,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f36])).
% 34.10/4.64  fof(f36,plain,(
% 34.10/4.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 34.10/4.64    inference(nnf_transformation,[],[f29])).
% 34.10/4.64  fof(f29,plain,(
% 34.10/4.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 34.10/4.64    inference(ennf_transformation,[],[f20])).
% 34.10/4.64  fof(f20,axiom,(
% 34.10/4.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 34.10/4.64  fof(f46,plain,(
% 34.10/4.64    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 34.10/4.64    inference(cnf_transformation,[],[f35])).
% 34.10/4.64  fof(f35,plain,(
% 34.10/4.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 34.10/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f34])).
% 34.10/4.64  fof(f34,plain,(
% 34.10/4.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 34.10/4.64    introduced(choice_axiom,[])).
% 34.10/4.64  fof(f28,plain,(
% 34.10/4.64    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.10/4.64    inference(ennf_transformation,[],[f26])).
% 34.10/4.64  fof(f26,negated_conjecture,(
% 34.10/4.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 34.10/4.64    inference(negated_conjecture,[],[f25])).
% 34.10/4.64  fof(f25,conjecture,(
% 34.10/4.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 34.10/4.64  fof(f48,plain,(
% 34.10/4.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f23])).
% 34.10/4.64  fof(f23,axiom,(
% 34.10/4.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 34.10/4.64  fof(f191,plain,(
% 34.10/4.64    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f46,f91])).
% 34.10/4.64  fof(f91,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f64,f57])).
% 34.10/4.64  fof(f57,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f5])).
% 34.10/4.64  fof(f5,axiom,(
% 34.10/4.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 34.10/4.64  fof(f64,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f31])).
% 34.10/4.64  fof(f31,plain,(
% 34.10/4.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.10/4.64    inference(ennf_transformation,[],[f22])).
% 34.10/4.64  fof(f22,axiom,(
% 34.10/4.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 34.10/4.64  fof(f104,plain,(
% 34.10/4.64    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 34.10/4.64    inference(backward_demodulation,[],[f47,f49])).
% 34.10/4.64  fof(f49,plain,(
% 34.10/4.64    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 34.10/4.64    inference(cnf_transformation,[],[f21])).
% 34.10/4.64  fof(f21,axiom,(
% 34.10/4.64    ! [X0] : k2_subset_1(X0) = X0),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 34.10/4.64  fof(f47,plain,(
% 34.10/4.64    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 34.10/4.64    inference(cnf_transformation,[],[f35])).
% 34.10/4.64  fof(f14761,plain,(
% 34.10/4.64    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 34.10/4.64    inference(backward_demodulation,[],[f8278,f14747])).
% 34.10/4.64  fof(f14747,plain,(
% 34.10/4.64    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 34.10/4.64    inference(superposition,[],[f14249,f147])).
% 34.10/4.64  fof(f14249,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = X0) )),
% 34.10/4.64    inference(backward_demodulation,[],[f3339,f14248])).
% 34.10/4.64  fof(f14248,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5)))) = X5) )),
% 34.10/4.64    inference(forward_demodulation,[],[f14143,f50])).
% 34.10/4.64  fof(f50,plain,(
% 34.10/4.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 34.10/4.64    inference(cnf_transformation,[],[f9])).
% 34.10/4.64  fof(f9,axiom,(
% 34.10/4.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 34.10/4.64  fof(f14143,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k5_xboole_0(X5,k1_xboole_0) = k3_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5))))) )),
% 34.10/4.64    inference(superposition,[],[f546,f5229])).
% 34.10/4.64  fof(f5229,plain,(
% 34.10/4.64    ( ! [X10,X9] : (k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f3754,f5212])).
% 34.10/4.64  fof(f5212,plain,(
% 34.10/4.64    ( ! [X37,X38,X36] : (r2_hidden(sK3(X36,X36,k3_xboole_0(X37,X38)),X37) | k1_xboole_0 = k3_xboole_0(X37,X38)) )),
% 34.10/4.64    inference(resolution,[],[f5177,f3741])).
% 34.10/4.64  fof(f3741,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k1_xboole_0 = X1) )),
% 34.10/4.64    inference(backward_demodulation,[],[f570,f3660])).
% 34.10/4.64  fof(f3660,plain,(
% 34.10/4.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f1103,f3637])).
% 34.10/4.64  fof(f3637,plain,(
% 34.10/4.64    k1_xboole_0 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f981,f2925])).
% 34.10/4.64  fof(f2925,plain,(
% 34.10/4.64    ( ! [X94,X95] : (r2_hidden(sK3(k1_xboole_0,X94,X95),X95) | k1_xboole_0 = X95) )),
% 34.10/4.64    inference(forward_demodulation,[],[f2924,f2905])).
% 34.10/4.64  fof(f2905,plain,(
% 34.10/4.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f2430,f63])).
% 34.10/4.64  fof(f2430,plain,(
% 34.10/4.64    ( ! [X12] : (r1_tarski(k1_xboole_0,X12)) )),
% 34.10/4.64    inference(superposition,[],[f2089,f50])).
% 34.10/4.64  fof(f2089,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,X0),X1)) )),
% 34.10/4.64    inference(superposition,[],[f1944,f1103])).
% 34.10/4.64  fof(f1944,plain,(
% 34.10/4.64    ( ! [X4] : (r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)),X4)) )),
% 34.10/4.64    inference(superposition,[],[f116,f1103])).
% 34.10/4.64  fof(f116,plain,(
% 34.10/4.64    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 34.10/4.64    inference(superposition,[],[f89,f51])).
% 34.10/4.64  fof(f51,plain,(
% 34.10/4.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 34.10/4.64    inference(cnf_transformation,[],[f27])).
% 34.10/4.64  fof(f27,plain,(
% 34.10/4.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 34.10/4.64    inference(rectify,[],[f4])).
% 34.10/4.64  fof(f4,axiom,(
% 34.10/4.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 34.10/4.64  fof(f89,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f52,f57])).
% 34.10/4.64  fof(f52,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f8])).
% 34.10/4.64  fof(f8,axiom,(
% 34.10/4.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 34.10/4.64  fof(f2924,plain,(
% 34.10/4.64    ( ! [X94,X95] : (k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X94)) = X95 | r2_hidden(sK3(k1_xboole_0,X94,X95),X95)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f2921,f2905])).
% 34.10/4.64  fof(f2921,plain,(
% 34.10/4.64    ( ! [X94,X95,X93] : (r2_hidden(sK3(k1_xboole_0,X94,X95),X95) | k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95) )),
% 34.10/4.64    inference(backward_demodulation,[],[f2862,f2905])).
% 34.10/4.64  fof(f2862,plain,(
% 34.10/4.64    ( ! [X94,X95,X93] : (k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95 | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f2861,f546])).
% 34.10/4.64  fof(f2861,plain,(
% 34.10/4.64    ( ! [X94,X95,X93] : (k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94)) = X95 | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f2860,f105])).
% 34.10/4.64  fof(f105,plain,(
% 34.10/4.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 34.10/4.64    inference(superposition,[],[f54,f50])).
% 34.10/4.64  fof(f54,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f2])).
% 34.10/4.64  fof(f2,axiom,(
% 34.10/4.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 34.10/4.64  fof(f2860,plain,(
% 34.10/4.64    ( ! [X94,X95,X93] : (r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95) | k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94))) = X95) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f2723,f312])).
% 34.10/4.64  fof(f312,plain,(
% 34.10/4.64    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 34.10/4.64    inference(superposition,[],[f146,f50])).
% 34.10/4.64  fof(f146,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0))) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f142,f138])).
% 34.10/4.64  fof(f138,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 34.10/4.64    inference(superposition,[],[f102,f51])).
% 34.10/4.64  fof(f102,plain,(
% 34.10/4.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 34.10/4.64    inference(equality_resolution,[],[f97])).
% 34.10/4.64  fof(f97,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 34.10/4.64    inference(definition_unfolding,[],[f74,f57])).
% 34.10/4.64  fof(f74,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 34.10/4.64    inference(cnf_transformation,[],[f45])).
% 34.10/4.64  fof(f45,plain,(
% 34.10/4.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 34.10/4.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 34.10/4.64  fof(f44,plain,(
% 34.10/4.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 34.10/4.64    introduced(choice_axiom,[])).
% 34.10/4.64  fof(f43,plain,(
% 34.10/4.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 34.10/4.64    inference(rectify,[],[f42])).
% 34.10/4.64  fof(f42,plain,(
% 34.10/4.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 34.10/4.64    inference(flattening,[],[f41])).
% 34.10/4.64  fof(f41,plain,(
% 34.10/4.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 34.10/4.64    inference(nnf_transformation,[],[f3])).
% 34.10/4.64  fof(f3,axiom,(
% 34.10/4.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 34.10/4.64  fof(f142,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 34.10/4.64    inference(superposition,[],[f103,f51])).
% 34.10/4.64  fof(f103,plain,(
% 34.10/4.64    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X0)) )),
% 34.10/4.64    inference(equality_resolution,[],[f98])).
% 34.10/4.64  fof(f98,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 34.10/4.64    inference(definition_unfolding,[],[f73,f57])).
% 34.10/4.64  fof(f73,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 34.10/4.64    inference(cnf_transformation,[],[f45])).
% 34.10/4.64  fof(f2723,plain,(
% 34.10/4.64    ( ! [X94,X95,X93] : (r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),X95) | r2_hidden(sK3(k3_xboole_0(k1_xboole_0,X93),X94,X95),k1_xboole_0) | k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X93),k3_xboole_0(k3_xboole_0(k1_xboole_0,X93),X94))) = X95) )),
% 34.10/4.64    inference(superposition,[],[f632,f105])).
% 34.10/4.64  fof(f632,plain,(
% 34.10/4.64    ( ! [X10,X8,X11,X9] : (r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11) | r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X8) | k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10))) = X11) )),
% 34.10/4.64    inference(forward_demodulation,[],[f631,f546])).
% 34.10/4.64  fof(f631,plain,(
% 34.10/4.64    ( ! [X10,X8,X11,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10))) = X11 | r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11) | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f593,f546])).
% 34.10/4.64  fof(f593,plain,(
% 34.10/4.64    ( ! [X10,X8,X11,X9] : (r2_hidden(sK3(k3_xboole_0(X8,k5_xboole_0(X8,X9)),X10,X11),X11) | k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10))) = X11 | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f271,f546])).
% 34.10/4.64  fof(f271,plain,(
% 34.10/4.64    ( ! [X10,X8,X11,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10))) = X11 | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X11) | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f265,f70])).
% 34.10/4.64  fof(f70,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f10])).
% 34.10/4.64  fof(f10,axiom,(
% 34.10/4.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 34.10/4.64  fof(f265,plain,(
% 34.10/4.64    ( ! [X10,X8,X11,X9] : (r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X11) | k5_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),k3_xboole_0(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10)) = X11 | r2_hidden(sK3(k5_xboole_0(X8,k3_xboole_0(X8,X9)),X10,X11),X8)) )),
% 34.10/4.64    inference(resolution,[],[f95,f103])).
% 34.10/4.64  fof(f95,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 34.10/4.64    inference(definition_unfolding,[],[f76,f57])).
% 34.10/4.64  fof(f76,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f45])).
% 34.10/4.64  fof(f981,plain,(
% 34.10/4.64    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f980,f233])).
% 34.10/4.64  fof(f233,plain,(
% 34.10/4.64    ( ! [X1] : (k3_xboole_0(sK1,k5_xboole_0(X1,sK1)) = k3_xboole_0(sK1,k5_xboole_0(X1,sK0))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f232,f53])).
% 34.10/4.64  fof(f232,plain,(
% 34.10/4.64    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k3_xboole_0(sK1,k5_xboole_0(X1,sK1))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f225,f187])).
% 34.10/4.64  fof(f187,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f171,f53])).
% 34.10/4.64  fof(f171,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 34.10/4.64    inference(superposition,[],[f71,f51])).
% 34.10/4.64  fof(f71,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f6])).
% 34.10/4.64  fof(f6,axiom,(
% 34.10/4.64    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 34.10/4.64  fof(f225,plain,(
% 34.10/4.64    ( ! [X1] : (k3_xboole_0(k5_xboole_0(X1,sK0),sK1) = k5_xboole_0(k3_xboole_0(X1,sK1),sK1)) )),
% 34.10/4.64    inference(superposition,[],[f71,f194])).
% 34.10/4.64  fof(f980,plain,(
% 34.10/4.64    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f966,f388])).
% 34.10/4.64  fof(f388,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X2,k5_xboole_0(X3,X2))) | r2_hidden(X4,X2)) )),
% 34.10/4.64    inference(superposition,[],[f184,f54])).
% 34.10/4.64  fof(f184,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X2,k5_xboole_0(X2,X3))) | r2_hidden(X4,X2)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f143,f183])).
% 34.10/4.64  fof(f183,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f168,f53])).
% 34.10/4.64  fof(f168,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 34.10/4.64    inference(superposition,[],[f71,f51])).
% 34.10/4.64  fof(f143,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (~r2_hidden(X4,k5_xboole_0(X2,k3_xboole_0(X3,X2))) | r2_hidden(X4,X2)) )),
% 34.10/4.64    inference(superposition,[],[f103,f53])).
% 34.10/4.64  fof(f966,plain,(
% 34.10/4.64    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) | ~r2_hidden(X0,sK1)) )),
% 34.10/4.64    inference(superposition,[],[f582,f548])).
% 34.10/4.64  fof(f548,plain,(
% 34.10/4.64    k5_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),
% 34.10/4.64    inference(superposition,[],[f183,f147])).
% 34.10/4.64  fof(f582,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_xboole_0(X4,k3_xboole_0(X3,k5_xboole_0(X3,X4)))) | ~r2_hidden(X5,X4)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f189,f546])).
% 34.10/4.64  fof(f189,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_xboole_0(X4,k5_xboole_0(X3,k3_xboole_0(X3,X4)))) | ~r2_hidden(X5,X4)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f177,f53])).
% 34.10/4.64  fof(f177,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k3_xboole_0(k5_xboole_0(X3,k3_xboole_0(X3,X4)),X4)) | ~r2_hidden(X5,X4)) )),
% 34.10/4.64    inference(superposition,[],[f102,f71])).
% 34.10/4.64  fof(f1103,plain,(
% 34.10/4.64    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) )),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f981,f570])).
% 34.10/4.64  fof(f570,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,X0) = X1) )),
% 34.10/4.64    inference(backward_demodulation,[],[f270,f545])).
% 34.10/4.64  fof(f545,plain,(
% 34.10/4.64    ( ! [X0] : (k5_xboole_0(X0,X0) = k3_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 34.10/4.64    inference(superposition,[],[f183,f51])).
% 34.10/4.64  fof(f270,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,X0)) = X1 | r2_hidden(sK3(X0,X0,X1),X1)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f268,f183])).
% 34.10/4.64  fof(f268,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1) )),
% 34.10/4.64    inference(duplicate_literal_removal,[],[f262])).
% 34.10/4.64  fof(f262,plain,(
% 34.10/4.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 | r2_hidden(sK3(X0,X0,X1),X1)) )),
% 34.10/4.64    inference(resolution,[],[f95,f94])).
% 34.10/4.64  fof(f94,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f77,f57])).
% 34.10/4.64  fof(f77,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f45])).
% 34.10/4.64  fof(f5177,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (~r2_hidden(X4,k3_xboole_0(X3,X2)) | r2_hidden(X4,X3)) )),
% 34.10/4.64    inference(superposition,[],[f5036,f53])).
% 34.10/4.64  fof(f5036,plain,(
% 34.10/4.64    ( ! [X6,X8,X7] : (~r2_hidden(X8,k3_xboole_0(X6,X7)) | r2_hidden(X8,X7)) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f585,f5034])).
% 34.10/4.64  fof(f5034,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5033,f183])).
% 34.10/4.64  fof(f5033,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X9,k3_xboole_0(X8,X9))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5032,f54])).
% 34.10/4.64  fof(f5032,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X9)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5031,f3912])).
% 34.10/4.64  fof(f3912,plain,(
% 34.10/4.64    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X7,X8)) = X8) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3674,f105])).
% 34.10/4.64  fof(f3674,plain,(
% 34.10/4.64    ( ! [X8,X7] : (k5_xboole_0(k1_xboole_0,X8) = k5_xboole_0(X7,k5_xboole_0(X7,X8))) )),
% 34.10/4.64    inference(backward_demodulation,[],[f1945,f3637])).
% 34.10/4.64  fof(f1945,plain,(
% 34.10/4.64    ( ! [X8,X7] : (k5_xboole_0(X7,k5_xboole_0(X7,X8)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)),X8)) )),
% 34.10/4.64    inference(superposition,[],[f70,f1103])).
% 34.10/4.64  fof(f5031,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),X9)))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5030,f458])).
% 34.10/4.64  fof(f458,plain,(
% 34.10/4.64    ( ! [X19,X17,X18,X16] : (k5_xboole_0(X18,k5_xboole_0(X17,k5_xboole_0(X16,X19))) = k5_xboole_0(X18,k5_xboole_0(X16,k5_xboole_0(X17,X19)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f457,f70])).
% 34.10/4.64  fof(f457,plain,(
% 34.10/4.64    ( ! [X19,X17,X18,X16] : (k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X16,X17),X19)) = k5_xboole_0(X18,k5_xboole_0(X17,k5_xboole_0(X16,X19)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f429,f456])).
% 34.10/4.64  fof(f456,plain,(
% 34.10/4.64    ( ! [X14,X12,X15,X13] : (k5_xboole_0(k5_xboole_0(X13,k5_xboole_0(X12,X14)),X15) = k5_xboole_0(X14,k5_xboole_0(X12,k5_xboole_0(X13,X15)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f428,f70])).
% 34.10/4.64  fof(f428,plain,(
% 34.10/4.64    ( ! [X14,X12,X15,X13] : (k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X12,X13),X15)) = k5_xboole_0(k5_xboole_0(X13,k5_xboole_0(X12,X14)),X15)) )),
% 34.10/4.64    inference(superposition,[],[f152,f152])).
% 34.10/4.64  fof(f152,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) )),
% 34.10/4.64    inference(superposition,[],[f70,f54])).
% 34.10/4.64  fof(f429,plain,(
% 34.10/4.64    ( ! [X19,X17,X18,X16] : (k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X16,X17),X19)) = k5_xboole_0(k5_xboole_0(X16,k5_xboole_0(X17,X18)),X19)) )),
% 34.10/4.64    inference(superposition,[],[f152,f70])).
% 34.10/4.64  fof(f5030,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5029,f3912])).
% 34.10/4.64  fof(f5029,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(X9,k5_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(X8,X9)))))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5028,f562])).
% 34.10/4.64  fof(f562,plain,(
% 34.10/4.64    ( ! [X21,X22,X20] : (k5_xboole_0(X20,k5_xboole_0(k3_xboole_0(X21,X20),X22)) = k5_xboole_0(X22,k3_xboole_0(X20,k5_xboole_0(X20,X21)))) )),
% 34.10/4.64    inference(superposition,[],[f157,f183])).
% 34.10/4.64  fof(f157,plain,(
% 34.10/4.64    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 34.10/4.64    inference(superposition,[],[f70,f54])).
% 34.10/4.64  fof(f5028,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X8,X9),k3_xboole_0(X9,k5_xboole_0(X9,X8)))))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5027,f157])).
% 34.10/4.64  fof(f5027,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),X9)))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5026,f458])).
% 34.10/4.64  fof(f5026,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9)))))) )),
% 34.10/4.64    inference(subsumption_resolution,[],[f5025,f184])).
% 34.10/4.64  fof(f5025,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5024,f183])).
% 34.10/4.64  fof(f5024,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k3_xboole_0(k5_xboole_0(k3_xboole_0(X9,k5_xboole_0(X9,X8)),k5_xboole_0(k5_xboole_0(X8,X9),X9)),X8))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5023,f169])).
% 34.10/4.64  fof(f169,plain,(
% 34.10/4.64    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X4),X3) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X4,X3))) )),
% 34.10/4.64    inference(superposition,[],[f71,f53])).
% 34.10/4.64  fof(f5023,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8)))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5022,f54])).
% 34.10/4.64  fof(f5022,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8),k3_xboole_0(X8,k3_xboole_0(X9,k5_xboole_0(X9,X8)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5021,f910])).
% 34.10/4.64  fof(f910,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5))) = k3_xboole_0(k3_xboole_0(X6,X5),k3_xboole_0(X5,k5_xboole_0(X5,X6)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f909,f183])).
% 34.10/4.64  fof(f909,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k3_xboole_0(X6,k5_xboole_0(X6,X5)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f908,f546])).
% 34.10/4.64  fof(f908,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k5_xboole_0(X6,k3_xboole_0(X6,X5)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f907,f54])).
% 34.10/4.64  fof(f907,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(X5,k5_xboole_0(k3_xboole_0(X6,X5),X6))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f878,f53])).
% 34.10/4.64  fof(f878,plain,(
% 34.10/4.64    ( ! [X6,X5] : (k3_xboole_0(k3_xboole_0(X6,X5),k5_xboole_0(X5,k3_xboole_0(X6,X5))) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X6,X5),X6),X5)) )),
% 34.10/4.64    inference(superposition,[],[f169,f187])).
% 34.10/4.64  fof(f5021,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8),k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5020,f54])).
% 34.10/4.64  fof(f5020,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X8,X9),X9),X8)))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5019,f892])).
% 34.10/4.64  fof(f892,plain,(
% 34.10/4.64    ( ! [X35,X33,X36,X34] : (k5_xboole_0(k3_xboole_0(X35,X33),k5_xboole_0(X36,k3_xboole_0(X33,X34))) = k5_xboole_0(X36,k3_xboole_0(k5_xboole_0(X34,X35),X33))) )),
% 34.10/4.64    inference(superposition,[],[f157,f169])).
% 34.10/4.64  fof(f5019,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,X8),k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5018,f458])).
% 34.10/4.64  fof(f5018,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5017,f54])).
% 34.10/4.64  fof(f5017,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k5_xboole_0(k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5016,f157])).
% 34.10/4.64  fof(f5016,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(k3_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9))),k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f4943,f473])).
% 34.10/4.64  fof(f473,plain,(
% 34.10/4.64    ( ! [X30,X28,X29] : (k5_xboole_0(k3_xboole_0(X28,X29),k5_xboole_0(X30,k5_xboole_0(X28,X29))) = k5_xboole_0(X30,k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29)))) )),
% 34.10/4.64    inference(superposition,[],[f157,f90])).
% 34.10/4.64  fof(f90,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 34.10/4.64    inference(definition_unfolding,[],[f58,f88])).
% 34.10/4.64  fof(f88,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 34.10/4.64    inference(definition_unfolding,[],[f55,f87])).
% 34.10/4.64  fof(f87,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f56,f86])).
% 34.10/4.64  fof(f86,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f69,f85])).
% 34.10/4.64  fof(f85,plain,(
% 34.10/4.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f79,f84])).
% 34.10/4.64  fof(f84,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f80,f83])).
% 34.10/4.64  fof(f83,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 34.10/4.64    inference(definition_unfolding,[],[f81,f82])).
% 34.10/4.64  fof(f82,plain,(
% 34.10/4.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f17])).
% 34.10/4.64  fof(f17,axiom,(
% 34.10/4.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 34.10/4.64  fof(f81,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f16])).
% 34.10/4.64  fof(f16,axiom,(
% 34.10/4.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 34.10/4.64  fof(f80,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f15])).
% 34.10/4.64  fof(f15,axiom,(
% 34.10/4.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 34.10/4.64  fof(f79,plain,(
% 34.10/4.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f14])).
% 34.10/4.64  fof(f14,axiom,(
% 34.10/4.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 34.10/4.64  fof(f69,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f13])).
% 34.10/4.64  fof(f13,axiom,(
% 34.10/4.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 34.10/4.64  fof(f56,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f12])).
% 34.10/4.64  fof(f12,axiom,(
% 34.10/4.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 34.10/4.64  fof(f55,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f19])).
% 34.10/4.64  fof(f19,axiom,(
% 34.10/4.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 34.10/4.64  fof(f58,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f11])).
% 34.10/4.64  fof(f11,axiom,(
% 34.10/4.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 34.10/4.64  fof(f4943,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(X10,k5_xboole_0(X8,k3_tarski(k6_enumset1(k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X9,X8),k3_xboole_0(X8,k5_xboole_0(X8,X9)))))) | ~r2_hidden(X10,X8)) )),
% 34.10/4.64    inference(superposition,[],[f3929,f183])).
% 34.10/4.64  fof(f3929,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3))))) | ~r2_hidden(X5,X4)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f1822,f3925])).
% 34.10/4.64  fof(f3925,plain,(
% 34.10/4.64    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X15,X14)) = X15) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3676,f50])).
% 34.10/4.64  fof(f3676,plain,(
% 34.10/4.64    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X15,X14)) = k5_xboole_0(X15,k1_xboole_0)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f1948,f3637])).
% 34.10/4.64  fof(f1948,plain,(
% 34.10/4.64    ( ! [X14,X15] : (k5_xboole_0(X14,k5_xboole_0(X15,X14)) = k5_xboole_0(X15,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))) )),
% 34.10/4.64    inference(superposition,[],[f157,f1103])).
% 34.10/4.64  fof(f1822,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k5_xboole_0(X3,k5_xboole_0(X4,X3))) | ~r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3)))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f1788,f54])).
% 34.10/4.64  fof(f1788,plain,(
% 34.10/4.64    ( ! [X4,X5,X3] : (~r2_hidden(X5,k5_xboole_0(X4,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,X3))))) | ~r2_hidden(X5,k5_xboole_0(k5_xboole_0(X4,X3),X3))) )),
% 34.10/4.64    inference(superposition,[],[f163,f250])).
% 34.10/4.64  fof(f250,plain,(
% 34.10/4.64    ( ! [X2,X3] : (k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k5_xboole_0(X2,k3_xboole_0(X3,k5_xboole_0(X3,X2)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f243,f183])).
% 34.10/4.64  fof(f243,plain,(
% 34.10/4.64    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 34.10/4.64    inference(superposition,[],[f90,f70])).
% 34.10/4.64  fof(f163,plain,(
% 34.10/4.64    ( ! [X14,X12,X15,X13] : (~r2_hidden(X15,k5_xboole_0(X12,k5_xboole_0(X13,k3_xboole_0(k5_xboole_0(X12,X13),X14)))) | ~r2_hidden(X15,X14)) )),
% 34.10/4.64    inference(superposition,[],[f102,f70])).
% 34.10/4.64  fof(f585,plain,(
% 34.10/4.64    ( ! [X6,X8,X7] : (r2_hidden(X8,k3_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X6,X7)))) | r2_hidden(X8,X7) | ~r2_hidden(X8,k3_xboole_0(X6,X7))) )),
% 34.10/4.64    inference(backward_demodulation,[],[f220,f546])).
% 34.10/4.64  fof(f220,plain,(
% 34.10/4.64    ( ! [X6,X8,X7] : (r2_hidden(X8,k3_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7)))) | r2_hidden(X8,X7) | ~r2_hidden(X8,k3_xboole_0(X6,X7))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f214,f53])).
% 34.10/4.64  fof(f214,plain,(
% 34.10/4.64    ( ! [X6,X8,X7] : (r2_hidden(X8,k3_xboole_0(k5_xboole_0(X6,k3_xboole_0(X6,X7)),X7)) | r2_hidden(X8,X7) | ~r2_hidden(X8,k3_xboole_0(X6,X7))) )),
% 34.10/4.64    inference(superposition,[],[f101,f71])).
% 34.10/4.64  fof(f101,plain,(
% 34.10/4.64    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 34.10/4.64    inference(equality_resolution,[],[f96])).
% 34.10/4.64  fof(f96,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 34.10/4.64    inference(definition_unfolding,[],[f75,f57])).
% 34.10/4.64  fof(f75,plain,(
% 34.10/4.64    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 34.10/4.64    inference(cnf_transformation,[],[f45])).
% 34.10/4.64  fof(f3754,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9))) | ~r2_hidden(sK3(X8,X8,k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))),X9)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f796,f3660])).
% 34.10/4.64  fof(f796,plain,(
% 34.10/4.64    ( ! [X10,X8,X9] : (~r2_hidden(sK3(X8,X8,k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))),X9) | k5_xboole_0(X8,X8) = k3_xboole_0(X9,k3_xboole_0(X10,k5_xboole_0(X10,X9)))) )),
% 34.10/4.64    inference(resolution,[],[f582,f570])).
% 34.10/4.64  fof(f546,plain,(
% 34.10/4.64    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,k5_xboole_0(X2,X1))) )),
% 34.10/4.64    inference(superposition,[],[f183,f53])).
% 34.10/4.64  fof(f3339,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X1,X0))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3338,f546])).
% 34.10/4.64  fof(f3338,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3337,f54])).
% 34.10/4.64  fof(f3337,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),X1)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3336,f157])).
% 34.10/4.64  fof(f3336,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,X0)))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3335,f53])).
% 34.10/4.64  fof(f3335,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k3_xboole_0(k5_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X1,X0)),X0)) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3334,f71])).
% 34.10/4.64  fof(f3334,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X1,X0),X0),k3_xboole_0(k5_xboole_0(X1,X0),X0))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f3267,f54])).
% 34.10/4.64  fof(f3267,plain,(
% 34.10/4.64    ( ! [X0,X1] : (k3_tarski(k6_enumset1(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),k3_xboole_0(X1,X0),X0)) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X1,X0),X0),k3_xboole_0(k3_xboole_0(X1,X0),X0))) )),
% 34.10/4.64    inference(superposition,[],[f238,f51])).
% 34.10/4.64  fof(f238,plain,(
% 34.10/4.64    ( ! [X6,X7,X5] : (k3_tarski(k6_enumset1(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X7,X6))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(X5,X7),X6),k3_xboole_0(k3_xboole_0(X5,X6),k3_xboole_0(X7,X6)))) )),
% 34.10/4.64    inference(superposition,[],[f90,f71])).
% 34.10/4.64  fof(f8278,plain,(
% 34.10/4.64    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 34.10/4.64    inference(forward_demodulation,[],[f8096,f352])).
% 34.10/4.64  fof(f352,plain,(
% 34.10/4.64    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f46,f302,f92])).
% 34.10/4.64  fof(f92,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.10/4.64    inference(definition_unfolding,[],[f72,f88])).
% 34.10/4.64  fof(f72,plain,(
% 34.10/4.64    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 34.10/4.64    inference(cnf_transformation,[],[f33])).
% 34.10/4.64  fof(f33,plain,(
% 34.10/4.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 34.10/4.64    inference(flattening,[],[f32])).
% 34.10/4.64  fof(f32,plain,(
% 34.10/4.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 34.10/4.64    inference(ennf_transformation,[],[f24])).
% 34.10/4.64  fof(f24,axiom,(
% 34.10/4.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 34.10/4.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 34.10/4.64  fof(f302,plain,(
% 34.10/4.64    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f48,f254,f60])).
% 34.10/4.64  fof(f60,plain,(
% 34.10/4.64    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 34.10/4.64    inference(cnf_transformation,[],[f36])).
% 34.10/4.64  fof(f254,plain,(
% 34.10/4.64    r2_hidden(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 34.10/4.64    inference(unit_resulting_resolution,[],[f226,f99])).
% 34.10/4.64  fof(f99,plain,(
% 34.10/4.64    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 34.10/4.64    inference(equality_resolution,[],[f66])).
% 34.10/4.64  fof(f66,plain,(
% 34.10/4.64    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 34.10/4.64    inference(cnf_transformation,[],[f40])).
% 34.10/4.64  fof(f226,plain,(
% 34.10/4.64    r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 34.10/4.64    inference(superposition,[],[f89,f194])).
% 34.10/4.64  fof(f8096,plain,(
% 34.10/4.64    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,sK1)))),
% 34.10/4.64    inference(superposition,[],[f5299,f548])).
% 34.10/4.64  fof(f5299,plain,(
% 34.10/4.64    ( ! [X15,X16] : (k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)) = k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15))))) )),
% 34.10/4.64    inference(forward_demodulation,[],[f5250,f50])).
% 34.10/4.64  fof(f5250,plain,(
% 34.10/4.64    ( ! [X15,X16] : (k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k1_xboole_0)) )),
% 34.10/4.64    inference(backward_demodulation,[],[f1791,f5229])).
% 34.10/4.65  fof(f1791,plain,(
% 34.10/4.65    ( ! [X15,X16] : (k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,k3_xboole_0(X16,k5_xboole_0(X16,X15)))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k3_xboole_0(X15,k3_xboole_0(X16,k5_xboole_0(X16,X15))))) )),
% 34.10/4.65    inference(superposition,[],[f90,f250])).
% 34.10/4.65  % SZS output end Proof for theBenchmark
% 34.10/4.65  % (8345)------------------------------
% 34.10/4.65  % (8345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 34.10/4.65  % (8345)Termination reason: Refutation
% 34.10/4.65  
% 34.10/4.65  % (8345)Memory used [KB]: 30575
% 34.10/4.65  % (8345)Time elapsed: 2.395 s
% 34.10/4.65  % (8345)------------------------------
% 34.10/4.65  % (8345)------------------------------
% 34.10/4.65  % (8034)Success in time 4.291 s
%------------------------------------------------------------------------------
