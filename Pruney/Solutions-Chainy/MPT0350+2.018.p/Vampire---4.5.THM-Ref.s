%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:52 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 637 expanded)
%              Number of leaves         :   24 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  225 (1151 expanded)
%              Number of equality atoms :   85 ( 580 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f894,plain,(
    $false ),
    inference(subsumption_resolution,[],[f893,f106])).

fof(f106,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f52,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f52,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f38])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f893,plain,(
    sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f884,f460])).

fof(f460,plain,(
    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f459,f132])).

fof(f132,plain,(
    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f129,f97])).

fof(f97,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f60,f91,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f79,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f83,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f84,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f129,plain,(
    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f118,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f70,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f91])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f118,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f110,f105])).

fof(f105,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f110,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f51,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f459,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f458,f97])).

fof(f458,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f457,f133])).

fof(f133,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f114,f132])).

fof(f114,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    inference(forward_demodulation,[],[f109,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f109,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(unit_resulting_resolution,[],[f51,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(definition_unfolding,[],[f71,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f63,f93])).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f65,f92])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f457,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f456,f80])).

fof(f456,plain,(
    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)))) ),
    inference(superposition,[],[f98,f132])).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))) ),
    inference(definition_unfolding,[],[f64,f92,f92,f94])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f884,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f51,f605,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f82,f92])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f605,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f53,f502,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f502,plain,(
    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f477,f104])).

fof(f104,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f477,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f103,f123,f276])).

fof(f276,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(sK0,sK1),X0)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(k5_xboole_0(sK1,sK0),X0) ) ),
    inference(duplicate_literal_removal,[],[f275])).

fof(f275,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(sK0,sK1),X0)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_tarski(k5_xboole_0(sK1,sK0),X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f155,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f155,plain,(
    ! [X0] :
      ( ~ r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)),X0)
      | r1_tarski(k3_subset_1(sK0,sK1),X0)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f81,f133])).

fof(f123,plain,(
    r1_tarski(k5_xboole_0(sK1,sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f102,f118,f81])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (10707)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (10706)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (10715)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (10702)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (10714)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (10703)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (10730)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (10701)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (10730)Refutation not found, incomplete strategy% (10730)------------------------------
% 0.22/0.54  % (10730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (10730)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (10730)Memory used [KB]: 1663
% 0.22/0.54  % (10730)Time elapsed: 0.001 s
% 0.22/0.54  % (10730)------------------------------
% 0.22/0.54  % (10730)------------------------------
% 0.22/0.54  % (10705)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (10723)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (10726)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (10713)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (10713)Refutation not found, incomplete strategy% (10713)------------------------------
% 0.22/0.55  % (10713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10713)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10713)Memory used [KB]: 10618
% 0.22/0.55  % (10713)Time elapsed: 0.122 s
% 0.22/0.55  % (10713)------------------------------
% 0.22/0.55  % (10713)------------------------------
% 0.22/0.55  % (10720)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (10722)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (10719)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (10719)Refutation not found, incomplete strategy% (10719)------------------------------
% 0.22/0.55  % (10719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10719)Memory used [KB]: 1663
% 0.22/0.55  % (10719)Time elapsed: 0.135 s
% 0.22/0.55  % (10719)------------------------------
% 0.22/0.55  % (10719)------------------------------
% 0.22/0.55  % (10718)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (10704)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (10729)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (10729)Refutation not found, incomplete strategy% (10729)------------------------------
% 0.22/0.55  % (10729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10729)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (10729)Memory used [KB]: 10746
% 0.22/0.55  % (10729)Time elapsed: 0.138 s
% 0.22/0.55  % (10729)------------------------------
% 0.22/0.55  % (10729)------------------------------
% 0.22/0.55  % (10727)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (10710)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (10717)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (10711)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (10712)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (10711)Refutation not found, incomplete strategy% (10711)------------------------------
% 0.22/0.56  % (10711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10711)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10711)Memory used [KB]: 10746
% 0.22/0.56  % (10711)Time elapsed: 0.148 s
% 0.22/0.56  % (10711)------------------------------
% 0.22/0.56  % (10711)------------------------------
% 0.22/0.56  % (10716)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (10721)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (10728)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (10709)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (10708)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (10725)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.58  % (10717)Refutation not found, incomplete strategy% (10717)------------------------------
% 0.22/0.58  % (10717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (10717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (10717)Memory used [KB]: 10618
% 0.22/0.58  % (10717)Time elapsed: 0.164 s
% 0.22/0.58  % (10717)------------------------------
% 0.22/0.58  % (10717)------------------------------
% 0.22/0.58  % (10724)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.93/0.61  % (10712)Refutation found. Thanks to Tanya!
% 1.93/0.61  % SZS status Theorem for theBenchmark
% 1.93/0.61  % SZS output start Proof for theBenchmark
% 1.93/0.61  fof(f894,plain,(
% 1.93/0.61    $false),
% 1.93/0.61    inference(subsumption_resolution,[],[f893,f106])).
% 1.93/0.61  fof(f106,plain,(
% 1.93/0.61    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.93/0.61    inference(forward_demodulation,[],[f52,f54])).
% 1.93/0.61  fof(f54,plain,(
% 1.93/0.61    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.93/0.61    inference(cnf_transformation,[],[f22])).
% 1.93/0.61  fof(f22,axiom,(
% 1.93/0.61    ! [X0] : k2_subset_1(X0) = X0),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.93/0.61  fof(f52,plain,(
% 1.93/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.93/0.61    inference(cnf_transformation,[],[f39])).
% 1.93/0.61  fof(f39,plain,(
% 1.93/0.61    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f38])).
% 1.93/0.61  fof(f38,plain,(
% 1.93/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.93/0.61    introduced(choice_axiom,[])).
% 1.93/0.61  fof(f30,plain,(
% 1.93/0.61    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.61    inference(ennf_transformation,[],[f27])).
% 1.93/0.61  fof(f27,negated_conjecture,(
% 1.93/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.93/0.61    inference(negated_conjecture,[],[f26])).
% 1.93/0.61  fof(f26,conjecture,(
% 1.93/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.93/0.61  fof(f893,plain,(
% 1.93/0.61    sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.93/0.61    inference(forward_demodulation,[],[f884,f460])).
% 1.93/0.61  fof(f460,plain,(
% 1.93/0.61    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.93/0.61    inference(forward_demodulation,[],[f459,f132])).
% 1.93/0.61  fof(f132,plain,(
% 1.93/0.61    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.93/0.61    inference(forward_demodulation,[],[f129,f97])).
% 1.93/0.61  fof(f97,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f60,f91,f91])).
% 1.93/0.61  fof(f91,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f61,f90])).
% 1.93/0.61  fof(f90,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f79,f89])).
% 1.93/0.61  fof(f89,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f83,f88])).
% 1.93/0.61  fof(f88,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f84,f87])).
% 1.93/0.61  fof(f87,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.93/0.61    inference(definition_unfolding,[],[f85,f86])).
% 1.93/0.61  fof(f86,plain,(
% 1.93/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f18])).
% 1.93/0.61  fof(f18,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.93/0.61  fof(f85,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f17])).
% 1.93/0.61  fof(f17,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.93/0.61  fof(f84,plain,(
% 1.93/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f16])).
% 1.93/0.61  fof(f16,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.93/0.61  fof(f83,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f15])).
% 1.93/0.61  fof(f15,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.93/0.61  fof(f79,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f14])).
% 1.93/0.61  fof(f14,axiom,(
% 1.93/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.93/0.61  fof(f61,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f13])).
% 1.93/0.61  fof(f13,axiom,(
% 1.93/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.93/0.61  fof(f60,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f12])).
% 1.93/0.61  fof(f12,axiom,(
% 1.93/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.93/0.61  fof(f129,plain,(
% 1.93/0.61    sK0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f118,f99])).
% 1.93/0.61  fof(f99,plain,(
% 1.93/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 1.93/0.61    inference(definition_unfolding,[],[f70,f92])).
% 1.93/0.61  fof(f92,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f62,f91])).
% 1.93/0.61  fof(f62,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f20])).
% 1.93/0.61  fof(f20,axiom,(
% 1.93/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.93/0.61  fof(f70,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f32])).
% 1.93/0.61  fof(f32,plain,(
% 1.93/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.93/0.61    inference(ennf_transformation,[],[f7])).
% 1.93/0.61  fof(f7,axiom,(
% 1.93/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.93/0.61  fof(f118,plain,(
% 1.93/0.61    r1_tarski(sK1,sK0)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f110,f105])).
% 1.93/0.61  fof(f105,plain,(
% 1.93/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.93/0.61    inference(equality_resolution,[],[f75])).
% 1.93/0.61  fof(f75,plain,(
% 1.93/0.61    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.93/0.61    inference(cnf_transformation,[],[f50])).
% 1.93/0.61  fof(f50,plain,(
% 1.93/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 1.93/0.61  fof(f49,plain,(
% 1.93/0.61    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.93/0.61    introduced(choice_axiom,[])).
% 1.93/0.61  fof(f48,plain,(
% 1.93/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.61    inference(rectify,[],[f47])).
% 1.93/0.61  fof(f47,plain,(
% 1.93/0.61    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.93/0.61    inference(nnf_transformation,[],[f19])).
% 1.93/0.61  fof(f19,axiom,(
% 1.93/0.61    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.93/0.61  fof(f110,plain,(
% 1.93/0.61    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f53,f51,f66])).
% 1.93/0.61  fof(f66,plain,(
% 1.93/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f44])).
% 1.93/0.61  fof(f44,plain,(
% 1.93/0.61    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.93/0.61    inference(nnf_transformation,[],[f31])).
% 1.93/0.61  fof(f31,plain,(
% 1.93/0.61    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.93/0.61    inference(ennf_transformation,[],[f21])).
% 1.93/0.61  fof(f21,axiom,(
% 1.93/0.61    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.93/0.61  fof(f51,plain,(
% 1.93/0.61    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.93/0.61    inference(cnf_transformation,[],[f39])).
% 1.93/0.61  fof(f53,plain,(
% 1.93/0.61    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f24])).
% 1.93/0.61  fof(f24,axiom,(
% 1.93/0.61    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.93/0.61  fof(f459,plain,(
% 1.93/0.61    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.93/0.61    inference(forward_demodulation,[],[f458,f97])).
% 1.93/0.61  fof(f458,plain,(
% 1.93/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.93/0.61    inference(forward_demodulation,[],[f457,f133])).
% 1.93/0.61  fof(f133,plain,(
% 1.93/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))),
% 1.93/0.61    inference(backward_demodulation,[],[f114,f132])).
% 1.93/0.61  fof(f114,plain,(
% 1.93/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 1.93/0.61    inference(forward_demodulation,[],[f109,f80])).
% 1.93/0.61  fof(f80,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f9])).
% 1.93/0.61  fof(f9,axiom,(
% 1.93/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.93/0.61  fof(f109,plain,(
% 1.93/0.61    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f51,f100])).
% 1.93/0.61  fof(f100,plain,(
% 1.93/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f71,f94])).
% 1.93/0.61  fof(f94,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f63,f93])).
% 1.93/0.61  fof(f93,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f65,f92])).
% 1.93/0.61  fof(f65,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f11])).
% 1.93/0.61  fof(f11,axiom,(
% 1.93/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.93/0.61  fof(f63,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f5])).
% 1.93/0.61  fof(f5,axiom,(
% 1.93/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.93/0.61  fof(f71,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f33])).
% 1.93/0.61  fof(f33,plain,(
% 1.93/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.61    inference(ennf_transformation,[],[f23])).
% 1.93/0.61  fof(f23,axiom,(
% 1.93/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.93/0.61  fof(f457,plain,(
% 1.93/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)))))),
% 1.93/0.61    inference(forward_demodulation,[],[f456,f80])).
% 1.93/0.61  fof(f456,plain,(
% 1.93/0.61    k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,sK1),sK0))))),
% 1.93/0.61    inference(superposition,[],[f98,f132])).
% 1.93/0.61  fof(f98,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f64,f92,f92,f94])).
% 1.93/0.61  fof(f64,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f8])).
% 1.93/0.61  fof(f8,axiom,(
% 1.93/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.93/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.93/0.61  fof(f884,plain,(
% 1.93/0.61    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f51,f605,f101])).
% 1.93/0.61  fof(f101,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.93/0.61    inference(definition_unfolding,[],[f82,f92])).
% 1.93/0.61  fof(f82,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f37])).
% 1.93/0.61  fof(f37,plain,(
% 1.93/0.61    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.93/0.61    inference(flattening,[],[f36])).
% 2.06/0.63  fof(f36,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.06/0.63    inference(ennf_transformation,[],[f25])).
% 2.06/0.63  fof(f25,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.06/0.63  fof(f605,plain,(
% 2.06/0.63    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f53,f502,f67])).
% 2.06/0.63  fof(f67,plain,(
% 2.06/0.63    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f44])).
% 2.06/0.63  fof(f502,plain,(
% 2.06/0.63    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f477,f104])).
% 2.06/0.63  fof(f104,plain,(
% 2.06/0.63    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.06/0.63    inference(equality_resolution,[],[f76])).
% 2.06/0.63  fof(f76,plain,(
% 2.06/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.06/0.63    inference(cnf_transformation,[],[f50])).
% 2.06/0.63  fof(f477,plain,(
% 2.06/0.63    r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f103,f123,f276])).
% 2.06/0.63  fof(f276,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k3_subset_1(sK0,sK1),X0) | ~r1_tarski(sK0,X0) | ~r1_tarski(k5_xboole_0(sK1,sK0),X0)) )),
% 2.06/0.63    inference(duplicate_literal_removal,[],[f275])).
% 2.06/0.63  fof(f275,plain,(
% 2.06/0.63    ( ! [X0] : (r1_tarski(k3_subset_1(sK0,sK1),X0) | ~r1_tarski(sK0,X0) | ~r1_tarski(k5_xboole_0(sK1,sK0),X0) | ~r1_tarski(sK0,X0)) )),
% 2.06/0.63    inference(resolution,[],[f155,f81])).
% 2.06/0.63  fof(f81,plain,(
% 2.06/0.63    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.06/0.63    inference(cnf_transformation,[],[f35])).
% 2.06/0.63  fof(f35,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.06/0.63    inference(flattening,[],[f34])).
% 2.06/0.63  fof(f34,plain,(
% 2.06/0.63    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.06/0.63    inference(ennf_transformation,[],[f6])).
% 2.06/0.63  fof(f6,axiom,(
% 2.06/0.63    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 2.06/0.63  fof(f155,plain,(
% 2.06/0.63    ( ! [X0] : (~r1_tarski(k5_xboole_0(sK0,k5_xboole_0(sK1,sK0)),X0) | r1_tarski(k3_subset_1(sK0,sK1),X0) | ~r1_tarski(sK0,X0)) )),
% 2.06/0.63    inference(superposition,[],[f81,f133])).
% 2.06/0.63  fof(f123,plain,(
% 2.06/0.63    r1_tarski(k5_xboole_0(sK1,sK0),sK0)),
% 2.06/0.63    inference(unit_resulting_resolution,[],[f102,f118,f81])).
% 2.06/0.63  fof(f102,plain,(
% 2.06/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.63    inference(equality_resolution,[],[f73])).
% 2.06/0.63  fof(f73,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.63    inference(cnf_transformation,[],[f46])).
% 2.06/0.63  fof(f46,plain,(
% 2.06/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.63    inference(flattening,[],[f45])).
% 2.06/0.63  fof(f45,plain,(
% 2.06/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.63    inference(nnf_transformation,[],[f4])).
% 2.06/0.63  fof(f4,axiom,(
% 2.06/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.63  fof(f103,plain,(
% 2.06/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.63    inference(equality_resolution,[],[f72])).
% 2.06/0.63  fof(f72,plain,(
% 2.06/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.06/0.63    inference(cnf_transformation,[],[f46])).
% 2.06/0.63  % SZS output end Proof for theBenchmark
% 2.06/0.63  % (10712)------------------------------
% 2.06/0.63  % (10712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.63  % (10712)Termination reason: Refutation
% 2.06/0.63  
% 2.06/0.63  % (10712)Memory used [KB]: 6908
% 2.06/0.63  % (10712)Time elapsed: 0.203 s
% 2.06/0.63  % (10712)------------------------------
% 2.06/0.63  % (10712)------------------------------
% 2.10/0.63  % (10700)Success in time 0.267 s
%------------------------------------------------------------------------------
