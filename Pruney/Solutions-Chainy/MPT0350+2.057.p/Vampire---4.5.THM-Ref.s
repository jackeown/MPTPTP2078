%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:58 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  127 (1861 expanded)
%              Number of leaves         :   26 ( 551 expanded)
%              Depth                    :   21
%              Number of atoms          :  214 (4197 expanded)
%              Number of equality atoms :  115 (1668 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(subsumption_resolution,[],[f573,f234])).

fof(f234,plain,(
    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f84,f227])).

fof(f227,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f87,f215])).

fof(f215,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f125,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f125,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f92,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f92,plain,(
    r1_tarski(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f89,f83])).

fof(f83,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f89,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f41,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f87,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f59,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f84,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f42,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f573,plain,(
    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f559,f560])).

fof(f560,plain,(
    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f436,f557])).

fof(f557,plain,(
    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f556,f371])).

fof(f371,plain,(
    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f78,f215])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f556,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f555,f439])).

fof(f439,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f438,f376])).

fof(f376,plain,(
    ! [X2] : k5_xboole_0(sK0,k5_xboole_0(X2,sK1)) = k5_xboole_0(X2,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f266,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f266,plain,(
    ! [X1] : k5_xboole_0(sK0,k5_xboole_0(X1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),X1) ),
    inference(backward_demodulation,[],[f225,f227])).

fof(f225,plain,(
    ! [X1] : k5_xboole_0(k3_subset_1(sK0,sK1),X1) = k5_xboole_0(sK0,k5_xboole_0(X1,sK1)) ),
    inference(backward_demodulation,[],[f168,f215])).

fof(f168,plain,(
    ! [X1] : k5_xboole_0(k3_subset_1(sK0,sK1),X1) = k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f106,f47])).

fof(f106,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k3_subset_1(sK0,sK1),X0) ),
    inference(superposition,[],[f65,f87])).

fof(f65,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f438,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f422,f47])).

fof(f422,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f259,f215])).

fof(f259,plain,(
    ! [X0] : k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1)) ),
    inference(backward_demodulation,[],[f173,f227])).

fof(f173,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f167,f46])).

fof(f167,plain,(
    ! [X0] : k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) ),
    inference(superposition,[],[f106,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f555,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f554,f373])).

fof(f373,plain,(
    ! [X0] : k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f369,f46])).

fof(f369,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f66,f215])).

fof(f554,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f553,f277])).

fof(f277,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f146,f274])).

fof(f274,plain,(
    sK1 = k4_subset_1(sK0,sK1,sK1) ),
    inference(backward_demodulation,[],[f86,f221])).

fof(f221,plain,(
    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f78,f125])).

fof(f86,plain,(
    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f41,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f77])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f146,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f122,f65])).

fof(f122,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f117,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f117,plain,(
    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f86,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f553,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))) ),
    inference(forward_demodulation,[],[f531,f65])).

fof(f531,plain,(
    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) ),
    inference(superposition,[],[f229,f276])).

fof(f276,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(backward_demodulation,[],[f122,f274])).

fof(f229,plain,(
    ! [X2] : k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,X2))) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X2,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f223,f225])).

fof(f223,plain,(
    ! [X2] : k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,X2))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK0,sK1),X2),k3_xboole_0(sK0,k5_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f172,f215])).

fof(f172,plain,(
    ! [X2] : k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X2))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK0,sK1),X2),k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X2))) ),
    inference(superposition,[],[f79,f106])).

fof(f436,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f435,f376])).

fof(f435,plain,(
    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f418,f47])).

fof(f418,plain,(
    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f259,f45])).

fof(f559,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f386,f557])).

fof(f386,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f261,f376])).

fof(f261,plain,(
    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f183,f227])).

fof(f183,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),k3_xboole_0(sK1,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f98,f79])).

fof(f98,plain,(
    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f41,f88,f81])).

fof(f88,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:56:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (13475)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (13483)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13478)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (13473)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (13492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (13477)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (13489)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13476)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13493)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (13479)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.54  % (13499)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (13474)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (13501)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (13500)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (13482)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  % (13481)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (13497)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (13502)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (13485)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (13494)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.55  % (13487)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.55  % (13486)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.56  % (13495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.56  % (13498)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.56  % (13490)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.56  % (13495)Refutation not found, incomplete strategy% (13495)------------------------------
% 1.54/0.56  % (13495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (13495)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (13495)Memory used [KB]: 10746
% 1.54/0.56  % (13495)Time elapsed: 0.147 s
% 1.54/0.56  % (13495)------------------------------
% 1.54/0.56  % (13495)------------------------------
% 1.54/0.56  % (13490)Refutation not found, incomplete strategy% (13490)------------------------------
% 1.54/0.56  % (13490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (13490)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (13490)Memory used [KB]: 10618
% 1.54/0.56  % (13490)Time elapsed: 0.152 s
% 1.54/0.56  % (13490)------------------------------
% 1.54/0.56  % (13490)------------------------------
% 1.54/0.56  % (13484)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.57  % (13491)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.54/0.57  % (13488)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.57  % (13496)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  % (13488)Refutation not found, incomplete strategy% (13488)------------------------------
% 1.54/0.57  % (13488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (13488)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (13488)Memory used [KB]: 6140
% 1.54/0.57  % (13488)Time elapsed: 0.006 s
% 1.54/0.57  % (13488)------------------------------
% 1.54/0.57  % (13488)------------------------------
% 1.54/0.57  % (13480)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.58  % (13499)Refutation found. Thanks to Tanya!
% 1.54/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f574,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(subsumption_resolution,[],[f573,f234])).
% 1.54/0.58  fof(f234,plain,(
% 1.54/0.58    sK0 != k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f84,f227])).
% 1.54/0.58  fof(f227,plain,(
% 1.54/0.58    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(backward_demodulation,[],[f87,f215])).
% 1.54/0.58  fof(f215,plain,(
% 1.54/0.58    sK1 = k3_xboole_0(sK0,sK1)),
% 1.54/0.58    inference(superposition,[],[f125,f46])).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.58  fof(f125,plain,(
% 1.54/0.58    sK1 = k3_xboole_0(sK1,sK0)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f92,f57])).
% 1.54/0.58  fof(f57,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f29])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.58  fof(f92,plain,(
% 1.54/0.58    r1_tarski(sK1,sK0)),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f89,f83])).
% 1.54/0.58  fof(f83,plain,(
% 1.54/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(equality_resolution,[],[f60])).
% 1.54/0.58  fof(f60,plain,(
% 1.54/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f40])).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(rectify,[],[f37])).
% 1.54/0.58  fof(f37,plain,(
% 1.54/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.58    inference(nnf_transformation,[],[f16])).
% 1.54/0.58  fof(f16,axiom,(
% 1.54/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.54/0.58  fof(f89,plain,(
% 1.54/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f43,f41,f53])).
% 1.54/0.58  fof(f53,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f36])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.54/0.58    inference(nnf_transformation,[],[f28])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f18])).
% 1.54/0.58  fof(f18,axiom,(
% 1.54/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.54/0.58  fof(f41,plain,(
% 1.54/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(cnf_transformation,[],[f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f25])).
% 1.54/0.58  fof(f25,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.54/0.58    inference(negated_conjecture,[],[f24])).
% 1.54/0.58  fof(f24,conjecture,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 1.54/0.58  fof(f43,plain,(
% 1.54/0.58    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,axiom,(
% 1.54/0.58    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.54/0.58  fof(f87,plain,(
% 1.54/0.58    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f41,f80])).
% 1.54/0.58  fof(f80,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f59,f51])).
% 1.54/0.58  fof(f51,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f31])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.54/0.58  fof(f84,plain,(
% 1.54/0.58    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f42,f44])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f19])).
% 1.54/0.58  fof(f19,axiom,(
% 1.54/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.54/0.58  fof(f42,plain,(
% 1.54/0.58    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.54/0.58    inference(cnf_transformation,[],[f35])).
% 1.54/0.58  fof(f573,plain,(
% 1.54/0.58    sK0 = k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f559,f560])).
% 1.54/0.58  fof(f560,plain,(
% 1.54/0.58    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(backward_demodulation,[],[f436,f557])).
% 1.54/0.58  fof(f557,plain,(
% 1.54/0.58    sK0 = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f556,f371])).
% 1.54/0.58  fof(f371,plain,(
% 1.54/0.58    sK0 = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.54/0.58    inference(superposition,[],[f78,f215])).
% 1.54/0.58  fof(f78,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 1.54/0.58    inference(definition_unfolding,[],[f48,f77])).
% 1.54/0.58  fof(f77,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f49,f76])).
% 1.54/0.58  fof(f76,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f50,f75])).
% 1.54/0.58  fof(f75,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f64,f74])).
% 1.54/0.58  fof(f74,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f68,f73])).
% 1.54/0.58  fof(f73,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f69,f72])).
% 1.54/0.58  fof(f72,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.54/0.58    inference(definition_unfolding,[],[f70,f71])).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f15])).
% 1.54/0.58  fof(f15,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.54/0.58  fof(f70,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.54/0.58  fof(f69,plain,(
% 1.54/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f13])).
% 1.54/0.58  fof(f13,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.54/0.58  fof(f68,plain,(
% 1.54/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f12])).
% 1.54/0.58  fof(f12,axiom,(
% 1.54/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.54/0.58  fof(f64,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f17])).
% 1.54/0.58  fof(f17,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.54/0.58  fof(f556,plain,(
% 1.54/0.58    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(forward_demodulation,[],[f555,f439])).
% 1.54/0.58  fof(f439,plain,(
% 1.54/0.58    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 1.54/0.58    inference(forward_demodulation,[],[f438,f376])).
% 1.54/0.58  fof(f376,plain,(
% 1.54/0.58    ( ! [X2] : (k5_xboole_0(sK0,k5_xboole_0(X2,sK1)) = k5_xboole_0(X2,k5_xboole_0(sK0,sK1))) )),
% 1.54/0.58    inference(superposition,[],[f266,f47])).
% 1.54/0.58  fof(f47,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.58  fof(f266,plain,(
% 1.54/0.58    ( ! [X1] : (k5_xboole_0(sK0,k5_xboole_0(X1,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),X1)) )),
% 1.54/0.58    inference(backward_demodulation,[],[f225,f227])).
% 1.54/0.58  fof(f225,plain,(
% 1.54/0.58    ( ! [X1] : (k5_xboole_0(k3_subset_1(sK0,sK1),X1) = k5_xboole_0(sK0,k5_xboole_0(X1,sK1))) )),
% 1.54/0.58    inference(backward_demodulation,[],[f168,f215])).
% 1.54/0.58  fof(f168,plain,(
% 1.54/0.58    ( ! [X1] : (k5_xboole_0(k3_subset_1(sK0,sK1),X1) = k5_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(sK0,sK1)))) )),
% 1.54/0.58    inference(superposition,[],[f106,f47])).
% 1.54/0.58  fof(f106,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X0)) = k5_xboole_0(k3_subset_1(sK0,sK1),X0)) )),
% 1.54/0.58    inference(superposition,[],[f65,f87])).
% 1.54/0.58  fof(f65,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.58  fof(f438,plain,(
% 1.54/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 1.54/0.58    inference(forward_demodulation,[],[f422,f47])).
% 1.54/0.58  fof(f422,plain,(
% 1.54/0.58    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 1.54/0.58    inference(superposition,[],[f259,f215])).
% 1.54/0.58  fof(f259,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))) )),
% 1.54/0.58    inference(backward_demodulation,[],[f173,f227])).
% 1.54/0.58  fof(f173,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,X0)))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f167,f46])).
% 1.54/0.58  fof(f167,plain,(
% 1.54/0.58    ( ! [X0] : (k5_xboole_0(k3_subset_1(sK0,sK1),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK0,X0),sK1))) )),
% 1.54/0.58    inference(superposition,[],[f106,f66])).
% 1.54/0.58  fof(f66,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.54/0.58  fof(f555,plain,(
% 1.54/0.58    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK0)))),
% 1.54/0.58    inference(forward_demodulation,[],[f554,f373])).
% 1.54/0.58  fof(f373,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(sK1,k5_xboole_0(sK0,X0)) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f369,f46])).
% 1.54/0.58  fof(f369,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.54/0.58    inference(superposition,[],[f66,f215])).
% 1.54/0.58  fof(f554,plain,(
% 1.54/0.58    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(forward_demodulation,[],[f553,f277])).
% 1.54/0.58  fof(f277,plain,(
% 1.54/0.58    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(backward_demodulation,[],[f146,f274])).
% 1.54/0.58  fof(f274,plain,(
% 1.54/0.58    sK1 = k4_subset_1(sK0,sK1,sK1)),
% 1.54/0.58    inference(backward_demodulation,[],[f86,f221])).
% 1.54/0.58  fof(f221,plain,(
% 1.54/0.58    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.54/0.58    inference(superposition,[],[f78,f125])).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK1) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f41,f41,f81])).
% 1.54/0.58  fof(f81,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f67,f77])).
% 1.54/0.58  fof(f67,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f33])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(flattening,[],[f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f23])).
% 1.54/0.58  fof(f23,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.54/0.58  fof(f146,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(superposition,[],[f122,f65])).
% 1.54/0.58  fof(f122,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 1.54/0.58    inference(forward_demodulation,[],[f117,f45])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.58    inference(rectify,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.58  fof(f117,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,sK1) = k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(sK1,sK1))),
% 1.54/0.58    inference(superposition,[],[f86,f79])).
% 1.54/0.58  fof(f79,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.54/0.58    inference(definition_unfolding,[],[f52,f77])).
% 1.54/0.58  fof(f52,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.54/0.58  fof(f553,plain,(
% 1.54/0.58    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))))),
% 1.54/0.58    inference(forward_demodulation,[],[f531,f65])).
% 1.54/0.58  fof(f531,plain,(
% 1.54/0.58    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)))) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))))),
% 1.54/0.58    inference(superposition,[],[f229,f276])).
% 1.54/0.58  fof(f276,plain,(
% 1.54/0.58    sK1 = k5_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 1.54/0.58    inference(backward_demodulation,[],[f122,f274])).
% 1.54/0.58  fof(f229,plain,(
% 1.54/0.58    ( ! [X2] : (k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,X2))) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(X2,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,X2)))) )),
% 1.54/0.58    inference(backward_demodulation,[],[f223,f225])).
% 1.54/0.58  fof(f223,plain,(
% 1.54/0.58    ( ! [X2] : (k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(sK1,X2))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK0,sK1),X2),k3_xboole_0(sK0,k5_xboole_0(sK1,X2)))) )),
% 1.54/0.58    inference(backward_demodulation,[],[f172,f215])).
% 1.54/0.58  fof(f172,plain,(
% 1.54/0.58    ( ! [X2] : (k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X2))) = k5_xboole_0(k5_xboole_0(k3_subset_1(sK0,sK1),X2),k3_xboole_0(sK0,k5_xboole_0(k3_xboole_0(sK0,sK1),X2)))) )),
% 1.54/0.58    inference(superposition,[],[f79,f106])).
% 1.54/0.58  fof(f436,plain,(
% 1.54/0.58    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(forward_demodulation,[],[f435,f376])).
% 1.54/0.58  fof(f435,plain,(
% 1.54/0.58    k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(forward_demodulation,[],[f418,f47])).
% 1.54/0.58  fof(f418,plain,(
% 1.54/0.58    k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(superposition,[],[f259,f45])).
% 1.54/0.58  fof(f559,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(backward_demodulation,[],[f386,f557])).
% 1.54/0.58  fof(f386,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(backward_demodulation,[],[f261,f376])).
% 1.54/0.58  fof(f261,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,k5_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)))),
% 1.54/0.58    inference(backward_demodulation,[],[f183,f227])).
% 1.54/0.58  fof(f183,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),k3_xboole_0(sK1,k3_subset_1(sK0,sK1)))),
% 1.54/0.58    inference(superposition,[],[f98,f79])).
% 1.54/0.58  fof(f98,plain,(
% 1.54/0.58    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f41,f88,f81])).
% 1.54/0.58  fof(f88,plain,(
% 1.54/0.58    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(unit_resulting_resolution,[],[f41,f58])).
% 1.54/0.58  fof(f58,plain,(
% 1.54/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f21])).
% 1.54/0.58  fof(f21,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (13499)------------------------------
% 1.54/0.58  % (13499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (13499)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (13499)Memory used [KB]: 11257
% 1.54/0.58  % (13499)Time elapsed: 0.145 s
% 1.54/0.58  % (13499)------------------------------
% 1.54/0.58  % (13499)------------------------------
% 1.54/0.58  % (13472)Success in time 0.218 s
%------------------------------------------------------------------------------
