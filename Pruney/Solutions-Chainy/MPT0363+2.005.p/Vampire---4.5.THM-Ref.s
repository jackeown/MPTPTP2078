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
% DateTime   : Thu Dec  3 12:45:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 907 expanded)
%              Number of leaves         :   24 ( 267 expanded)
%              Depth                    :   30
%              Number of atoms          :  230 (2557 expanded)
%              Number of equality atoms :   54 ( 386 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f323,plain,(
    $false ),
    inference(resolution,[],[f318,f315])).

fof(f315,plain,(
    ~ r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f314,f124])).

fof(f124,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f44,f121])).

fof(f121,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f118,f111])).

fof(f111,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f104,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f104,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f60,f94])).

fof(f94,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f93,f45])).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f93,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f92,f47])).

fof(f47,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f92,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f86,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f118,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f78,f42])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f61,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f44,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f314,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f310,f46])).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f310,plain,
    ( ~ r1_xboole_0(sK1,k1_xboole_0)
    | r1_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f305,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f50,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f49,f54,f75])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f305,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK2,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f151,f304])).

fof(f304,plain,(
    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f269,f60])).

fof(f269,plain,(
    r1_tarski(sK2,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f267,f105])).

fof(f105,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f103,f48])).

fof(f103,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f60,f89])).

fof(f89,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(forward_demodulation,[],[f87,f47])).

fof(f87,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f85,f59])).

fof(f85,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f267,plain,(
    r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f266,f133])).

fof(f133,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(sK2,X2)
      | r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2))) ) ),
    inference(resolution,[],[f79,f94])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f64,f54])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f266,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f265,f46])).

fof(f265,plain,
    ( ~ r1_xboole_0(sK2,k1_xboole_0)
    | r1_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f264,f81])).

fof(f264,plain,
    ( ~ r1_xboole_0(sK2,k5_xboole_0(sK1,sK1))
    | r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f154,f235])).

fof(f235,plain,(
    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,
    ( sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))
    | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f138,f60])).

fof(f138,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK0,sK2))
    | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f136,f111])).

fof(f136,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))
    | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f131,f122])).

fof(f122,plain,
    ( r1_xboole_0(sK1,sK2)
    | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f102,f121])).

fof(f102,plain,
    ( sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f60,f43])).

fof(f43,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f131,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK1,X0)
      | r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ) ),
    inference(resolution,[],[f79,f89])).

fof(f154,plain,(
    ! [X11] :
      ( ~ r1_xboole_0(sK2,k5_xboole_0(X11,k3_xboole_0(X11,k5_xboole_0(sK0,sK2))))
      | r1_xboole_0(sK2,X11) ) ),
    inference(resolution,[],[f80,f113])).

fof(f113,plain,(
    r1_xboole_0(sK2,k5_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f82,f104])).

fof(f82,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f51,f48])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f54])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f151,plain,(
    ! [X8] :
      ( ~ r1_xboole_0(sK1,k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(sK0,sK1))))
      | r1_xboole_0(sK1,X8) ) ),
    inference(resolution,[],[f80,f107])).

fof(f107,plain,(
    r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f82,f103])).

fof(f318,plain,(
    r1_tarski(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f316,f111])).

fof(f316,plain,(
    r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f314,f131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (22860)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (22860)Refutation not found, incomplete strategy% (22860)------------------------------
% 0.20/0.41  % (22860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (22860)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (22860)Memory used [KB]: 10746
% 0.20/0.41  % (22860)Time elapsed: 0.005 s
% 0.20/0.41  % (22860)------------------------------
% 0.20/0.41  % (22860)------------------------------
% 0.20/0.44  % (22850)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (22850)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f323,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(resolution,[],[f318,f315])).
% 0.20/0.45  fof(f315,plain,(
% 0.20/0.45    ~r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(resolution,[],[f314,f124])).
% 0.20/0.45  fof(f124,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(backward_demodulation,[],[f44,f121])).
% 0.20/0.45  fof(f121,plain,(
% 0.20/0.45    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.20/0.45    inference(forward_demodulation,[],[f118,f111])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    sK2 = k3_xboole_0(sK0,sK2)),
% 0.20/0.45    inference(superposition,[],[f104,f48])).
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    sK2 = k3_xboole_0(sK2,sK0)),
% 0.20/0.45    inference(resolution,[],[f60,f94])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    r1_tarski(sK2,sK0)),
% 0.20/0.45    inference(resolution,[],[f93,f45])).
% 0.20/0.45  fof(f45,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f21])).
% 0.20/0.45  fof(f21,axiom,(
% 0.20/0.45    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK0)),
% 0.20/0.45    inference(forward_demodulation,[],[f92,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,axiom,(
% 0.20/0.45    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK2,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(resolution,[],[f86,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f55,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f38,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(flattening,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f24])).
% 0.20/0.45  fof(f24,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f23])).
% 0.20/0.45  fof(f23,conjecture,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f40])).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(nnf_transformation,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,axiom,(
% 0.20/0.45    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.45  fof(f118,plain,(
% 0.20/0.45    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(resolution,[],[f78,f42])).
% 0.20/0.45  fof(f78,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f61,f54])).
% 0.20/0.45  fof(f54,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.45  fof(f61,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,sK2) | ~r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f314,plain,(
% 0.20/0.45    r1_xboole_0(sK1,sK2)),
% 0.20/0.45    inference(resolution,[],[f310,f46])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.45  fof(f310,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,k1_xboole_0) | r1_xboole_0(sK1,sK2)),
% 0.20/0.45    inference(forward_demodulation,[],[f305,f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.45    inference(backward_demodulation,[],[f76,f77])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X0) )),
% 0.20/0.45    inference(definition_unfolding,[],[f50,f75])).
% 0.20/0.45  fof(f75,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f52,f74])).
% 0.20/0.45  fof(f74,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f53,f73])).
% 0.20/0.45  fof(f73,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f63,f72])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f66,f71])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f67,f70])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(definition_unfolding,[],[f68,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.45  fof(f63,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.45  fof(f76,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f49,f54,f75])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.45  fof(f305,plain,(
% 0.20/0.45    ~r1_xboole_0(sK1,k5_xboole_0(sK2,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.20/0.45    inference(superposition,[],[f151,f304])).
% 0.20/0.45  fof(f304,plain,(
% 0.20/0.45    sK2 = k3_xboole_0(sK2,k5_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(resolution,[],[f269,f60])).
% 0.20/0.45  fof(f269,plain,(
% 0.20/0.45    r1_tarski(sK2,k5_xboole_0(sK0,sK1))),
% 0.20/0.45    inference(forward_demodulation,[],[f267,f105])).
% 0.20/0.45  fof(f105,plain,(
% 0.20/0.45    sK1 = k3_xboole_0(sK0,sK1)),
% 0.20/0.45    inference(superposition,[],[f103,f48])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    sK1 = k3_xboole_0(sK1,sK0)),
% 0.20/0.45    inference(resolution,[],[f60,f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    r1_tarski(sK1,sK0)),
% 0.20/0.45    inference(resolution,[],[f88,f45])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK0)),
% 0.20/0.45    inference(forward_demodulation,[],[f87,f47])).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,k3_tarski(k1_zfmisc_1(sK0)))),
% 0.20/0.45    inference(resolution,[],[f85,f59])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(resolution,[],[f55,f41])).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f39])).
% 0.20/0.45  fof(f267,plain,(
% 0.20/0.45    r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 0.20/0.45    inference(resolution,[],[f266,f133])).
% 0.20/0.45  fof(f133,plain,(
% 0.20/0.45    ( ! [X2] : (~r1_xboole_0(sK2,X2) | r1_tarski(sK2,k5_xboole_0(sK0,k3_xboole_0(sK0,X2)))) )),
% 0.20/0.45    inference(resolution,[],[f79,f94])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f64,f54])).
% 0.20/0.45  fof(f64,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.20/0.45  fof(f266,plain,(
% 0.20/0.45    r1_xboole_0(sK2,sK1)),
% 0.20/0.45    inference(resolution,[],[f265,f46])).
% 0.20/0.45  fof(f265,plain,(
% 0.20/0.45    ~r1_xboole_0(sK2,k1_xboole_0) | r1_xboole_0(sK2,sK1)),
% 0.20/0.45    inference(forward_demodulation,[],[f264,f81])).
% 0.20/0.45  fof(f264,plain,(
% 0.20/0.45    ~r1_xboole_0(sK2,k5_xboole_0(sK1,sK1)) | r1_xboole_0(sK2,sK1)),
% 0.20/0.45    inference(superposition,[],[f154,f235])).
% 0.20/0.46  fof(f235,plain,(
% 0.20/0.46    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f234])).
% 0.20/0.46  fof(f234,plain,(
% 0.20/0.46    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(resolution,[],[f138,f60])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    r1_tarski(sK1,k5_xboole_0(sK0,sK2)) | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f136,f111])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))) | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(resolution,[],[f131,f122])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    r1_xboole_0(sK1,sK2) | sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(backward_demodulation,[],[f102,f121])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(resolution,[],[f60,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f39])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    ( ! [X0] : (~r1_xboole_0(sK1,X0) | r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) )),
% 0.20/0.46    inference(resolution,[],[f79,f89])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    ( ! [X11] : (~r1_xboole_0(sK2,k5_xboole_0(X11,k3_xboole_0(X11,k5_xboole_0(sK0,sK2)))) | r1_xboole_0(sK2,X11)) )),
% 0.20/0.46    inference(resolution,[],[f80,f113])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    r1_xboole_0(sK2,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(superposition,[],[f82,f104])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(superposition,[],[f51,f48])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f65,f54])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    ( ! [X8] : (~r1_xboole_0(sK1,k5_xboole_0(X8,k3_xboole_0(X8,k5_xboole_0(sK0,sK1)))) | r1_xboole_0(sK1,X8)) )),
% 0.20/0.46    inference(resolution,[],[f80,f107])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 0.20/0.46    inference(superposition,[],[f82,f103])).
% 0.20/0.46  fof(f318,plain,(
% 0.20/0.46    r1_tarski(sK1,k5_xboole_0(sK0,sK2))),
% 0.20/0.46    inference(forward_demodulation,[],[f316,f111])).
% 0.20/0.46  fof(f316,plain,(
% 0.20/0.46    r1_tarski(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)))),
% 0.20/0.46    inference(resolution,[],[f314,f131])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (22850)------------------------------
% 0.20/0.46  % (22850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22850)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (22850)Memory used [KB]: 1918
% 0.20/0.46  % (22850)Time elapsed: 0.054 s
% 0.20/0.46  % (22850)------------------------------
% 0.20/0.46  % (22850)------------------------------
% 0.20/0.46  % (22848)Success in time 0.104 s
%------------------------------------------------------------------------------
