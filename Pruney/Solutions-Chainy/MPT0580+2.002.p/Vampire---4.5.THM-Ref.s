%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   94 (1037 expanded)
%              Number of leaves         :   17 ( 293 expanded)
%              Depth                    :   28
%              Number of atoms          :  255 (3415 expanded)
%              Number of equality atoms :   59 ( 995 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f187])).

fof(f187,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f41,f185])).

fof(f185,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f181,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).

% (21003)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f27,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (21013)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f28,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).

fof(f181,plain,
    ( v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f180,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f45,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f47,plain,(
    ! [X0] :
      ( v3_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

% (21000)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).

% (21016)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f180,plain,(
    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f177,f48])).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f177,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f80,f176])).

fof(f176,plain,(
    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f173,f116])).

fof(f116,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f114,f41])).

fof(f114,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f113,f38])).

fof(f113,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f81,f69])).

fof(f81,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f39,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = X2
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f173,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f170,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f44,f48])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f170,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f153,f118])).

fof(f118,plain,
    ( r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,
    ( k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f114,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v3_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f66,f64])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f153,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(X0))
      | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f120,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f54,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f115,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f114,f40])).

fof(f40,plain,
    ( ~ v3_relat_1(sK0)
    | r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
      | r1_tarski(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X2))
      | ~ r1_tarski(X3,X2) ) ),
    inference(subsumption_resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f77,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(k1_zfmisc_1(X2))
      | r2_hidden(X3,k1_zfmisc_1(X2))
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f41,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f199,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f194,f82])).

fof(f194,plain,(
    r1_tarski(sK1,k1_xboole_0) ),
    inference(resolution,[],[f191,f180])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(X0))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f190,f71])).

fof(f190,plain,(
    ! [X0] :
      ( r2_hidden(sK1,X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f186,f49])).

fof(f186,plain,(
    r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f40,f185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:27:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (20994)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (21005)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (21001)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (20996)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (21015)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (20997)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (21007)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20997)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (20992)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (20995)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f199,f187])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    k1_xboole_0 != sK1),
% 0.22/0.53    inference(subsumption_resolution,[],[f41,f185])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    v3_relat_1(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f181,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    v1_relat_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ((k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f28,f27])).
% 0.22/0.53  % (21003)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0)) => ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) | ~v3_relat_1(sK0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(sK0))) | v3_relat_1(sK0)) & v1_relat_1(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 1.32/0.54  % (21013)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(sK0))) => (k1_xboole_0 != sK1 & r2_hidden(sK1,k2_relat_1(sK0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X2] : (k1_xboole_0 = X2 | ~r2_hidden(X2,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 1.32/0.54    inference(rectify,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ? [X0] : ((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0)) & v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ? [X0] : (((? [X1] : (k1_xboole_0 != X1 & r2_hidden(X1,k2_relat_1(X0))) | ~v3_relat_1(X0)) & (! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0))) | v3_relat_1(X0))) & v1_relat_1(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ? [X0] : ((v3_relat_1(X0) <~> ! [X1] : (k1_xboole_0 = X1 | ~r2_hidden(X1,k2_relat_1(X0)))) & v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,negated_conjecture,(
% 1.32/0.54    ~! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 1.32/0.54    inference(negated_conjecture,[],[f16])).
% 1.32/0.54  fof(f16,conjecture,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> ! [X1] : (r2_hidden(X1,k2_relat_1(X0)) => k1_xboole_0 = X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t184_relat_1)).
% 1.32/0.54  fof(f181,plain,(
% 1.32/0.54    v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 1.32/0.54    inference(resolution,[],[f180,f69])).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f65,f64])).
% 1.32/0.54  fof(f64,plain,(
% 1.32/0.54    k1_zfmisc_1(k1_xboole_0) = k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.32/0.54    inference(definition_unfolding,[],[f45,f63])).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f56,f62])).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f58,f61])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f59,f60])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.54  fof(f58,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.32/0.54    inference(cnf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f47,f63])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ( ! [X0] : (v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f32])).
% 1.32/0.54  % (21000)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0] : (((v3_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) & (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ! [X0] : ((v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,axiom,(
% 1.32/0.54    ! [X0] : (v1_relat_1(X0) => (v3_relat_1(X0) <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_relat_1)).
% 1.32/0.54  % (21016)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.54  fof(f180,plain,(
% 1.32/0.54    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f177,f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.54  fof(f177,plain,(
% 1.32/0.54    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(superposition,[],[f80,f176])).
% 1.32/0.54  fof(f176,plain,(
% 1.32/0.54    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f173,f116])).
% 1.32/0.54  fof(f116,plain,(
% 1.32/0.54    k1_xboole_0 != sK1 | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(resolution,[],[f114,f41])).
% 1.32/0.54  fof(f114,plain,(
% 1.32/0.54    v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f113,f38])).
% 1.32/0.54  fof(f113,plain,(
% 1.32/0.54    v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f109])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | v3_relat_1(sK0) | ~v1_relat_1(sK0)),
% 1.32/0.54    inference(resolution,[],[f81,f69])).
% 1.32/0.54  fof(f81,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),X0) | v3_relat_1(sK0) | k1_xboole_0 = sK2(k2_relat_1(sK0),X0)) )),
% 1.32/0.54    inference(resolution,[],[f39,f50])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(rectify,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(nnf_transformation,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK0)) | k1_xboole_0 = X2 | v3_relat_1(sK0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f173,plain,(
% 1.32/0.54    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK1),
% 1.32/0.54    inference(resolution,[],[f170,f82])).
% 1.32/0.54  fof(f82,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.32/0.54    inference(resolution,[],[f44,f48])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(flattening,[],[f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(nnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.54  fof(f170,plain,(
% 1.32/0.54    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(duplicate_literal_removal,[],[f168])).
% 1.32/0.54  fof(f168,plain,(
% 1.32/0.54    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(resolution,[],[f153,f118])).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f117,f38])).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(sK0)),
% 1.32/0.54    inference(resolution,[],[f114,f70])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X0] : (~v3_relat_1(X0) | r1_tarski(k2_relat_1(X0),k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f66,f64])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f46,f63])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) | ~v3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f32])).
% 1.32/0.54  fof(f153,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(X0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | r1_tarski(sK1,X0)) )),
% 1.32/0.54    inference(resolution,[],[f120,f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(resolution,[],[f54,f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f21])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,axiom,(
% 1.32/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.32/0.54    inference(nnf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.32/0.54  fof(f120,plain,(
% 1.32/0.54    ( ! [X0] : (r2_hidden(sK1,X0) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(sK0),X0)) )),
% 1.32/0.54    inference(resolution,[],[f115,f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  fof(f115,plain,(
% 1.32/0.54    r2_hidden(sK1,k2_relat_1(sK0)) | k1_xboole_0 = sK2(k2_relat_1(sK0),k1_zfmisc_1(k1_xboole_0))),
% 1.32/0.54    inference(resolution,[],[f114,f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ~v3_relat_1(sK0) | r2_hidden(sK1,k2_relat_1(sK0))),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f80,plain,(
% 1.32/0.54    ( ! [X2,X3] : (~r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | r1_tarski(X2,k1_zfmisc_1(X3))) )),
% 1.32/0.54    inference(resolution,[],[f78,f51])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f36])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X2,X3] : (r2_hidden(X3,k1_zfmisc_1(X2)) | ~r1_tarski(X3,X2)) )),
% 1.32/0.54    inference(subsumption_resolution,[],[f77,f57])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ( ! [X2,X3] : (v1_xboole_0(k1_zfmisc_1(X2)) | r2_hidden(X3,k1_zfmisc_1(X2)) | ~r1_tarski(X3,X2)) )),
% 1.32/0.54    inference(resolution,[],[f53,f55])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.32/0.54    inference(flattening,[],[f22])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.32/0.54    inference(ennf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ~v3_relat_1(sK0) | k1_xboole_0 != sK1),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f199,plain,(
% 1.32/0.54    k1_xboole_0 = sK1),
% 1.32/0.54    inference(resolution,[],[f194,f82])).
% 1.32/0.54  fof(f194,plain,(
% 1.32/0.54    r1_tarski(sK1,k1_xboole_0)),
% 1.32/0.54    inference(resolution,[],[f191,f180])).
% 1.32/0.54  fof(f191,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK0),k1_zfmisc_1(X0)) | r1_tarski(sK1,X0)) )),
% 1.32/0.54    inference(resolution,[],[f190,f71])).
% 1.32/0.54  fof(f190,plain,(
% 1.32/0.54    ( ! [X0] : (r2_hidden(sK1,X0) | ~r1_tarski(k2_relat_1(sK0),X0)) )),
% 1.32/0.54    inference(resolution,[],[f186,f49])).
% 1.32/0.54  fof(f186,plain,(
% 1.32/0.54    r2_hidden(sK1,k2_relat_1(sK0))),
% 1.32/0.54    inference(subsumption_resolution,[],[f40,f185])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (20997)------------------------------
% 1.32/0.54  % (20997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (20997)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (20997)Memory used [KB]: 6268
% 1.32/0.54  % (20997)Time elapsed: 0.119 s
% 1.32/0.54  % (20997)------------------------------
% 1.32/0.54  % (20997)------------------------------
% 1.32/0.54  % (21014)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (20990)Success in time 0.17 s
%------------------------------------------------------------------------------
