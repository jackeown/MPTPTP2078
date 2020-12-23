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
% DateTime   : Thu Dec  3 12:56:02 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 147 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  193 ( 414 expanded)
%              Number of equality atoms :   51 ( 119 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(global_subsumption,[],[f31,f101])).

fof(f101,plain,(
    sK0 = k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f100,f79])).

fof(f79,plain,(
    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) ),
    inference(global_subsumption,[],[f30,f78])).

fof(f78,plain,
    ( sK0 = k7_relat_1(sK0,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f74,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f64,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0,k3_relat_1(sK0)),k1_relat_1(sK0))
      | r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f62,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X1] :
      ( r2_hidden(X1,k3_relat_1(sK0))
      | ~ r2_hidden(X1,k1_relat_1(sK0)) ) ),
    inference(superposition,[],[f57,f60])).

fof(f60,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f30,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

% (1412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (1419)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (1404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (1399)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (1412)Refutation not found, incomplete strategy% (1412)------------------------------
% (1412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1412)Termination reason: Refutation not found, incomplete strategy

% (1412)Memory used [KB]: 10618
% (1412)Time elapsed: 0.163 s
% (1412)------------------------------
% (1412)------------------------------
% (1404)Refutation not found, incomplete strategy% (1404)------------------------------
% (1404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1422)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (1410)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (1404)Termination reason: Refutation not found, incomplete strategy

% (1404)Memory used [KB]: 10618
% (1404)Time elapsed: 0.171 s
% (1404)------------------------------
% (1404)------------------------------
% (1411)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (1410)Refutation not found, incomplete strategy% (1410)------------------------------
% (1410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1410)Termination reason: Refutation not found, incomplete strategy

% (1410)Memory used [KB]: 6140
% (1410)Time elapsed: 0.003 s
% (1410)------------------------------
% (1410)------------------------------
% (1401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f30,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( k2_wellord1(X0,k3_relat_1(X0)) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k2_wellord1(sK0,k3_relat_1(sK0))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).

fof(f100,plain,(
    k2_wellord1(sK0,k3_relat_1(sK0)) = k7_relat_1(sK0,k3_relat_1(sK0)) ),
    inference(superposition,[],[f59,f89])).

fof(f89,plain,(
    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) ),
    inference(global_subsumption,[],[f30,f88])).

fof(f88,plain,
    ( sK0 = k8_relat_1(k3_relat_1(sK0),sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f77,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f77,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))
    | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) ),
    inference(resolution,[],[f67,f38])).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0,k3_relat_1(sK0)),k2_relat_1(sK0))
      | r1_tarski(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X2] :
      ( r2_hidden(X2,k3_relat_1(sK0))
      | ~ r2_hidden(X2,k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f56,f60])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0] : k2_wellord1(sK0,X0) = k7_relat_1(k8_relat_1(X0,sK0),X0) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f31,plain,(
    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:17:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.45/0.56  % (1398)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.45/0.56  % (1413)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.57  % (1405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.57  % (1407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.57  % (1400)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.45/0.57  % (1405)Refutation not found, incomplete strategy% (1405)------------------------------
% 1.45/0.57  % (1405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (1397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.45/0.57  % (1405)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (1405)Memory used [KB]: 10618
% 1.45/0.57  % (1405)Time elapsed: 0.149 s
% 1.45/0.57  % (1405)------------------------------
% 1.45/0.57  % (1405)------------------------------
% 1.45/0.58  % (1421)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.58  % (1397)Refutation found. Thanks to Tanya!
% 1.45/0.58  % SZS status Theorem for theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f102,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(global_subsumption,[],[f31,f101])).
% 1.45/0.58  fof(f101,plain,(
% 1.45/0.58    sK0 = k2_wellord1(sK0,k3_relat_1(sK0))),
% 1.45/0.58    inference(forward_demodulation,[],[f100,f79])).
% 1.45/0.58  fof(f79,plain,(
% 1.45/0.58    sK0 = k7_relat_1(sK0,k3_relat_1(sK0))),
% 1.45/0.58    inference(global_subsumption,[],[f30,f78])).
% 1.45/0.58  fof(f78,plain,(
% 1.45/0.58    sK0 = k7_relat_1(sK0,k3_relat_1(sK0)) | ~v1_relat_1(sK0)),
% 1.45/0.58    inference(resolution,[],[f74,f37])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.45/0.58    inference(flattening,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.45/0.58    inference(ennf_transformation,[],[f8])).
% 1.45/0.58  fof(f8,axiom,(
% 1.45/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.45/0.58  fof(f74,plain,(
% 1.45/0.58    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))),
% 1.45/0.58    inference(duplicate_literal_removal,[],[f73])).
% 1.45/0.58  fof(f73,plain,(
% 1.45/0.58    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0)) | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK0))),
% 1.45/0.58    inference(resolution,[],[f64,f38])).
% 1.45/0.58  fof(f38,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f23])).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.45/0.58    introduced(choice_axiom,[])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,plain,(
% 1.45/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.45/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.58  fof(f64,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(sK1(X0,k3_relat_1(sK0)),k1_relat_1(sK0)) | r1_tarski(X0,k3_relat_1(sK0))) )),
% 1.45/0.58    inference(resolution,[],[f62,f39])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f24])).
% 1.45/0.58  fof(f62,plain,(
% 1.45/0.58    ( ! [X1] : (r2_hidden(X1,k3_relat_1(sK0)) | ~r2_hidden(X1,k1_relat_1(sK0))) )),
% 1.45/0.58    inference(superposition,[],[f57,f60])).
% 1.45/0.58  fof(f60,plain,(
% 1.45/0.58    k3_relat_1(sK0) = k3_tarski(k2_enumset1(k1_relat_1(sK0),k1_relat_1(sK0),k1_relat_1(sK0),k2_relat_1(sK0)))),
% 1.45/0.58    inference(resolution,[],[f30,f49])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f32,f48])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f33,f47])).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f34,f40])).
% 1.45/0.58  fof(f40,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.58  fof(f33,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f5])).
% 1.45/0.58  fof(f5,axiom,(
% 1.45/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.45/0.58  fof(f32,plain,(
% 1.45/0.58    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f14])).
% 1.45/0.58  fof(f14,plain,(
% 1.45/0.58    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,axiom,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.45/0.58  fof(f57,plain,(
% 1.45/0.58    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.45/0.58    inference(equality_resolution,[],[f54])).
% 1.45/0.58  fof(f54,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.45/0.58    inference(definition_unfolding,[],[f42,f48])).
% 1.45/0.58  fof(f42,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.45/0.58    inference(cnf_transformation,[],[f29])).
% 1.45/0.58  fof(f29,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.45/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.45/0.58  % (1412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.58  % (1419)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.59  % (1404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.59  % (1399)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.45/0.59  % (1412)Refutation not found, incomplete strategy% (1412)------------------------------
% 1.45/0.59  % (1412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (1412)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.59  
% 1.45/0.59  % (1412)Memory used [KB]: 10618
% 1.45/0.59  % (1412)Time elapsed: 0.163 s
% 1.45/0.59  % (1412)------------------------------
% 1.45/0.59  % (1412)------------------------------
% 1.45/0.59  % (1404)Refutation not found, incomplete strategy% (1404)------------------------------
% 1.45/0.59  % (1404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (1422)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.59  % (1410)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.59  % (1404)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.59  
% 1.45/0.59  % (1404)Memory used [KB]: 10618
% 1.45/0.59  % (1404)Time elapsed: 0.171 s
% 1.45/0.59  % (1404)------------------------------
% 1.45/0.59  % (1404)------------------------------
% 1.45/0.59  % (1411)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.59  % (1410)Refutation not found, incomplete strategy% (1410)------------------------------
% 1.45/0.59  % (1410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (1410)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.59  
% 1.45/0.59  % (1410)Memory used [KB]: 6140
% 1.45/0.59  % (1410)Time elapsed: 0.003 s
% 1.45/0.59  % (1410)------------------------------
% 1.45/0.59  % (1410)------------------------------
% 1.45/0.59  % (1401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.59  fof(f28,plain,(
% 1.45/0.59    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f27,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(rectify,[],[f26])).
% 1.45/0.59  fof(f26,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(flattening,[],[f25])).
% 1.45/0.59  fof(f25,plain,(
% 1.45/0.59    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.45/0.59    inference(nnf_transformation,[],[f2])).
% 1.45/0.59  fof(f2,axiom,(
% 1.45/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.45/0.59  fof(f30,plain,(
% 1.45/0.59    v1_relat_1(sK0)),
% 1.45/0.59    inference(cnf_transformation,[],[f22])).
% 1.45/0.59  fof(f22,plain,(
% 1.45/0.59    sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0)),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f21])).
% 1.45/0.59  fof(f21,plain,(
% 1.45/0.59    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0)) => (sK0 != k2_wellord1(sK0,k3_relat_1(sK0)) & v1_relat_1(sK0))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f13,plain,(
% 1.45/0.59    ? [X0] : (k2_wellord1(X0,k3_relat_1(X0)) != X0 & v1_relat_1(X0))),
% 1.45/0.59    inference(ennf_transformation,[],[f11])).
% 1.45/0.59  fof(f11,negated_conjecture,(
% 1.45/0.59    ~! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 1.45/0.59    inference(negated_conjecture,[],[f10])).
% 1.45/0.59  fof(f10,conjecture,(
% 1.45/0.59    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_wellord1)).
% 1.45/0.59  fof(f100,plain,(
% 1.45/0.59    k2_wellord1(sK0,k3_relat_1(sK0)) = k7_relat_1(sK0,k3_relat_1(sK0))),
% 1.45/0.59    inference(superposition,[],[f59,f89])).
% 1.45/0.59  fof(f89,plain,(
% 1.45/0.59    sK0 = k8_relat_1(k3_relat_1(sK0),sK0)),
% 1.45/0.59    inference(global_subsumption,[],[f30,f88])).
% 1.45/0.59  fof(f88,plain,(
% 1.45/0.59    sK0 = k8_relat_1(k3_relat_1(sK0),sK0) | ~v1_relat_1(sK0)),
% 1.45/0.59    inference(resolution,[],[f77,f36])).
% 1.45/0.59  fof(f36,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f17])).
% 1.45/0.59  fof(f17,plain,(
% 1.45/0.59    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(flattening,[],[f16])).
% 1.45/0.59  fof(f16,plain,(
% 1.45/0.59    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f7])).
% 1.45/0.59  fof(f7,axiom,(
% 1.45/0.59    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.45/0.59  fof(f77,plain,(
% 1.45/0.59    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 1.45/0.59    inference(duplicate_literal_removal,[],[f75])).
% 1.45/0.59  fof(f75,plain,(
% 1.45/0.59    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0)) | r1_tarski(k2_relat_1(sK0),k3_relat_1(sK0))),
% 1.45/0.59    inference(resolution,[],[f67,f38])).
% 1.45/0.59  fof(f67,plain,(
% 1.45/0.59    ( ! [X0] : (~r2_hidden(sK1(X0,k3_relat_1(sK0)),k2_relat_1(sK0)) | r1_tarski(X0,k3_relat_1(sK0))) )),
% 1.45/0.59    inference(resolution,[],[f63,f39])).
% 1.45/0.59  fof(f63,plain,(
% 1.45/0.59    ( ! [X2] : (r2_hidden(X2,k3_relat_1(sK0)) | ~r2_hidden(X2,k2_relat_1(sK0))) )),
% 1.45/0.59    inference(superposition,[],[f56,f60])).
% 1.45/0.59  fof(f56,plain,(
% 1.45/0.59    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_enumset1(X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.45/0.59    inference(equality_resolution,[],[f53])).
% 1.45/0.59  fof(f53,plain,(
% 1.45/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 1.45/0.59    inference(definition_unfolding,[],[f43,f48])).
% 1.45/0.59  fof(f43,plain,(
% 1.45/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.45/0.59    inference(cnf_transformation,[],[f29])).
% 1.45/0.59  fof(f59,plain,(
% 1.45/0.59    ( ! [X0] : (k2_wellord1(sK0,X0) = k7_relat_1(k8_relat_1(X0,sK0),X0)) )),
% 1.45/0.59    inference(resolution,[],[f30,f35])).
% 1.45/0.59  fof(f35,plain,(
% 1.45/0.59    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f15])).
% 1.45/0.59  fof(f15,plain,(
% 1.45/0.59    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 1.45/0.59    inference(ennf_transformation,[],[f9])).
% 1.45/0.59  fof(f9,axiom,(
% 1.45/0.59    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 1.45/0.59  fof(f31,plain,(
% 1.45/0.59    sK0 != k2_wellord1(sK0,k3_relat_1(sK0))),
% 1.45/0.59    inference(cnf_transformation,[],[f22])).
% 1.45/0.59  % SZS output end Proof for theBenchmark
% 1.45/0.59  % (1397)------------------------------
% 1.45/0.59  % (1397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (1397)Termination reason: Refutation
% 1.45/0.59  
% 1.45/0.59  % (1397)Memory used [KB]: 10746
% 1.45/0.59  % (1397)Time elapsed: 0.154 s
% 1.45/0.59  % (1397)------------------------------
% 1.45/0.59  % (1397)------------------------------
% 1.45/0.60  % (1395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.45/0.60  % (1424)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.60  % (1395)Refutation not found, incomplete strategy% (1395)------------------------------
% 1.45/0.60  % (1395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (1395)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.60  
% 1.45/0.60  % (1395)Memory used [KB]: 1663
% 1.45/0.60  % (1395)Time elapsed: 0.172 s
% 1.45/0.60  % (1395)------------------------------
% 1.45/0.60  % (1395)------------------------------
% 1.45/0.60  % (1394)Success in time 0.232 s
%------------------------------------------------------------------------------
