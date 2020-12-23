%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:22 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 267 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 ( 511 expanded)
%              Number of equality atoms :   68 ( 263 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f120,f123,f45,f130,f161,f101])).

fof(f101,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ sP2(X6,X5,X8)
      | ~ sP1(X8,X5,X6)
      | X7 = X8
      | ~ sP1(X7,X5,X6)
      | ~ sP2(X6,X5,X7) ) ),
    inference(superposition,[],[f57,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k7_setfam_1(X1,X0) = X2
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_setfam_1(X1,X0) = X2
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k7_setfam_1(X1,X0) != X2 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( ( k7_setfam_1(X0,X1) = X2
          | ~ sP1(X2,X0,X1) )
        & ( sP1(X2,X0,X1)
          | k7_setfam_1(X0,X1) != X2 ) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( k7_setfam_1(X0,X1) = X2
      <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f161,plain,(
    ! [X0] : sP1(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f152,f126])).

fof(f126,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f85,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f68,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

% (17899)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (17896)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (17912)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (17914)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (17917)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (17907)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f66,f80,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f78])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f43])).

% (17911)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f43,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

% (17915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f152,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK6(X8,X9,k1_xboole_0),X8)
      | sP1(X8,X9,k1_xboole_0) ) ),
    inference(resolution,[],[f112,f126])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,sK6(X1,X0,X2)),X2)
      | r2_hidden(sK6(X1,X0,X2),X1)
      | sP1(X1,X0,X2) ) ),
    inference(resolution,[],[f63,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,sK6(X0,X1,X2),X1,X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ sP0(X2,sK6(X0,X1,X2),X1,X0)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ sP0(X2,X3,X1,X0)
          & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => ( ~ sP0(X2,sK6(X0,X1,X2),X1,X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ sP0(X2,X3,X1,X0)
            & m1_subset_1(X3,k1_zfmisc_1(X1)) ) )
      & ( ! [X4] :
            ( sP0(X2,X4,X1,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ sP0(X1,X3,X0,X2)
            & m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
      & ( ! [X3] :
            ( sP0(X1,X3,X0,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ! [X3] :
          ( sP0(X1,X3,X0,X2)
          | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | r2_hidden(k3_subset_1(X2,X1),X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ~ r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | r2_hidden(X1,X3) ) ) )
      & ( ( ( r2_hidden(X1,X3)
            | ~ r2_hidden(k3_subset_1(X2,X1),X0) )
          & ( r2_hidden(k3_subset_1(X2,X1),X0)
            | ~ r2_hidden(X1,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0,X2] :
      ( ( sP0(X1,X3,X0,X2)
        | ( ( ~ r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | r2_hidden(X3,X2) ) ) )
      & ( ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k3_subset_1(X0,X3),X1) )
          & ( r2_hidden(k3_subset_1(X0,X3),X1)
            | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X3,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X3,X0,X2] :
      ( sP0(X1,X3,X0,X2)
    <=> ( r2_hidden(X3,X2)
      <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f130,plain,(
    ! [X0] : sP2(k1_xboole_0,X0,k1_xboole_0) ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f49,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | sP2(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f65,f83])).

% (17913)Refutation not found, incomplete strategy% (17913)------------------------------
% (17913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17913)Termination reason: Refutation not found, incomplete strategy

% (17913)Memory used [KB]: 10618
% (17913)Time elapsed: 0.142 s
% (17913)------------------------------
% (17913)------------------------------
fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | sP2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP2(X1,X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(definition_folding,[],[f24,f29,f28,f27])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f45,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f32])).

% (17923)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f32,plain,
    ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
    & k1_xboole_0 != sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f31])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k7_setfam_1(X0,X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k1_xboole_0 = k7_setfam_1(sK3,sK4)
      & k1_xboole_0 != sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

% (17907)Refutation not found, incomplete strategy% (17907)------------------------------
% (17907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17911)Refutation not found, incomplete strategy% (17911)------------------------------
% (17911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17911)Termination reason: Refutation not found, incomplete strategy

% (17911)Memory used [KB]: 6268
% (17911)Time elapsed: 0.137 s
% (17911)------------------------------
% (17911)------------------------------
% (17907)Termination reason: Refutation not found, incomplete strategy

% (17907)Memory used [KB]: 10618
% (17907)Time elapsed: 0.138 s
% (17907)------------------------------
% (17907)------------------------------
fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f123,plain,(
    sP1(sK4,sK3,k1_xboole_0) ),
    inference(resolution,[],[f120,f96])).

fof(f96,plain,
    ( ~ sP2(k1_xboole_0,sK3,sK4)
    | sP1(sK4,sK3,k1_xboole_0) ),
    inference(superposition,[],[f86,f93])).

fof(f93,plain,(
    sK4 = k7_setfam_1(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,
    ( sK4 = k7_setfam_1(sK3,k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(superposition,[],[f55,f46])).

fof(f46,plain,(
    k1_xboole_0 = k7_setfam_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1,k7_setfam_1(X1,X0))
      | sP1(k7_setfam_1(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k7_setfam_1(X1,X0) != X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    sP2(k1_xboole_0,sK3,sK4) ),
    inference(resolution,[],[f118,f83])).

fof(f118,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3)))
      | sP2(X2,sK3,sK4) ) ),
    inference(resolution,[],[f65,f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:36:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (17908)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.51  % (17925)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.51  % (17905)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.24/0.51  % (17909)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.51  % (17910)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.52  % (17901)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.52  % (17921)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.52  % (17897)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.52  % (17902)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.52  % (17925)Refutation found. Thanks to Tanya!
% 1.24/0.52  % SZS status Theorem for theBenchmark
% 1.24/0.52  % (17916)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.52  % (17918)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.52  % (17913)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.52  % (17919)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.53  % (17922)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.53  % (17918)Refutation not found, incomplete strategy% (17918)------------------------------
% 1.37/0.53  % (17918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (17918)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (17918)Memory used [KB]: 10746
% 1.37/0.53  % (17918)Time elapsed: 0.088 s
% 1.37/0.53  % (17918)------------------------------
% 1.37/0.53  % (17918)------------------------------
% 1.37/0.53  % (17900)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % (17900)Refutation not found, incomplete strategy% (17900)------------------------------
% 1.37/0.53  % (17900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (17900)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (17900)Memory used [KB]: 6140
% 1.37/0.53  % (17900)Time elapsed: 0.129 s
% 1.37/0.53  % (17900)------------------------------
% 1.37/0.53  % (17900)------------------------------
% 1.37/0.53  % (17898)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.53  % SZS output start Proof for theBenchmark
% 1.37/0.53  fof(f171,plain,(
% 1.37/0.53    $false),
% 1.37/0.53    inference(unit_resulting_resolution,[],[f120,f123,f45,f130,f161,f101])).
% 1.37/0.53  fof(f101,plain,(
% 1.37/0.53    ( ! [X6,X8,X7,X5] : (~sP2(X6,X5,X8) | ~sP1(X8,X5,X6) | X7 = X8 | ~sP1(X7,X5,X6) | ~sP2(X6,X5,X7)) )),
% 1.37/0.53    inference(superposition,[],[f57,f57])).
% 1.37/0.53  fof(f57,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f36])).
% 1.37/0.53  fof(f36,plain,(
% 1.37/0.53    ! [X0,X1,X2] : (((k7_setfam_1(X1,X0) = X2 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2)) | ~sP2(X0,X1,X2))),
% 1.37/0.53    inference(rectify,[],[f35])).
% 1.37/0.53  fof(f35,plain,(
% 1.37/0.53    ! [X1,X0,X2] : (((k7_setfam_1(X0,X1) = X2 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k7_setfam_1(X0,X1) != X2)) | ~sP2(X1,X0,X2))),
% 1.37/0.53    inference(nnf_transformation,[],[f29])).
% 1.37/0.53  fof(f29,plain,(
% 1.37/0.53    ! [X1,X0,X2] : ((k7_setfam_1(X0,X1) = X2 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0,X2))),
% 1.37/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.37/0.53  fof(f161,plain,(
% 1.37/0.53    ( ! [X0] : (sP1(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.37/0.53    inference(resolution,[],[f152,f126])).
% 1.37/0.53  fof(f126,plain,(
% 1.37/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.37/0.53    inference(trivial_inequality_removal,[],[f124])).
% 1.37/0.53  fof(f124,plain,(
% 1.37/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.37/0.53    inference(superposition,[],[f85,f82])).
% 1.37/0.53  fof(f82,plain,(
% 1.37/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) )),
% 1.37/0.53    inference(definition_unfolding,[],[f48,f80])).
% 1.37/0.53  fof(f80,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.37/0.53    inference(definition_unfolding,[],[f54,f79])).
% 1.37/0.53  fof(f79,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.37/0.53    inference(definition_unfolding,[],[f52,f78])).
% 1.37/0.53  fof(f78,plain,(
% 1.37/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f53,f77])).
% 1.37/0.53  fof(f77,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f68,f76])).
% 1.37/0.53  fof(f76,plain,(
% 1.37/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f70,f75])).
% 1.37/0.53  fof(f75,plain,(
% 1.37/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f71,f74])).
% 1.37/0.53  fof(f74,plain,(
% 1.37/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.37/0.53    inference(definition_unfolding,[],[f72,f73])).
% 1.37/0.53  fof(f73,plain,(
% 1.37/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f10,axiom,(
% 1.37/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.37/0.53  fof(f72,plain,(
% 1.37/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f9])).
% 1.37/0.53  fof(f9,axiom,(
% 1.37/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.37/0.53  fof(f71,plain,(
% 1.37/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f8])).
% 1.37/0.53  fof(f8,axiom,(
% 1.37/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.37/0.53  fof(f70,plain,(
% 1.37/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f7])).
% 1.37/0.53  fof(f7,axiom,(
% 1.37/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.37/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.37/0.53  % (17899)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.53  % (17896)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.53  % (17912)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.54  % (17914)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.54  % (17917)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.54  % (17907)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.54  fof(f68,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f6])).
% 1.37/0.54  fof(f6,axiom,(
% 1.37/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.37/0.54  fof(f53,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f5])).
% 1.37/0.54  fof(f5,axiom,(
% 1.37/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.37/0.54  fof(f52,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f16])).
% 1.37/0.54  fof(f16,axiom,(
% 1.37/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.37/0.54  fof(f54,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f2])).
% 1.37/0.54  fof(f2,axiom,(
% 1.37/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.37/0.54  fof(f48,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f3])).
% 1.37/0.54  fof(f3,axiom,(
% 1.37/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.37/0.54  fof(f85,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != X0 | ~r2_hidden(X1,X0)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f66,f80,f81])).
% 1.37/0.54  fof(f81,plain,(
% 1.37/0.54    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.37/0.54    inference(definition_unfolding,[],[f50,f78])).
% 1.37/0.54  fof(f50,plain,(
% 1.37/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f4])).
% 1.37/0.54  fof(f4,axiom,(
% 1.37/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.37/0.54  fof(f66,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.37/0.54    inference(cnf_transformation,[],[f43])).
% 1.37/0.54  % (17911)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.54  fof(f43,plain,(
% 1.37/0.54    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.37/0.54    inference(nnf_transformation,[],[f11])).
% 1.37/0.54  fof(f11,axiom,(
% 1.37/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.37/0.54  % (17915)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.54  fof(f152,plain,(
% 1.37/0.54    ( ! [X8,X9] : (r2_hidden(sK6(X8,X9,k1_xboole_0),X8) | sP1(X8,X9,k1_xboole_0)) )),
% 1.37/0.54    inference(resolution,[],[f112,f126])).
% 1.37/0.54  fof(f112,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,sK6(X1,X0,X2)),X2) | r2_hidden(sK6(X1,X0,X2),X1) | sP1(X1,X0,X2)) )),
% 1.37/0.54    inference(resolution,[],[f63,f60])).
% 1.37/0.54  fof(f60,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~sP0(X2,sK6(X0,X1,X2),X1,X0) | sP1(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f40])).
% 1.37/0.54  fof(f40,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~sP0(X2,sK6(X0,X1,X2),X1,X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 1.37/0.54  fof(f39,plain,(
% 1.37/0.54    ! [X2,X1,X0] : (? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1))) => (~sP0(X2,sK6(X0,X1,X2),X1,X0) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(X1))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f38,plain,(
% 1.37/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~sP0(X2,X3,X1,X0) & m1_subset_1(X3,k1_zfmisc_1(X1)))) & (! [X4] : (sP0(X2,X4,X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(X1))) | ~sP1(X0,X1,X2)))),
% 1.37/0.54    inference(rectify,[],[f37])).
% 1.37/0.54  fof(f37,plain,(
% 1.37/0.54    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ? [X3] : (~sP0(X1,X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(X0)))) & (! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) | ~sP1(X2,X0,X1)))),
% 1.37/0.54    inference(nnf_transformation,[],[f28])).
% 1.37/0.54  fof(f28,plain,(
% 1.37/0.54    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> ! [X3] : (sP0(X1,X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(X0))))),
% 1.37/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.37/0.54  fof(f63,plain,(
% 1.37/0.54    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f42])).
% 1.37/0.54  fof(f42,plain,(
% 1.37/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((~r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3)) & (r2_hidden(k3_subset_1(X2,X1),X0) | r2_hidden(X1,X3)))) & (((r2_hidden(X1,X3) | ~r2_hidden(k3_subset_1(X2,X1),X0)) & (r2_hidden(k3_subset_1(X2,X1),X0) | ~r2_hidden(X1,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.37/0.54    inference(rectify,[],[f41])).
% 1.37/0.54  fof(f41,plain,(
% 1.37/0.54    ! [X1,X3,X0,X2] : ((sP0(X1,X3,X0,X2) | ((~r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2)) & (r2_hidden(k3_subset_1(X0,X3),X1) | r2_hidden(X3,X2)))) & (((r2_hidden(X3,X2) | ~r2_hidden(k3_subset_1(X0,X3),X1)) & (r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2))) | ~sP0(X1,X3,X0,X2)))),
% 1.37/0.54    inference(nnf_transformation,[],[f27])).
% 1.37/0.54  fof(f27,plain,(
% 1.37/0.54    ! [X1,X3,X0,X2] : (sP0(X1,X3,X0,X2) <=> (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)))),
% 1.37/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.37/0.54  fof(f130,plain,(
% 1.37/0.54    ( ! [X0] : (sP2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.37/0.54    inference(resolution,[],[f117,f83])).
% 1.37/0.54  fof(f83,plain,(
% 1.37/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(definition_unfolding,[],[f49,f47])).
% 1.37/0.54  fof(f47,plain,(
% 1.37/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f12])).
% 1.37/0.54  fof(f12,axiom,(
% 1.37/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.37/0.54  fof(f49,plain,(
% 1.37/0.54    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f13])).
% 1.37/0.54  fof(f13,axiom,(
% 1.37/0.54    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.37/0.54  fof(f117,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) | sP2(X0,X1,k1_xboole_0)) )),
% 1.37/0.54    inference(resolution,[],[f65,f83])).
% 1.37/0.54  % (17913)Refutation not found, incomplete strategy% (17913)------------------------------
% 1.37/0.54  % (17913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (17913)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (17913)Memory used [KB]: 10618
% 1.37/0.54  % (17913)Time elapsed: 0.142 s
% 1.37/0.54  % (17913)------------------------------
% 1.37/0.54  % (17913)------------------------------
% 1.37/0.54  fof(f65,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | sP2(X1,X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f30])).
% 1.37/0.54  fof(f30,plain,(
% 1.37/0.54    ! [X0,X1] : (! [X2] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(definition_folding,[],[f24,f29,f28,f27])).
% 1.37/0.54  fof(f24,plain,(
% 1.37/0.54    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f14])).
% 1.37/0.54  fof(f14,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 1.37/0.54  fof(f45,plain,(
% 1.37/0.54    k1_xboole_0 != sK4),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  % (17923)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.54  fof(f32,plain,(
% 1.37/0.54    k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 1.37/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f31])).
% 1.37/0.54  fof(f31,plain,(
% 1.37/0.54    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k1_xboole_0 = k7_setfam_1(sK3,sK4) & k1_xboole_0 != sK4 & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 1.37/0.54    introduced(choice_axiom,[])).
% 1.37/0.54  fof(f21,plain,(
% 1.37/0.54    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(flattening,[],[f20])).
% 1.37/0.54  fof(f20,plain,(
% 1.37/0.54    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f19])).
% 1.37/0.54  % (17907)Refutation not found, incomplete strategy% (17907)------------------------------
% 1.37/0.54  % (17907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (17911)Refutation not found, incomplete strategy% (17911)------------------------------
% 1.37/0.54  % (17911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (17911)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (17911)Memory used [KB]: 6268
% 1.37/0.54  % (17911)Time elapsed: 0.137 s
% 1.37/0.54  % (17911)------------------------------
% 1.37/0.54  % (17911)------------------------------
% 1.37/0.54  % (17907)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (17907)Memory used [KB]: 10618
% 1.37/0.54  % (17907)Time elapsed: 0.138 s
% 1.37/0.54  % (17907)------------------------------
% 1.37/0.54  % (17907)------------------------------
% 1.37/0.54  fof(f19,negated_conjecture,(
% 1.37/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.37/0.54    inference(negated_conjecture,[],[f18])).
% 1.37/0.54  fof(f18,conjecture,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 1.37/0.54  fof(f123,plain,(
% 1.37/0.54    sP1(sK4,sK3,k1_xboole_0)),
% 1.37/0.54    inference(resolution,[],[f120,f96])).
% 1.37/0.54  fof(f96,plain,(
% 1.37/0.54    ~sP2(k1_xboole_0,sK3,sK4) | sP1(sK4,sK3,k1_xboole_0)),
% 1.37/0.54    inference(superposition,[],[f86,f93])).
% 1.37/0.54  fof(f93,plain,(
% 1.37/0.54    sK4 = k7_setfam_1(sK3,k1_xboole_0)),
% 1.37/0.54    inference(subsumption_resolution,[],[f92,f44])).
% 1.37/0.54  fof(f44,plain,(
% 1.37/0.54    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f92,plain,(
% 1.37/0.54    sK4 = k7_setfam_1(sK3,k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 1.37/0.54    inference(superposition,[],[f55,f46])).
% 1.37/0.54  fof(f46,plain,(
% 1.37/0.54    k1_xboole_0 = k7_setfam_1(sK3,sK4)),
% 1.37/0.54    inference(cnf_transformation,[],[f32])).
% 1.37/0.54  fof(f55,plain,(
% 1.37/0.54    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.37/0.54    inference(cnf_transformation,[],[f23])).
% 1.37/0.54  fof(f23,plain,(
% 1.37/0.54    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.37/0.54    inference(ennf_transformation,[],[f15])).
% 1.37/0.54  fof(f15,axiom,(
% 1.37/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.37/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.37/0.54  fof(f86,plain,(
% 1.37/0.54    ( ! [X0,X1] : (~sP2(X0,X1,k7_setfam_1(X1,X0)) | sP1(k7_setfam_1(X1,X0),X1,X0)) )),
% 1.37/0.54    inference(equality_resolution,[],[f56])).
% 1.37/0.54  fof(f56,plain,(
% 1.37/0.54    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k7_setfam_1(X1,X0) != X2 | ~sP2(X0,X1,X2)) )),
% 1.37/0.54    inference(cnf_transformation,[],[f36])).
% 1.37/0.54  fof(f120,plain,(
% 1.37/0.54    sP2(k1_xboole_0,sK3,sK4)),
% 1.37/0.54    inference(resolution,[],[f118,f83])).
% 1.37/0.54  fof(f118,plain,(
% 1.37/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3))) | sP2(X2,sK3,sK4)) )),
% 1.37/0.54    inference(resolution,[],[f65,f44])).
% 1.37/0.54  % SZS output end Proof for theBenchmark
% 1.37/0.54  % (17925)------------------------------
% 1.37/0.54  % (17925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (17925)Termination reason: Refutation
% 1.37/0.54  
% 1.37/0.54  % (17925)Memory used [KB]: 1791
% 1.37/0.54  % (17925)Time elapsed: 0.123 s
% 1.37/0.54  % (17925)------------------------------
% 1.37/0.54  % (17925)------------------------------
% 1.37/0.54  % (17924)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.54  % (17895)Success in time 0.188 s
%------------------------------------------------------------------------------
