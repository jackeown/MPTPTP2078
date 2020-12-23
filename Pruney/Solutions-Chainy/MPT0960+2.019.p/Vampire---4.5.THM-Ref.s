%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 150 expanded)
%              Number of leaves         :   18 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  208 ( 395 expanded)
%              Number of equality atoms :   30 (  76 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f221,f304])).

fof(f304,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f301,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (15984)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (15965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (15968)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (15968)Refutation not found, incomplete strategy% (15968)------------------------------
% (15968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15968)Termination reason: Refutation not found, incomplete strategy

% (15968)Memory used [KB]: 10490
% (15968)Time elapsed: 0.106 s
% (15968)------------------------------
% (15968)------------------------------
% (15982)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (15981)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (15971)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (15963)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f301,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl7_4 ),
    inference(resolution,[],[f299,f83])).

fof(f83,plain,(
    ! [X0] : sP2(X0,k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f82,plain,(
    ! [X0] :
      ( sP2(X0,k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f68,f59])).

% (15969)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f17,f25,f24,f23,f22])).

fof(f22,plain,(
    ! [X3,X2,X1] :
      ( sP0(X3,X2,X1)
    <=> ( r2_hidden(k4_tarski(X2,X3),X1)
      <=> r1_tarski(X2,X3) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ! [X2,X3] :
          ( sP0(X3,X2,X1)
          | ~ r2_hidden(X3,X0)
          | ~ r2_hidden(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( sP1(X1,X0)
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ( k1_wellord2(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f68,plain,(
    ! [X1] :
      ( ~ sP3(k1_wellord2(X1),X1)
      | sP2(X1,k1_wellord2(X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k1_wellord2(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k1_wellord2(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_wellord2(sK4))
        | ~ r1_tarski(X0,sK4) )
    | spl7_4 ),
    inference(superposition,[],[f296,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(X1,X0)
        | k3_relat_1(X1) != X0 )
      & ( ( sP1(X1,X0)
          & k3_relat_1(X1) = X0 )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f296,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f295,f42])).

fof(f295,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4))
    | spl7_4 ),
    inference(superposition,[],[f284,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f284,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)
    | spl7_4 ),
    inference(resolution,[],[f241,f70])).

fof(f241,plain,
    ( ! [X6,X5] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X6)
        | ~ r1_tarski(k2_xboole_0(X5,X6),sK4) )
    | spl7_4 ),
    inference(resolution,[],[f233,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl7_4 ),
    inference(resolution,[],[f186,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f67,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f186,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_4
  <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f221,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f218,f70])).

fof(f218,plain,
    ( ~ r1_tarski(sK4,sK4)
    | spl7_3 ),
    inference(resolution,[],[f212,f83])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ sP2(X0,k1_wellord2(sK4))
        | ~ r1_tarski(X0,sK4) )
    | spl7_3 ),
    inference(superposition,[],[f199,f48])).

fof(f199,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f190,f42])).

fof(f190,plain,
    ( ~ r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4))
    | spl7_3 ),
    inference(resolution,[],[f188,f104])).

fof(f104,plain,(
    ! [X9] :
      ( r1_tarski(k1_relat_1(X9),k3_relat_1(X9))
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl7_3 ),
    inference(resolution,[],[f182,f78])).

fof(f182,plain,
    ( ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl7_3
  <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f187,plain,
    ( ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f178,f184,f180])).

fof(f178,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) ),
    inference(subsumption_resolution,[],[f175,f42])).

fof(f175,plain,
    ( ~ r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)
    | ~ r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)
    | ~ v1_relat_1(k1_wellord2(sK4)) ),
    inference(resolution,[],[f167,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f167,plain,(
    ! [X17,X16] :
      ( ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16))
      | ~ r1_tarski(X16,sK4)
      | ~ r1_tarski(X17,sK4) ) ),
    inference(resolution,[],[f66,f145])).

fof(f145,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X1,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X2)
      | ~ r1_tarski(X1,sK4) ) ),
    inference(resolution,[],[f65,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f109,f78])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(sK4,sK4))
      | ~ r1_tarski(k1_wellord2(sK4),X0) ) ),
    inference(resolution,[],[f78,f41])).

fof(f41,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f27])).

fof(f27,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:17:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (15975)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (15975)Refutation not found, incomplete strategy% (15975)------------------------------
% 0.21/0.49  % (15975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (15964)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (15967)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (15975)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15975)Memory used [KB]: 6012
% 0.21/0.50  % (15975)Time elapsed: 0.080 s
% 0.21/0.50  % (15975)------------------------------
% 0.21/0.50  % (15975)------------------------------
% 0.21/0.50  % (15967)Refutation not found, incomplete strategy% (15967)------------------------------
% 0.21/0.50  % (15967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15967)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (15967)Memory used [KB]: 6012
% 0.21/0.50  % (15967)Time elapsed: 0.087 s
% 0.21/0.50  % (15967)------------------------------
% 0.21/0.50  % (15967)------------------------------
% 0.21/0.50  % (15974)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (15978)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (15972)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (15985)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (15966)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (15977)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (15980)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (15970)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (15962)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (15962)Refutation not found, incomplete strategy% (15962)------------------------------
% 0.21/0.51  % (15962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15962)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15962)Memory used [KB]: 10490
% 0.21/0.51  % (15962)Time elapsed: 0.095 s
% 0.21/0.51  % (15962)------------------------------
% 0.21/0.51  % (15962)------------------------------
% 0.21/0.51  % (15966)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f187,f221,f304])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    spl7_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    $false | spl7_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f301,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  % (15984)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (15965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (15968)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (15968)Refutation not found, incomplete strategy% (15968)------------------------------
% 0.21/0.52  % (15968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15968)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15968)Memory used [KB]: 10490
% 0.21/0.52  % (15968)Time elapsed: 0.106 s
% 0.21/0.52  % (15968)------------------------------
% 0.21/0.52  % (15968)------------------------------
% 0.21/0.52  % (15982)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (15981)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (15971)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (15963)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f301,plain,(
% 0.21/0.53    ~r1_tarski(sK4,sK4) | spl7_4),
% 0.21/0.53    inference(resolution,[],[f299,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0] : (sP2(X0,k1_wellord2(X0))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f82,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (sP2(X0,k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.53    inference(resolution,[],[f68,f59])).
% 0.21/0.53  % (15969)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1] : (sP3(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(definition_folding,[],[f17,f25,f24,f23,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X3,X2,X1] : (sP0(X3,X2,X1) <=> (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X1,X0] : (sP1(X1,X0) <=> ! [X2,X3] : (sP0(X3,X2,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : (sP2(X0,X1) <=> (sP1(X1,X0) & k3_relat_1(X1) = X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X1,X0] : ((k1_wellord2(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X1] : (~sP3(k1_wellord2(X1),X1) | sP2(X1,k1_wellord2(X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP2(X1,X0) | k1_wellord2(X1) != X0 | ~sP3(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (((k1_wellord2(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k1_wellord2(X1) != X0)) | ~sP3(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X0] : (((k1_wellord2(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k1_wellord2(X0) != X1)) | ~sP3(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f299,plain,(
% 0.21/0.53    ( ! [X0] : (~sP2(X0,k1_wellord2(sK4)) | ~r1_tarski(X0,sK4)) ) | spl7_4),
% 0.21/0.53    inference(superposition,[],[f296,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | ~sP2(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP2(X0,X1) | ~sP1(X1,X0) | k3_relat_1(X1) != X0) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(X1,X0) | k3_relat_1(X1) != X0)) & ((sP1(X1,X0) & k3_relat_1(X1) = X0) | ~sP2(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | spl7_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f295,f42])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4)) | spl7_4),
% 0.21/0.53    inference(superposition,[],[f284,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k2_relat_1(k1_wellord2(sK4))),sK4)) ) | spl7_4),
% 0.21/0.53    inference(resolution,[],[f241,f70])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X6) | ~r1_tarski(k2_xboole_0(X5,X6),sK4)) ) | spl7_4),
% 0.21/0.53    inference(resolution,[],[f233,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k2_relat_1(k1_wellord2(sK4)),X0) | ~r1_tarski(X0,sK4)) ) | spl7_4),
% 0.21/0.53    inference(resolution,[],[f186,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f67,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    spl7_4 <=> r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    spl7_3),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    $false | spl7_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f218,f70])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~r1_tarski(sK4,sK4) | spl7_3),
% 0.21/0.53    inference(resolution,[],[f212,f83])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0] : (~sP2(X0,k1_wellord2(sK4)) | ~r1_tarski(X0,sK4)) ) | spl7_3),
% 0.21/0.53    inference(superposition,[],[f199,f48])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | spl7_3),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f42])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~r1_tarski(k3_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4)) | spl7_3),
% 0.21/0.53    inference(resolution,[],[f188,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X9] : (r1_tarski(k1_relat_1(X9),k3_relat_1(X9)) | ~v1_relat_1(X9)) )),
% 0.21/0.53    inference(superposition,[],[f45,f44])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(k1_wellord2(sK4)),X0) | ~r1_tarski(X0,sK4)) ) | spl7_3),
% 0.21/0.53    inference(resolution,[],[f182,f78])).
% 0.21/0.53  fof(f182,plain,(
% 0.21/0.53    ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | spl7_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl7_3 <=> r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~spl7_3 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f178,f184,f180])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f175,f42])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ~r1_tarski(k2_relat_1(k1_wellord2(sK4)),sK4) | ~r1_tarski(k1_relat_1(k1_wellord2(sK4)),sK4) | ~v1_relat_1(k1_wellord2(sK4))),
% 0.21/0.53    inference(resolution,[],[f167,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    ( ! [X17,X16] : (~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(X17,X16)) | ~r1_tarski(X16,sK4) | ~r1_tarski(X17,sK4)) )),
% 0.21/0.53    inference(resolution,[],[f66,f145])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X2,X1] : (~r1_tarski(X2,k2_zfmisc_1(X1,sK4)) | ~r1_tarski(k1_wellord2(sK4),X2) | ~r1_tarski(X1,sK4)) )),
% 0.21/0.53    inference(resolution,[],[f65,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f109,f78])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k2_zfmisc_1(sK4,sK4)) | ~r1_tarski(k1_wellord2(sK4),X0)) )),
% 0.21/0.53    inference(resolution,[],[f78,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK4),k2_zfmisc_1(sK4,sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (15966)------------------------------
% 0.21/0.53  % (15966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15966)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (15966)Memory used [KB]: 6268
% 0.21/0.53  % (15966)Time elapsed: 0.102 s
% 0.21/0.53  % (15966)------------------------------
% 0.21/0.53  % (15966)------------------------------
% 0.21/0.53  % (15963)Refutation not found, incomplete strategy% (15963)------------------------------
% 0.21/0.53  % (15963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15963)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15963)Memory used [KB]: 10618
% 0.21/0.53  % (15963)Time elapsed: 0.117 s
% 0.21/0.53  % (15963)------------------------------
% 0.21/0.53  % (15963)------------------------------
% 0.21/0.53  % (15961)Success in time 0.168 s
%------------------------------------------------------------------------------
