%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 155 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 ( 545 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (13241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (13250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (13255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (13249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (13230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (13242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (13251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (13257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (13251)Refutation not found, incomplete strategy% (13251)------------------------------
% (13251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13251)Termination reason: Refutation not found, incomplete strategy

% (13251)Memory used [KB]: 10746
% (13251)Time elapsed: 0.128 s
% (13251)------------------------------
% (13251)------------------------------
% (13236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f83,f96,f117,f119,f124,f144,f181,f187,f244])).

fof(f244,plain,
    ( ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f143,f235])).

fof(f235,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f193,f81])).

fof(f81,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f125,f143])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f81,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( r2_hidden(X3,X0)
        & r2_hidden(X2,X3)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_ordinal1)).

fof(f143,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_10
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f187,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_8
    | spl3_2 ),
    inference(avatar_split_clause,[],[f185,f78,f132,f91,f88])).

fof(f88,plain,
    ( spl3_3
  <=> v3_ordinal1(k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f91,plain,
    ( spl3_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( spl3_8
  <=> r2_hidden(sK1,k1_ordinal1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f78,plain,
    ( spl3_2
  <=> r1_ordinal1(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f185,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | spl3_2 ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f79,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f181,plain,
    ( ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f147,f172])).

fof(f172,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f166,f147])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f151,f147])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK0,X1)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f147,f69])).

fof(f147,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f81,f140])).

fof(f140,plain,
    ( sK0 = sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_9
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f135,f132,f142,f139])).

fof(f135,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f133,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_ordinal1(X1))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f133,plain,
    ( r2_hidden(sK1,k1_ordinal1(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f124,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_1
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f95,f111])).

fof(f111,plain,
    ( ~ r1_tarski(k1_ordinal1(sK0),sK1)
    | spl3_1 ),
    inference(resolution,[],[f85,f73])).

fof(f73,plain,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_1 ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f76,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f95,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_5
  <=> r1_tarski(k1_ordinal1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f44,f92])).

fof(f92,plain,
    ( ~ v3_ordinal1(sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f44,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f117,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f43,f97])).

fof(f97,plain,
    ( ~ v3_ordinal1(sK0)
    | spl3_3 ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f89,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f43,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f86,f78,f94,f91,f88])).

fof(f86,plain,
    ( r1_tarski(k1_ordinal1(sK0),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f82,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f83,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f45,f78,f75])).

fof(f45,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f78,f75])).

fof(f46,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:29:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (13247)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (13239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (13232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13234)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (13256)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (13240)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (13254)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (13258)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (13229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (13248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (13231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (13243)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (13238)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (13233)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (13231)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.57  % (13235)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.57  % (13241)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (13250)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (13255)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (13249)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (13230)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (13242)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (13251)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.58  % (13257)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.58  % (13251)Refutation not found, incomplete strategy% (13251)------------------------------
% 0.21/0.58  % (13251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (13251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (13251)Memory used [KB]: 10746
% 0.21/0.58  % (13251)Time elapsed: 0.128 s
% 0.21/0.58  % (13251)------------------------------
% 0.21/0.58  % (13251)------------------------------
% 0.21/0.58  % (13236)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.59  fof(f245,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(avatar_sat_refutation,[],[f80,f83,f96,f117,f119,f124,f144,f181,f187,f244])).
% 0.21/0.59  fof(f244,plain,(
% 0.21/0.59    ~spl3_1 | ~spl3_10),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f241])).
% 0.21/0.59  fof(f241,plain,(
% 0.21/0.59    $false | (~spl3_1 | ~spl3_10)),
% 0.21/0.59    inference(subsumption_resolution,[],[f143,f235])).
% 0.21/0.59  fof(f235,plain,(
% 0.21/0.59    ~r2_hidden(sK1,sK0) | (~spl3_1 | ~spl3_10)),
% 0.21/0.59    inference(resolution,[],[f193,f81])).
% 0.21/0.59  fof(f81,plain,(
% 0.21/0.59    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f75])).
% 0.21/0.59  fof(f75,plain,(
% 0.21/0.59    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.59  fof(f193,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(X0,sK0)) ) | (~spl3_1 | ~spl3_10)),
% 0.21/0.59    inference(resolution,[],[f125,f143])).
% 0.21/0.59  fof(f125,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(sK1,X1) | ~r2_hidden(X1,X0) | ~r2_hidden(X0,sK0)) ) | ~spl3_1),
% 0.21/0.59    inference(resolution,[],[f81,f69])).
% 0.21/0.59  fof(f69,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f27])).
% 0.21/0.59  fof(f27,plain,(
% 0.21/0.59    ! [X0,X1,X2,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f14])).
% 0.21/0.59  fof(f14,axiom,(
% 0.21/0.59    ! [X0,X1,X2,X3] : ~(r2_hidden(X3,X0) & r2_hidden(X2,X3) & r2_hidden(X1,X2) & r2_hidden(X0,X1))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_ordinal1)).
% 0.21/0.59  fof(f143,plain,(
% 0.21/0.59    r2_hidden(sK1,sK0) | ~spl3_10),
% 0.21/0.59    inference(avatar_component_clause,[],[f142])).
% 0.21/0.59  fof(f142,plain,(
% 0.21/0.59    spl3_10 <=> r2_hidden(sK1,sK0)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.59  fof(f187,plain,(
% 0.21/0.59    ~spl3_3 | ~spl3_4 | spl3_8 | spl3_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f185,f78,f132,f91,f88])).
% 0.21/0.59  fof(f88,plain,(
% 0.21/0.59    spl3_3 <=> v3_ordinal1(k1_ordinal1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.59  fof(f91,plain,(
% 0.21/0.59    spl3_4 <=> v3_ordinal1(sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.59  fof(f132,plain,(
% 0.21/0.59    spl3_8 <=> r2_hidden(sK1,k1_ordinal1(sK0))),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.59  fof(f78,plain,(
% 0.21/0.59    spl3_2 <=> r1_ordinal1(k1_ordinal1(sK0),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.59  fof(f185,plain,(
% 0.21/0.59    r2_hidden(sK1,k1_ordinal1(sK0)) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | spl3_2),
% 0.21/0.59    inference(resolution,[],[f79,f50])).
% 0.21/0.59  fof(f50,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.59    inference(flattening,[],[f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f12])).
% 0.21/0.59  fof(f12,axiom,(
% 0.21/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.59  fof(f79,plain,(
% 0.21/0.59    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | spl3_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f78])).
% 0.21/0.59  fof(f181,plain,(
% 0.21/0.59    ~spl3_1 | ~spl3_9),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.59  fof(f178,plain,(
% 0.21/0.59    $false | (~spl3_1 | ~spl3_9)),
% 0.21/0.59    inference(subsumption_resolution,[],[f147,f172])).
% 0.21/0.59  fof(f172,plain,(
% 0.21/0.59    ~r2_hidden(sK0,sK0) | (~spl3_1 | ~spl3_9)),
% 0.21/0.59    inference(resolution,[],[f166,f147])).
% 0.21/0.59  fof(f166,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r2_hidden(X0,sK0)) ) | (~spl3_1 | ~spl3_9)),
% 0.21/0.59    inference(resolution,[],[f151,f147])).
% 0.21/0.59  fof(f151,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(sK0,X1) | ~r2_hidden(X1,X0) | ~r2_hidden(X0,sK0)) ) | (~spl3_1 | ~spl3_9)),
% 0.21/0.59    inference(resolution,[],[f147,f69])).
% 0.21/0.59  fof(f147,plain,(
% 0.21/0.59    r2_hidden(sK0,sK0) | (~spl3_1 | ~spl3_9)),
% 0.21/0.59    inference(backward_demodulation,[],[f81,f140])).
% 0.21/0.59  fof(f140,plain,(
% 0.21/0.59    sK0 = sK1 | ~spl3_9),
% 0.21/0.59    inference(avatar_component_clause,[],[f139])).
% 0.21/0.59  fof(f139,plain,(
% 0.21/0.59    spl3_9 <=> sK0 = sK1),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.59  fof(f144,plain,(
% 0.21/0.59    spl3_9 | spl3_10 | ~spl3_8),
% 0.21/0.59    inference(avatar_split_clause,[],[f135,f132,f142,f139])).
% 0.21/0.59  fof(f135,plain,(
% 0.21/0.59    r2_hidden(sK1,sK0) | sK0 = sK1 | ~spl3_8),
% 0.21/0.59    inference(resolution,[],[f133,f62])).
% 0.21/0.59  fof(f62,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X0,k1_ordinal1(X1)) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f41])).
% 0.21/0.59  fof(f41,plain,(
% 0.21/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.59    inference(flattening,[],[f40])).
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.59    inference(nnf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,axiom,(
% 0.21/0.59    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.59  fof(f133,plain,(
% 0.21/0.59    r2_hidden(sK1,k1_ordinal1(sK0)) | ~spl3_8),
% 0.21/0.59    inference(avatar_component_clause,[],[f132])).
% 0.21/0.59  fof(f124,plain,(
% 0.21/0.59    spl3_1 | ~spl3_5),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.59  fof(f123,plain,(
% 0.21/0.59    $false | (spl3_1 | ~spl3_5)),
% 0.21/0.59    inference(subsumption_resolution,[],[f95,f111])).
% 0.21/0.59  fof(f111,plain,(
% 0.21/0.59    ~r1_tarski(k1_ordinal1(sK0),sK1) | spl3_1),
% 0.21/0.59    inference(resolution,[],[f85,f73])).
% 0.21/0.59  fof(f73,plain,(
% 0.21/0.59    ( ! [X1] : (r2_hidden(X1,k1_ordinal1(X1))) )),
% 0.21/0.59    inference(equality_resolution,[],[f64])).
% 0.21/0.59  fof(f64,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.59    inference(cnf_transformation,[],[f41])).
% 0.21/0.59  fof(f85,plain,(
% 0.21/0.59    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,sK1)) ) | spl3_1),
% 0.21/0.59    inference(resolution,[],[f76,f59])).
% 0.21/0.59  fof(f59,plain,(
% 0.21/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f39])).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f37,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(rectify,[],[f36])).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.59    inference(nnf_transformation,[],[f24])).
% 0.21/0.59  fof(f24,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f76,plain,(
% 0.21/0.59    ~r2_hidden(sK0,sK1) | spl3_1),
% 0.21/0.59    inference(avatar_component_clause,[],[f75])).
% 0.21/0.59  fof(f95,plain,(
% 0.21/0.59    r1_tarski(k1_ordinal1(sK0),sK1) | ~spl3_5),
% 0.21/0.59    inference(avatar_component_clause,[],[f94])).
% 0.21/0.59  fof(f94,plain,(
% 0.21/0.59    spl3_5 <=> r1_tarski(k1_ordinal1(sK0),sK1)),
% 0.21/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.59  fof(f119,plain,(
% 0.21/0.59    spl3_4),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.59  fof(f118,plain,(
% 0.21/0.59    $false | spl3_4),
% 0.21/0.59    inference(subsumption_resolution,[],[f44,f92])).
% 0.21/0.59  fof(f92,plain,(
% 0.21/0.59    ~v3_ordinal1(sK1) | spl3_4),
% 0.21/0.59    inference(avatar_component_clause,[],[f91])).
% 0.21/0.59  fof(f44,plain,(
% 0.21/0.59    v3_ordinal1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f32,plain,(
% 0.21/0.59    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f31,plain,(
% 0.21/0.59    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.59    introduced(choice_axiom,[])).
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.59    inference(flattening,[],[f28])).
% 0.21/0.59  fof(f28,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f18])).
% 0.21/0.59  fof(f18,plain,(
% 0.21/0.59    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f17])).
% 0.21/0.59  fof(f17,negated_conjecture,(
% 0.21/0.59    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.59    inference(negated_conjecture,[],[f16])).
% 0.21/0.59  fof(f16,conjecture,(
% 0.21/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.59  fof(f117,plain,(
% 0.21/0.59    spl3_3),
% 0.21/0.59    inference(avatar_contradiction_clause,[],[f116])).
% 0.21/0.59  fof(f116,plain,(
% 0.21/0.59    $false | spl3_3),
% 0.21/0.59    inference(subsumption_resolution,[],[f43,f97])).
% 0.21/0.59  fof(f97,plain,(
% 0.21/0.59    ~v3_ordinal1(sK0) | spl3_3),
% 0.21/0.59    inference(resolution,[],[f89,f49])).
% 0.21/0.59  fof(f49,plain,(
% 0.21/0.59    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f19])).
% 0.21/0.59  fof(f19,plain,(
% 0.21/0.59    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f13])).
% 0.21/0.59  fof(f13,axiom,(
% 0.21/0.59    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.59  fof(f89,plain,(
% 0.21/0.59    ~v3_ordinal1(k1_ordinal1(sK0)) | spl3_3),
% 0.21/0.59    inference(avatar_component_clause,[],[f88])).
% 0.21/0.59  fof(f43,plain,(
% 0.21/0.59    v3_ordinal1(sK0)),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f96,plain,(
% 0.21/0.59    ~spl3_3 | ~spl3_4 | spl3_5 | ~spl3_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f86,f78,f94,f91,f88])).
% 0.21/0.59  fof(f86,plain,(
% 0.21/0.59    r1_tarski(k1_ordinal1(sK0),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK0)) | ~spl3_2),
% 0.21/0.59    inference(resolution,[],[f82,f53])).
% 0.21/0.59  fof(f53,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f33])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.59    inference(nnf_transformation,[],[f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.59    inference(flattening,[],[f22])).
% 0.21/0.59  fof(f22,plain,(
% 0.21/0.59    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,axiom,(
% 0.21/0.59    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.59  fof(f82,plain,(
% 0.21/0.59    r1_ordinal1(k1_ordinal1(sK0),sK1) | ~spl3_2),
% 0.21/0.59    inference(avatar_component_clause,[],[f78])).
% 0.21/0.59  fof(f83,plain,(
% 0.21/0.59    spl3_1 | spl3_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f45,f78,f75])).
% 0.21/0.59  fof(f45,plain,(
% 0.21/0.59    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  fof(f80,plain,(
% 0.21/0.59    ~spl3_1 | ~spl3_2),
% 0.21/0.59    inference(avatar_split_clause,[],[f46,f78,f75])).
% 0.21/0.59  fof(f46,plain,(
% 0.21/0.59    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f32])).
% 0.21/0.59  % SZS output end Proof for theBenchmark
% 0.21/0.59  % (13231)------------------------------
% 0.21/0.59  % (13231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (13231)Termination reason: Refutation
% 0.21/0.59  
% 0.21/0.59  % (13231)Memory used [KB]: 10746
% 0.21/0.59  % (13231)Time elapsed: 0.142 s
% 0.21/0.59  % (13231)------------------------------
% 0.21/0.59  % (13231)------------------------------
% 0.21/0.59  % (13228)Success in time 0.223 s
%------------------------------------------------------------------------------
