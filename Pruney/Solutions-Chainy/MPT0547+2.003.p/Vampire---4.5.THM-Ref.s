%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 (  99 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 258 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f50,f54,f58,f62,f74,f80,f97,f102,f110,f113])).

fof(f113,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f45,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_2
  <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(resolution,[],[f109,f53])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f109,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_15
  <=> v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f110,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f103,f100,f56,f107])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( spl3_14
  <=> ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f103,plain,
    ( v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f101,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f101,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f98,f95,f38,f100])).

fof(f38,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f95,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f98,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f96,f40])).

fof(f40,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f97,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f82,f78,f60,f95])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK2(X0,X1,X2),X1)
        | ~ r2_hidden(X0,k9_relat_1(X2,X1))
        | ~ v1_relat_1(X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f79,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f80,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f76,f72,f48,f78])).

fof(f48,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f76,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( ! [X0] :
        ( k1_enumset1(X0,X0,X0) != k1_enumset1(X0,X0,X0)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f73,f49])).

fof(f49,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f72])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f29,f26,f26])).

fof(f26,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f56])).

% (17717)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f46,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
        & v1_relat_1(X0) )
   => ( k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f41,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (17711)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (17712)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % (17723)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.45  % (17715)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (17710)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (17715)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f114,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f41,f46,f50,f54,f58,f62,f74,f80,f97,f102,f110,f113])).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    spl3_2 | ~spl3_4 | ~spl3_15),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f112])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    $false | (spl3_2 | ~spl3_4 | ~spl3_15)),
% 0.19/0.46    inference(subsumption_resolution,[],[f111,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) | spl3_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    spl3_2 <=> k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) | (~spl3_4 | ~spl3_15)),
% 0.19/0.46    inference(resolution,[],[f109,f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f52])).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    spl3_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) | ~spl3_15),
% 0.19/0.46    inference(avatar_component_clause,[],[f107])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    spl3_15 <=> v1_xboole_0(k9_relat_1(sK0,k1_xboole_0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    spl3_15 | ~spl3_5 | ~spl3_14),
% 0.19/0.46    inference(avatar_split_clause,[],[f103,f100,f56,f107])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    spl3_5 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    spl3_14 <=> ! [X0] : ~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    v1_xboole_0(k9_relat_1(sK0,k1_xboole_0)) | (~spl3_5 | ~spl3_14)),
% 0.19/0.46    inference(resolution,[],[f101,f57])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_5),
% 0.19/0.46    inference(avatar_component_clause,[],[f56])).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) ) | ~spl3_14),
% 0.19/0.46    inference(avatar_component_clause,[],[f100])).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    spl3_14 | ~spl3_1 | ~spl3_13),
% 0.19/0.46    inference(avatar_split_clause,[],[f98,f95,f38,f100])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    spl3_1 <=> v1_relat_1(sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.46  fof(f95,plain,(
% 0.19/0.46    spl3_13 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.46  fof(f98,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK0,k1_xboole_0))) ) | (~spl3_1 | ~spl3_13)),
% 0.19/0.46    inference(resolution,[],[f96,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    v1_relat_1(sK0) | ~spl3_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f38])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k9_relat_1(X1,k1_xboole_0))) ) | ~spl3_13),
% 0.19/0.46    inference(avatar_component_clause,[],[f95])).
% 0.19/0.46  fof(f97,plain,(
% 0.19/0.46    spl3_13 | ~spl3_6 | ~spl3_10),
% 0.19/0.46    inference(avatar_split_clause,[],[f82,f78,f60,f95])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    spl3_6 <=> ! [X1,X0,X2] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.46  fof(f78,plain,(
% 0.19/0.46    spl3_10 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1)) ) | (~spl3_6 | ~spl3_10)),
% 0.19/0.46    inference(resolution,[],[f79,f61])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) ) | ~spl3_6),
% 0.19/0.46    inference(avatar_component_clause,[],[f60])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_10),
% 0.19/0.46    inference(avatar_component_clause,[],[f78])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    spl3_10 | ~spl3_3 | ~spl3_9),
% 0.19/0.46    inference(avatar_split_clause,[],[f76,f72,f48,f78])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    spl3_9 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_3 | ~spl3_9)),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f75])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k1_enumset1(X0,X0,X0) | ~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_3 | ~spl3_9)),
% 0.19/0.46    inference(superposition,[],[f73,f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.19/0.46    inference(avatar_component_clause,[],[f48])).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_9),
% 0.19/0.46    inference(avatar_component_clause,[],[f72])).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    spl3_9),
% 0.19/0.46    inference(avatar_split_clause,[],[f36,f72])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 0.19/0.46    inference(definition_unfolding,[],[f29,f26,f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.19/0.46    inference(nnf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    spl3_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f33,f60])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(rectify,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(nnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    spl3_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f28,f56])).
% 0.19/0.46  % (17717)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.19/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    spl3_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f27,f52])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    spl3_3),
% 0.19/0.46    inference(avatar_split_clause,[],[f25,f48])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    ~spl3_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f24,f43])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0)) => (k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) & v1_relat_1(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,negated_conjecture,(
% 0.19/0.46    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.46    inference(negated_conjecture,[],[f7])).
% 0.19/0.46  fof(f7,conjecture,(
% 0.19/0.46    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    spl3_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f23,f38])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    v1_relat_1(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (17715)------------------------------
% 0.19/0.46  % (17715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (17715)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (17715)Memory used [KB]: 6140
% 0.19/0.46  % (17715)Time elapsed: 0.058 s
% 0.19/0.46  % (17715)------------------------------
% 0.19/0.46  % (17715)------------------------------
% 0.19/0.46  % (17707)Success in time 0.109 s
%------------------------------------------------------------------------------
