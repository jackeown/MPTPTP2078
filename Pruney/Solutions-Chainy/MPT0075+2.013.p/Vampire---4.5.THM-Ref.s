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
% DateTime   : Thu Dec  3 12:30:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 113 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  201 ( 340 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f63,f71,f75,f80,f88,f101,f119,f122])).

fof(f122,plain,
    ( ~ spl5_3
    | spl5_14
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl5_3
    | spl5_14
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f120,f100])).

fof(f100,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_14
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f120,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f118,f45])).

fof(f45,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl5_3
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | r1_xboole_0(X0,sK1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_17
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f119,plain,
    ( spl5_17
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f115,f73,f33,f117])).

fof(f33,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f73,plain,
    ( spl5_10
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f115,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f74,f35])).

fof(f35,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f101,plain,
    ( ~ spl5_14
    | spl5_4
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f96,f85,f78,f48,f98])).

fof(f48,plain,
    ( spl5_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f85,plain,
    ( spl5_12
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f96,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | spl5_4
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f94,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f94,plain,
    ( v1_xboole_0(sK2)
    | ~ r1_xboole_0(sK2,sK1)
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(superposition,[],[f79,f87])).

fof(f87,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f88,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f82,f69,f38,f85])).

fof(f38,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f69,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f82,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(resolution,[],[f70,f40])).

fof(f40,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f80,plain,
    ( spl5_11
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f76,f61,f53,f78])).

fof(f53,plain,
    ( spl5_5
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f61,plain,
    ( spl5_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) )
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f62,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f75,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f71,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f55,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f51,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X2,X0)
        & ~ v1_xboole_0(X2) )
   => ( r1_xboole_0(sK0,sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK2,sK0)
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f46,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f24,f38])).

fof(f24,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f25,f33])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:54:54 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.40  % (5339)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.40  % (5340)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.40  % (5339)Refutation found. Thanks to Tanya!
% 0.20/0.40  % SZS status Theorem for theBenchmark
% 0.20/0.40  % SZS output start Proof for theBenchmark
% 0.20/0.40  fof(f123,plain,(
% 0.20/0.40    $false),
% 0.20/0.40    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f55,f63,f71,f75,f80,f88,f101,f119,f122])).
% 0.20/0.40  fof(f122,plain,(
% 0.20/0.40    ~spl5_3 | spl5_14 | ~spl5_17),
% 0.20/0.40    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.40  fof(f121,plain,(
% 0.20/0.40    $false | (~spl5_3 | spl5_14 | ~spl5_17)),
% 0.20/0.40    inference(subsumption_resolution,[],[f120,f100])).
% 0.20/0.40  fof(f100,plain,(
% 0.20/0.40    ~r1_xboole_0(sK2,sK1) | spl5_14),
% 0.20/0.40    inference(avatar_component_clause,[],[f98])).
% 0.20/0.40  fof(f98,plain,(
% 0.20/0.40    spl5_14 <=> r1_xboole_0(sK2,sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.40  fof(f120,plain,(
% 0.20/0.40    r1_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_17)),
% 0.20/0.40    inference(resolution,[],[f118,f45])).
% 0.20/0.40  fof(f45,plain,(
% 0.20/0.40    r1_tarski(sK2,sK0) | ~spl5_3),
% 0.20/0.40    inference(avatar_component_clause,[],[f43])).
% 0.20/0.40  fof(f43,plain,(
% 0.20/0.40    spl5_3 <=> r1_tarski(sK2,sK0)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.40  fof(f118,plain,(
% 0.20/0.40    ( ! [X0] : (~r1_tarski(X0,sK0) | r1_xboole_0(X0,sK1)) ) | ~spl5_17),
% 0.20/0.40    inference(avatar_component_clause,[],[f117])).
% 0.20/0.40  fof(f117,plain,(
% 0.20/0.40    spl5_17 <=> ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.40  fof(f119,plain,(
% 0.20/0.40    spl5_17 | ~spl5_1 | ~spl5_10),
% 0.20/0.40    inference(avatar_split_clause,[],[f115,f73,f33,f117])).
% 0.20/0.40  fof(f33,plain,(
% 0.20/0.40    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.40  fof(f73,plain,(
% 0.20/0.40    spl5_10 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.40  fof(f115,plain,(
% 0.20/0.40    ( ! [X0] : (r1_xboole_0(X0,sK1) | ~r1_tarski(X0,sK0)) ) | (~spl5_1 | ~spl5_10)),
% 0.20/0.40    inference(resolution,[],[f74,f35])).
% 0.20/0.40  fof(f35,plain,(
% 0.20/0.40    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 0.20/0.40    inference(avatar_component_clause,[],[f33])).
% 0.20/0.40  fof(f74,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl5_10),
% 0.20/0.40    inference(avatar_component_clause,[],[f73])).
% 0.20/0.40  fof(f101,plain,(
% 0.20/0.40    ~spl5_14 | spl5_4 | ~spl5_11 | ~spl5_12),
% 0.20/0.40    inference(avatar_split_clause,[],[f96,f85,f78,f48,f98])).
% 0.20/0.40  fof(f48,plain,(
% 0.20/0.40    spl5_4 <=> v1_xboole_0(sK2)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.40  fof(f78,plain,(
% 0.20/0.40    spl5_11 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.40  fof(f85,plain,(
% 0.20/0.40    spl5_12 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.40  fof(f96,plain,(
% 0.20/0.40    ~r1_xboole_0(sK2,sK1) | (spl5_4 | ~spl5_11 | ~spl5_12)),
% 0.20/0.40    inference(subsumption_resolution,[],[f94,f50])).
% 0.20/0.40  fof(f50,plain,(
% 0.20/0.40    ~v1_xboole_0(sK2) | spl5_4),
% 0.20/0.40    inference(avatar_component_clause,[],[f48])).
% 0.20/0.40  fof(f94,plain,(
% 0.20/0.40    v1_xboole_0(sK2) | ~r1_xboole_0(sK2,sK1) | (~spl5_11 | ~spl5_12)),
% 0.20/0.40    inference(superposition,[],[f79,f87])).
% 0.20/0.40  fof(f87,plain,(
% 0.20/0.40    sK2 = k3_xboole_0(sK2,sK1) | ~spl5_12),
% 0.20/0.40    inference(avatar_component_clause,[],[f85])).
% 0.20/0.40  fof(f79,plain,(
% 0.20/0.40    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_11),
% 0.20/0.40    inference(avatar_component_clause,[],[f78])).
% 0.20/0.40  fof(f88,plain,(
% 0.20/0.40    spl5_12 | ~spl5_2 | ~spl5_9),
% 0.20/0.40    inference(avatar_split_clause,[],[f82,f69,f38,f85])).
% 0.20/0.40  fof(f38,plain,(
% 0.20/0.40    spl5_2 <=> r1_tarski(sK2,sK1)),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.40  fof(f69,plain,(
% 0.20/0.40    spl5_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.40  fof(f82,plain,(
% 0.20/0.40    sK2 = k3_xboole_0(sK2,sK1) | (~spl5_2 | ~spl5_9)),
% 0.20/0.40    inference(resolution,[],[f70,f40])).
% 0.20/0.40  fof(f40,plain,(
% 0.20/0.40    r1_tarski(sK2,sK1) | ~spl5_2),
% 0.20/0.40    inference(avatar_component_clause,[],[f38])).
% 0.20/0.40  fof(f70,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl5_9),
% 0.20/0.40    inference(avatar_component_clause,[],[f69])).
% 0.20/0.40  fof(f80,plain,(
% 0.20/0.40    spl5_11 | ~spl5_5 | ~spl5_7),
% 0.20/0.40    inference(avatar_split_clause,[],[f76,f61,f53,f78])).
% 0.20/0.40  fof(f53,plain,(
% 0.20/0.40    spl5_5 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.40  fof(f61,plain,(
% 0.20/0.40    spl5_7 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.40    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.40  fof(f76,plain,(
% 0.20/0.40    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) ) | (~spl5_5 | ~spl5_7)),
% 0.20/0.40    inference(resolution,[],[f62,f54])).
% 0.20/0.40  fof(f54,plain,(
% 0.20/0.40    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) ) | ~spl5_5),
% 0.20/0.40    inference(avatar_component_clause,[],[f53])).
% 0.20/0.40  fof(f62,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl5_7),
% 0.20/0.40    inference(avatar_component_clause,[],[f61])).
% 0.20/0.40  fof(f75,plain,(
% 0.20/0.40    spl5_10),
% 0.20/0.40    inference(avatar_split_clause,[],[f31,f73])).
% 0.20/0.40  fof(f31,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f13])).
% 0.20/0.40  fof(f13,plain,(
% 0.20/0.40    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.40    inference(flattening,[],[f12])).
% 0.20/0.40  fof(f12,plain,(
% 0.20/0.40    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.40    inference(ennf_transformation,[],[f4])).
% 0.20/0.40  fof(f4,axiom,(
% 0.20/0.40    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.40  fof(f71,plain,(
% 0.20/0.40    spl5_9),
% 0.20/0.40    inference(avatar_split_clause,[],[f30,f69])).
% 0.20/0.40  fof(f30,plain,(
% 0.20/0.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f11])).
% 0.20/0.40  fof(f11,plain,(
% 0.20/0.40    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.40    inference(ennf_transformation,[],[f3])).
% 0.20/0.40  fof(f3,axiom,(
% 0.20/0.40    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.40  fof(f63,plain,(
% 0.20/0.40    spl5_7),
% 0.20/0.40    inference(avatar_split_clause,[],[f29,f61])).
% 0.20/0.40  fof(f29,plain,(
% 0.20/0.40    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.40    inference(cnf_transformation,[],[f21])).
% 0.20/0.40  fof(f21,plain,(
% 0.20/0.40    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f20])).
% 0.20/0.40  fof(f20,plain,(
% 0.20/0.40    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.40  fof(f10,plain,(
% 0.20/0.40    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.40    inference(ennf_transformation,[],[f7])).
% 0.20/0.40  fof(f7,plain,(
% 0.20/0.40    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.40    inference(rectify,[],[f2])).
% 0.20/0.40  fof(f2,axiom,(
% 0.20/0.40    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.40  fof(f55,plain,(
% 0.20/0.40    spl5_5),
% 0.20/0.40    inference(avatar_split_clause,[],[f27,f53])).
% 0.20/0.40  fof(f27,plain,(
% 0.20/0.40    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.40    inference(cnf_transformation,[],[f19])).
% 0.20/0.40  fof(f19,plain,(
% 0.20/0.40    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.40  fof(f18,plain,(
% 0.20/0.40    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.40    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.41    inference(rectify,[],[f16])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.41    inference(nnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    ~spl5_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f22,f48])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ~v1_xboole_0(sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.20/0.41    inference(flattening,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.20/0.41  fof(f46,plain,(
% 0.20/0.41    spl5_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f23,f43])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    r1_tarski(sK2,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    spl5_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f24,f38])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    r1_tarski(sK2,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    spl5_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f25,f33])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    r1_xboole_0(sK0,sK1)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (5339)------------------------------
% 0.20/0.41  % (5339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (5339)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (5339)Memory used [KB]: 10618
% 0.20/0.41  % (5339)Time elapsed: 0.007 s
% 0.20/0.41  % (5339)------------------------------
% 0.20/0.41  % (5339)------------------------------
% 0.20/0.41  % (5332)Success in time 0.064 s
%------------------------------------------------------------------------------
