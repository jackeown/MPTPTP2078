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
% DateTime   : Thu Dec  3 12:30:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 111 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 317 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f60,f64,f71,f93,f103,f115,f127,f147])).

fof(f147,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f130,f47])).

fof(f47,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f130,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_4
    | ~ spl3_20 ),
    inference(superposition,[],[f42,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_20
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f42,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f127,plain,
    ( spl3_20
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f121,f112,f68,f123])).

fof(f68,plain,
    ( spl3_10
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f112,plain,
    ( spl3_18
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f121,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(superposition,[],[f70,f114])).

fof(f114,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f70,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f115,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f109,f101,f25,f112])).

fof(f25,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | k1_xboole_0 = k3_xboole_0(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f109,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(resolution,[],[f102,f27])).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | k1_xboole_0 = k3_xboole_0(sK2,X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f103,plain,
    ( spl3_16
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f99,f91,f58,f101])).

fof(f58,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f91,plain,
    ( spl3_14
  <=> ! [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        | r1_xboole_0(sK2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | k1_xboole_0 = k3_xboole_0(sK2,X0) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(resolution,[],[f92,f59])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f92,plain,
    ( ! [X1] :
        ( r1_xboole_0(sK2,X1)
        | ~ r1_xboole_0(sK0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f85,f62,f35,f91])).

fof(f35,plain,
    ( spl3_3
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f85,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(sK0,X1)
        | r1_xboole_0(sK2,X1) )
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f63,f37])).

fof(f37,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f63,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f71,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f65,f50,f30,f68])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f50,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f65,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f50])).

fof(f64,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f62])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f60,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f52,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f43,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f40])).

fof(f15,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( r1_xboole_0(sK0,sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK2,sK0)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
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

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
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

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f25])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (10556)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (10559)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.42  % (10556)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f148,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f43,f48,f52,f60,f64,f71,f93,f103,f115,f127,f147])).
% 0.22/0.42  fof(f147,plain,(
% 0.22/0.42    spl3_4 | ~spl3_5 | ~spl3_20),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.42  fof(f146,plain,(
% 0.22/0.42    $false | (spl3_4 | ~spl3_5 | ~spl3_20)),
% 0.22/0.42    inference(subsumption_resolution,[],[f130,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f45])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    ~v1_xboole_0(k1_xboole_0) | (spl3_4 | ~spl3_20)),
% 0.22/0.42    inference(superposition,[],[f42,f125])).
% 0.22/0.42  fof(f125,plain,(
% 0.22/0.42    k1_xboole_0 = sK2 | ~spl3_20),
% 0.22/0.42    inference(avatar_component_clause,[],[f123])).
% 0.22/0.42  fof(f123,plain,(
% 0.22/0.42    spl3_20 <=> k1_xboole_0 = sK2),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ~v1_xboole_0(sK2) | spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    spl3_4 <=> v1_xboole_0(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f127,plain,(
% 0.22/0.42    spl3_20 | ~spl3_10 | ~spl3_18),
% 0.22/0.42    inference(avatar_split_clause,[],[f121,f112,f68,f123])).
% 0.22/0.42  fof(f68,plain,(
% 0.22/0.42    spl3_10 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.42  fof(f112,plain,(
% 0.22/0.42    spl3_18 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.42  fof(f121,plain,(
% 0.22/0.42    k1_xboole_0 = sK2 | (~spl3_10 | ~spl3_18)),
% 0.22/0.42    inference(superposition,[],[f70,f114])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_18),
% 0.22/0.42    inference(avatar_component_clause,[],[f112])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f68])).
% 0.22/0.42  fof(f115,plain,(
% 0.22/0.42    spl3_18 | ~spl3_1 | ~spl3_16),
% 0.22/0.42    inference(avatar_split_clause,[],[f109,f101,f25,f112])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    spl3_16 <=> ! [X0] : (~r1_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK2,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_16)),
% 0.22/0.42    inference(resolution,[],[f102,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK2,X0)) ) | ~spl3_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f101])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    spl3_16 | ~spl3_8 | ~spl3_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f99,f91,f58,f101])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    spl3_14 <=> ! [X1] : (~r1_xboole_0(sK0,X1) | r1_xboole_0(sK2,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.42  fof(f99,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK2,X0)) ) | (~spl3_8 | ~spl3_14)),
% 0.22/0.42    inference(resolution,[],[f92,f59])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f58])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    ( ! [X1] : (r1_xboole_0(sK2,X1) | ~r1_xboole_0(sK0,X1)) ) | ~spl3_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f91])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    spl3_14 | ~spl3_3 | ~spl3_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f85,f62,f35,f91])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_3 <=> r1_tarski(sK2,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    spl3_9 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.42  fof(f85,plain,(
% 0.22/0.42    ( ! [X1] : (~r1_xboole_0(sK0,X1) | r1_xboole_0(sK2,X1)) ) | (~spl3_3 | ~spl3_9)),
% 0.22/0.42    inference(resolution,[],[f63,f37])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    r1_tarski(sK2,sK0) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f62])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl3_10 | ~spl3_2 | ~spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f65,f50,f30,f68])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    spl3_6 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    sK2 = k3_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_6)),
% 0.22/0.42    inference(resolution,[],[f51,f32])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f50])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    spl3_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f62])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    spl3_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f58])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(nnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f50])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f45])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    v1_xboole_0(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    ~spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f40])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ~v1_xboole_0(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2)) => (r1_xboole_0(sK0,sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK2,sK0) & ~v1_xboole_0(sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 0.22/0.42    inference(flattening,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    spl3_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f16,f35])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    r1_tarski(sK2,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    r1_tarski(sK2,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f25])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    r1_xboole_0(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (10556)------------------------------
% 0.22/0.42  % (10556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (10556)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (10556)Memory used [KB]: 10618
% 0.22/0.42  % (10556)Time elapsed: 0.007 s
% 0.22/0.42  % (10556)------------------------------
% 0.22/0.42  % (10556)------------------------------
% 0.22/0.42  % (10550)Success in time 0.066 s
%------------------------------------------------------------------------------
