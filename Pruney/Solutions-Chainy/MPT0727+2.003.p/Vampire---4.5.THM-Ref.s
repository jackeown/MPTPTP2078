%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :  144 ( 212 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f46,f50,f68,f79,f84,f90,f94])).

fof(f94,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f91,f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X1,X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f91,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(resolution,[],[f89,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f89,plain,
    ( r1_tarski(k1_tarski(sK0),sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_14
  <=> r1_tarski(k1_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f90,plain,
    ( spl2_14
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f85,f82,f22,f87])).

fof(f22,plain,
    ( spl2_1
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f82,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f85,plain,
    ( r1_tarski(k1_tarski(sK0),sK0)
    | ~ spl2_1
    | ~ spl2_13 ),
    inference(resolution,[],[f83,f24])).

fof(f24,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK0),X0) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,
    ( spl2_13
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f80,f76,f48,f82])).

fof(f48,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f76,plain,
    ( spl2_12
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tarski(sK0),X0) )
    | ~ spl2_7
    | ~ spl2_12 ),
    inference(superposition,[],[f49,f78])).

fof(f78,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f79,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f74,f66,f27,f76])).

fof(f27,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(k1_tarski(X0),X1) = X1
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f74,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f67,f29])).

fof(f29,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k2_xboole_0(k1_tarski(X0),X1) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f40,f36,f66])).

fof(f36,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f40,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) = X1
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f37,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f50,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f46,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f42,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f34,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f30,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r1_tarski(sK1,sK0)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) )
   => ( r1_tarski(sK1,sK0)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( r1_tarski(X1,X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( r1_tarski(X1,X0)
          & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f15,f22])).

fof(f15,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.41  % (5799)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (5800)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (5804)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.42  % (5799)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f42,f46,f50,f68,f79,f84,f90,f94])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    ~spl2_3 | ~spl2_6 | ~spl2_14),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.42  fof(f93,plain,(
% 0.20/0.42    $false | (~spl2_3 | ~spl2_6 | ~spl2_14)),
% 0.20/0.42    inference(subsumption_resolution,[],[f91,f33])).
% 0.20/0.42  fof(f33,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) ) | ~spl2_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f32])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl2_3 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.42  fof(f91,plain,(
% 0.20/0.42    r2_hidden(sK0,sK0) | (~spl2_6 | ~spl2_14)),
% 0.20/0.42    inference(resolution,[],[f89,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl2_6 <=> ! [X1,X0] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    r1_tarski(k1_tarski(sK0),sK0) | ~spl2_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f87])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl2_14 <=> r1_tarski(k1_tarski(sK0),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    spl2_14 | ~spl2_1 | ~spl2_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f85,f82,f22,f87])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    spl2_1 <=> r1_tarski(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl2_13 <=> ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK0),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    r1_tarski(k1_tarski(sK0),sK0) | (~spl2_1 | ~spl2_13)),
% 0.20/0.42    inference(resolution,[],[f83,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0) | ~spl2_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f22])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK0),X0)) ) | ~spl2_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f82])).
% 0.20/0.42  fof(f84,plain,(
% 0.20/0.42    spl2_13 | ~spl2_7 | ~spl2_12),
% 0.20/0.42    inference(avatar_split_clause,[],[f80,f76,f48,f82])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    spl2_7 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    spl2_12 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tarski(sK0),X0)) ) | (~spl2_7 | ~spl2_12)),
% 0.20/0.42    inference(superposition,[],[f49,f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f76])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl2_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f48])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl2_12 | ~spl2_2 | ~spl2_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f74,f66,f27,f76])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    spl2_10 <=> ! [X1,X0] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl2_2 | ~spl2_10)),
% 0.20/0.42    inference(resolution,[],[f67,f29])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f27])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) ) | ~spl2_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f66])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    spl2_10 | ~spl2_4 | ~spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f59,f40,f36,f66])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl2_4 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl2_5 <=> ! [X1,X0] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) ) | (~spl2_4 | ~spl2_5)),
% 0.20/0.42    inference(resolution,[],[f37,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl2_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f40])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl2_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f36])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    spl2_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f48])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    spl2_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f18,f44])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.42    inference(nnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl2_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f19,f40])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl2_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f36])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl2_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f32])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.42  fof(f30,plain,(
% 0.20/0.42    spl2_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f27])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0) & r2_hidden(sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1] : (r1_tarski(X1,X0) & r2_hidden(X0,X1)) => (r1_tarski(sK1,sK0) & r2_hidden(sK0,sK1))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1] : (r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f5])).
% 0.20/0.42  fof(f5,conjecture,(
% 0.20/0.42    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    spl2_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f22])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (5799)------------------------------
% 0.20/0.42  % (5799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (5799)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (5799)Memory used [KB]: 10618
% 0.20/0.42  % (5799)Time elapsed: 0.006 s
% 0.20/0.42  % (5799)------------------------------
% 0.20/0.42  % (5799)------------------------------
% 0.20/0.42  % (5792)Success in time 0.063 s
%------------------------------------------------------------------------------
