%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  219 ( 332 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f59,f63,f67,f71,f81,f87,f104,f118,f125])).

fof(f125,plain,
    ( spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f123,f80])).

fof(f80,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_11
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f123,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f120,f46])).

fof(f46,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f120,plain,
    ( v1_xboole_0(sK1)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(resolution,[],[f117,f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK1,X0)
        | ~ r1_xboole_0(sK0,X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | r1_xboole_0(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_17
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f118,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f114,f102,f57,f49,f116])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f102,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK2(X0),X1)
        | ~ r2_hidden(sK2(X0),k2_xboole_0(X1,X0))
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f50,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0),X0)
        | ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0),X0)
        | ~ r2_hidden(sK2(X0),X0)
        | ~ r1_xboole_0(X0,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(superposition,[],[f103,f58])).

fof(f58,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0),k2_xboole_0(X1,X0))
        | ~ r2_hidden(sK2(X0),X1)
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f69,f49,f102])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0),X1)
        | ~ r2_hidden(sK2(X0),k2_xboole_0(X1,X0))
        | ~ r1_xboole_0(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f87,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f83,f65,f39,f85])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK0,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f66,f41])).

fof(f41,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f81,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f61,f34,f78])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f62,f36])).

fof(f36,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f57])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK1,sK0)
    & r1_tarski(sK1,sK0)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( r1_xboole_0(X1,X0)
        & r1_tarski(X1,X0)
        & ~ v1_xboole_0(X1) )
   => ( r1_xboole_0(sK1,sK0)
      & r1_tarski(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X1,X0)
      & r1_tarski(X1,X0)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ~ ( r1_xboole_0(X1,X0)
            & r1_tarski(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f23,f34])).

fof(f23,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.42  % (12407)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.42  % (12401)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (12405)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (12406)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (12405)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f59,f63,f67,f71,f81,f87,f104,f118,f125])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    spl3_3 | ~spl3_11 | ~spl3_12 | ~spl3_17),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f124])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    $false | (spl3_3 | ~spl3_11 | ~spl3_12 | ~spl3_17)),
% 0.20/0.42    inference(subsumption_resolution,[],[f123,f80])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f78])).
% 0.20/0.42  fof(f78,plain,(
% 0.20/0.42    spl3_11 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f123,plain,(
% 0.20/0.42    ~r1_xboole_0(sK0,sK1) | (spl3_3 | ~spl3_12 | ~spl3_17)),
% 0.20/0.42    inference(subsumption_resolution,[],[f120,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    ~v1_xboole_0(sK1) | spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl3_3 <=> v1_xboole_0(sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f120,plain,(
% 0.20/0.42    v1_xboole_0(sK1) | ~r1_xboole_0(sK0,sK1) | (~spl3_12 | ~spl3_17)),
% 0.20/0.42    inference(resolution,[],[f117,f86])).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    ( ! [X0] : (r1_xboole_0(sK1,X0) | ~r1_xboole_0(sK0,X0)) ) | ~spl3_12),
% 0.20/0.42    inference(avatar_component_clause,[],[f85])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    spl3_12 <=> ! [X0] : (~r1_xboole_0(sK0,X0) | r1_xboole_0(sK1,X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.42  fof(f117,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | ~spl3_17),
% 0.20/0.42    inference(avatar_component_clause,[],[f116])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    spl3_17 <=> ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    spl3_17 | ~spl3_4 | ~spl3_6 | ~spl3_15),
% 0.20/0.42    inference(avatar_split_clause,[],[f114,f102,f57,f49,f116])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_4 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_6 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl3_15 <=> ! [X1,X0] : (~r2_hidden(sK2(X0),X1) | ~r2_hidden(sK2(X0),k2_xboole_0(X1,X0)) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | (~spl3_4 | ~spl3_6 | ~spl3_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f113,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f113,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(sK2(X0),X0) | ~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | (~spl3_6 | ~spl3_15)),
% 0.20/0.42    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    ( ! [X0] : (~r2_hidden(sK2(X0),X0) | ~r2_hidden(sK2(X0),X0) | ~r1_xboole_0(X0,X0) | v1_xboole_0(X0)) ) | (~spl3_6 | ~spl3_15)),
% 0.20/0.42    inference(superposition,[],[f103,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f103,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK2(X0),k2_xboole_0(X1,X0)) | ~r2_hidden(sK2(X0),X1) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X0)) ) | ~spl3_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f102])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    spl3_15 | ~spl3_4 | ~spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f100,f69,f49,f102])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    spl3_9 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r2_hidden(sK2(X0),X1) | ~r2_hidden(sK2(X0),k2_xboole_0(X1,X0)) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X0)) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.42    inference(resolution,[],[f70,f50])).
% 0.20/0.42  fof(f70,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f69])).
% 0.20/0.42  fof(f87,plain,(
% 0.20/0.42    spl3_12 | ~spl3_2 | ~spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f83,f65,f39,f85])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl3_2 <=> r1_tarski(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_xboole_0(sK0,X0) | r1_xboole_0(sK1,X0)) ) | (~spl3_2 | ~spl3_8)),
% 0.20/0.42    inference(resolution,[],[f66,f41])).
% 0.20/0.42  fof(f41,plain,(
% 0.20/0.42    r1_tarski(sK1,sK0) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f39])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    spl3_11 | ~spl3_1 | ~spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f76,f61,f34,f78])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl3_1 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl3_7 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_7)),
% 0.20/0.42    inference(resolution,[],[f62,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    r1_xboole_0(sK1,sK0) | ~spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f71,plain,(
% 0.20/0.42    spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f32,f69])).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    spl3_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl3_7),
% 0.20/0.42    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.42  fof(f59,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f26,f57])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.42    inference(rectify,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f49])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(rectify,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ~spl3_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ~v1_xboole_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1)) => (r1_xboole_0(sK1,sK0) & r1_tarski(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0,X1] : (r1_xboole_0(X1,X0) & r1_tarski(X1,X0) & ~v1_xboole_0(X1))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0,X1] : ((r1_xboole_0(X1,X0) & r1_tarski(X1,X0)) & ~v1_xboole_0(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f6])).
% 0.21/0.42  fof(f6,conjecture,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f39])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f34])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    r1_xboole_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (12405)------------------------------
% 0.21/0.42  % (12405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (12405)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (12405)Memory used [KB]: 10618
% 0.21/0.42  % (12405)Time elapsed: 0.006 s
% 0.21/0.42  % (12405)------------------------------
% 0.21/0.42  % (12405)------------------------------
% 0.21/0.43  % (12399)Success in time 0.076 s
%------------------------------------------------------------------------------
