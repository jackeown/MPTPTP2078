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
% DateTime   : Thu Dec  3 12:32:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  58 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 ( 130 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f48,f58,f62])).

fof(f62,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f59,f24])).

fof(f24,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f57,f19])).

fof(f19,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl3_1
  <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( ! [X2,X3,X1] :
        ( r1_tarski(k3_xboole_0(X1,X2),X3)
        | ~ r1_tarski(X1,X3) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_9
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,X3)
        | r1_tarski(k3_xboole_0(X1,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f58,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f50,f46,f35,f56])).

fof(f35,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f46,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f50,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,X3)
        | r1_tarski(k3_xboole_0(X1,X2),X3) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f36,f47])).

fof(f47,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f36,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f35])).

fof(f48,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f39,f31,f27,f46])).

fof(f27,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f39,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f27])).

fof(f32,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f37,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f33,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f13,f27])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f25,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f20,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f12,f17])).

fof(f12,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:58:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (21393)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (21394)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (21395)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (21393)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f20,f25,f29,f33,f37,f48,f58,f62])).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    spl3_1 | ~spl3_2 | ~spl3_9),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f61])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    $false | (spl3_1 | ~spl3_2 | ~spl3_9)),
% 0.22/0.42    inference(subsumption_resolution,[],[f59,f24])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    ~r1_tarski(sK0,sK1) | (spl3_1 | ~spl3_9)),
% 0.22/0.42    inference(resolution,[],[f57,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    spl3_1 <=> r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    ( ! [X2,X3,X1] : (r1_tarski(k3_xboole_0(X1,X2),X3) | ~r1_tarski(X1,X3)) ) | ~spl3_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f56])).
% 0.22/0.42  fof(f56,plain,(
% 0.22/0.42    spl3_9 <=> ! [X1,X3,X2] : (~r1_tarski(X1,X3) | r1_tarski(k3_xboole_0(X1,X2),X3))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    spl3_9 | ~spl3_5 | ~spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f50,f46,f35,f56])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    spl3_5 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    spl3_7 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X2,X3,X1] : (~r1_tarski(X1,X3) | r1_tarski(k3_xboole_0(X1,X2),X3)) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.42    inference(superposition,[],[f36,f47])).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f46])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) ) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f35])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    spl3_7 | ~spl3_3 | ~spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f39,f31,f27,f46])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    spl3_3 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    spl3_4 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) ) | (~spl3_3 | ~spl3_4)),
% 0.22/0.42    inference(resolution,[],[f32,f28])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f27])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f31])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl3_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f27])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl3_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f11,f22])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ~spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f12,f17])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (21393)------------------------------
% 0.22/0.42  % (21393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (21393)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (21393)Memory used [KB]: 10490
% 0.22/0.42  % (21393)Time elapsed: 0.005 s
% 0.22/0.42  % (21393)------------------------------
% 0.22/0.42  % (21393)------------------------------
% 0.22/0.42  % (21390)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.43  % (21387)Success in time 0.064 s
%------------------------------------------------------------------------------
